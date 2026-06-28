//! Port of `Term.Substitution.SubstVFresh` from
//! `lib/term/src/Term/Substitution/SubstVFresh.hs`.
//!
//! Substitutions whose range variables are considered fresh — such
//! substitutions cannot be applied directly; the caller must first convert
//! them to a regular `Subst` by re-naming away from existing free vars.

use std::collections::BTreeMap;

use crate::lterm::{LVar, Name};
use crate::vterm::{Lit, VTerm};
use crate::term::Term;

// `PartialOrd` / `Ord` derived to mirror Haskell's `deriving (Ord, ..)` on
// `SubstVFresh c v` (SubstVFresh.hs:79-80).  Haskell's `S.toList` in `performSplit`
// returns substitutions in sorted order; we need the same canonical
// ordering so split-case enumeration matches Haskell (e.g. KAS2_eCK
// Resp_1 variant `c1 = aenc(x, pk(~lkR))` comes before the trivial
// one, giving `split_case_1` = the meaningful variant).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct SubstVFresh<C, V> {
    map: BTreeMap<V, VTerm<C, V>>,
}

impl<C, V> Default for SubstVFresh<C, V> {
    fn default() -> Self { SubstVFresh { map: BTreeMap::new() } }
}

pub type LSubstVFresh<C> = SubstVFresh<C, LVar>;
pub type LNSubstVFresh = SubstVFresh<Name, LVar>;

impl<C, V> SubstVFresh<C, V>
where
    C: Ord + Clone,
    V: Ord + Clone,
{
    pub fn empty() -> Self { SubstVFresh::default() }

    /// `substFromListVFresh`: build directly from a mapping list (no
    /// trivial-mapping filtering, unlike free-variable `Subst`).
    pub fn from_list(pairs: impl IntoIterator<Item = (V, VTerm<C, V>)>) -> Self {
        SubstVFresh { map: pairs.into_iter().collect() }
    }

    /// `restrictVFresh`: drop entries whose key is not in `vars`.
    pub fn restrict(&self, vars: &[V]) -> Self
    where
        V: PartialEq,
    {
        let map = self
            .map
            .iter()
            .filter(|(v, _)| vars.contains(v))
            .map(|(v, t)| (v.clone(), t.clone()))
            .collect();
        SubstVFresh { map }
    }

    /// `mapRangeVFresh`: rewrite the range elements; result variables are
    /// considered fresh.
    ///
    /// Intentionally retained for parity with HS `mapRangeVFresh`; no current
    /// Rust caller (the live `Subst::map_range` is the distinct free-subst
    /// variant).
    pub fn map_range<F: FnMut(VTerm<C, V>) -> VTerm<C, V>>(&self, mut f: F) -> Self {
        let map = self.map.iter().map(|(v, t)| (v.clone(), f(t.clone()))).collect();
        SubstVFresh { map }
    }

    pub fn dom(&self) -> impl Iterator<Item = &V> { self.map.keys() }
    pub fn range(&self) -> impl Iterator<Item = &VTerm<C, V>> { self.map.values() }
    pub fn image_of(&self, v: &V) -> Option<&VTerm<C, V>> { self.map.get(v) }
    pub fn to_list(&self) -> Vec<(V, VTerm<C, V>)> {
        self.map.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
    /// Borrowing view over the (key, image) pairs in domain order, avoiding
    /// the per-entry clones of `to_list` when callers only need to read.
    pub fn iter(&self) -> impl Iterator<Item = (&V, &VTerm<C, V>)> {
        self.map.iter()
    }
    pub fn is_empty(&self) -> bool { self.map.is_empty() }
    pub fn len(&self) -> usize { self.map.len() }
}

/// Rename every variable in `t` to a canonical fresh variable (empty name
/// hint, sort preserved), assigning indices 0,1,2,… in order of FIRST
/// appearance, threading `bindings`/`counter` so repeated occurrences (and
/// later range terms in the same substitution) reuse earlier assignments.
/// Left-to-right depth-first traversal mirrors HS `mapFrees`/`HasFrees`.
fn rename_term_drop_hint<C: Ord + Clone>(
    t: &VTerm<C, LVar>,
    bindings: &mut BTreeMap<LVar, LVar>,
    counter: &mut u64,
) -> VTerm<C, LVar> {
    match t {
        Term::Lit(Lit::Con(c)) => Term::Lit(Lit::Con(c.clone())),
        Term::Lit(Lit::Var(v)) => {
            let nv = match bindings.get(v) {
                Some(nv) => nv.clone(),
                None => {
                    let nv = LVar { name: "".into(), sort: v.sort, idx: *counter };
                    *counter += 1;
                    bindings.insert(v.clone(), nv.clone());
                    nv
                }
            };
            Term::Lit(Lit::Var(nv))
        }
        Term::App(sym, args) => {
            let new_args: Vec<VTerm<C, LVar>> = args
                .iter()
                .map(|a| rename_term_drop_hint(a, bindings, counter))
                .collect();
            // Route through the AC/C-sorting smart constructor, matching
            // HS `mapFrees f@(Arbitrary _) (FApp o l) = fApp o <$> ...`
            // (LTerm.hs:733-734).  Renaming assigns fresh idxs by first
            // appearance, so an AC/C arg list sorted under the OLD vars
            // can become unsorted under the new ones; `fApp` re-sorts.
            crate::term::f_app(sym.clone(), new_args)
        }
    }
}

impl<C: Ord + Clone> LSubstVFresh<C> {
    /// `dropNameHintsLNSubstVFresh` (EquationStore.hs:143-147): the canonical
    /// form used as the split-case sort key. Renames every RANGE variable to a
    /// fresh variable with an EMPTY name hint, sort preserved, indices assigned
    /// 0,1,2,… in order of first appearance across the range terms (visited in
    /// domain-key order) — mirrors HS `renameDropNamehint` applied to
    /// `map snd (substToListVFresh s)`. Domain keys are kept unchanged. Two
    /// substitutions that are α-equivalent in their range map to the same
    /// canonical form, so a stable `sort_by_cached_key(drop_name_hints)`
    /// (= HS `sortOnMemo dropNameHintsLNSubstVFresh`) orders the split cases
    /// structurally, independent of the fresh-allocation counter.
    pub fn drop_name_hints(&self) -> Self {
        let mut bindings: BTreeMap<LVar, LVar> = BTreeMap::new();
        let mut counter: u64 = 0;
        let renamed: Vec<(LVar, VTerm<C, LVar>)> = self
            .map
            .iter()
            .map(|(k, t)| (k.clone(), rename_term_drop_hint(t, &mut bindings, &mut counter)))
            .collect();
        Self::from_list(renamed)
    }

    /// `varsRangeVFresh`: every variable that appears in any range term.
    pub fn vars_range(&self) -> Vec<LVar> {
        // Collect vars from every range term by reference (no clone of the
        // terms, no intermediate `f_app_list` bundle), then sort+dedup to
        // mirror `vars_vterm`'s set semantics.
        let mut out: Vec<LVar> = Vec::new();
        for t in self.range() {
            out.extend(crate::vterm::vars_vterm_in_order(t));
        }
        out.sort();
        out.dedup();
        out
    }

    /// `isRenamedVar`: the binding for `v` is just a sort-preserving
    /// rename, and the target variable doesn't appear elsewhere.
    pub fn is_renamed_var(&self, v: &LVar) -> bool {
        let Some(t) = self.image_of(v) else { return false; };
        let Term::Lit(Lit::Var(target)) = t else { return false; };
        if target.sort != v.sort { return false; }
        // target must not appear in any other range entry.  Borrow each
        // range term and scan in place (short-circuiting), avoiding the
        // per-key clone of every other range term + `f_app_list` bundle.
        self.map
            .iter()
            .filter(|(w, _)| *w != v)
            .all(|(_, t)| !crate::vterm::occurs_vterm(target, t))
    }

    /// `isRenaming`: every entry is a rename.
    ///
    /// Equivalent to `self.map.keys().all(|v| self.is_renamed_var(v))` but
    /// computed in a single pass (the naive form is O(n^2): each
    /// `is_renamed_var` re-scans every other range entry).  A substitution is
    /// a renaming iff every binding maps to a sort-preserving variable and no
    /// two distinct keys map to the same target variable (i.e. no target var
    /// occurs in any other entry).
    pub fn is_renaming(&self) -> bool {
        let mut targets: std::collections::BTreeSet<&LVar> = std::collections::BTreeSet::new();
        for (v, t) in self.map.iter() {
            let Term::Lit(Lit::Var(target)) = t else { return false; };
            if target.sort != v.sort { return false; }
            // A duplicate target means this target var also appears in another
            // entry, so that entry's `is_renamed_var` would have failed.
            if !targets.insert(target) { return false; }
        }
        true
    }

    /// `removeRenamings`: drop every entry that's just a rename.
    pub fn remove_renamings(&self) -> Self {
        let map = self
            .map
            .iter()
            .filter(|(v, _)| !self.is_renamed_var(v))
            .map(|(v, t)| (v.clone(), t.clone()))
            .collect();
        SubstVFresh { map }
    }

    /// `extendWithRenaming vs s`: extends `s` with renamings (with fresh
    /// variables) for the variables in `vs` that are not already in
    /// `dom s`.  Mirrors HS `Term.Substitution.SubstVFresh.extendWithRenaming`
    /// (SubstVFresh.hs:115-121).
    ///
    /// The new renamings use uniformly-shifted fresh idxs starting above
    /// `varsRangeVFresh self` (HS: `renameFreshAvoiding s2 (varsRangeVFresh s)`).
    /// The shift = freshStart - min(idx of vs_new); applied to each var in
    /// vs_new uniformly, preserving relative ordering — mirrors HS's
    /// `rename` semantics (LTerm.hs:607-614).
    pub fn extend_with_renaming(&self, vs: &[LVar]) -> Self {
        use std::collections::BTreeSet;
        let dom: BTreeSet<LVar> = self.dom().cloned().collect();
        let mut vs_new: Vec<LVar> = Vec::new();
        let mut seen: BTreeSet<LVar> = BTreeSet::new();
        for v in vs {
            if dom.contains(v) { continue; }
            if seen.insert(v.clone()) {
                vs_new.push(v.clone());
            }
        }
        if vs_new.is_empty() {
            return self.clone();
        }
        // Fresh state: `evalFreshAvoiding (varsRangeVFresh s)` =
        //   succ . maxIdx . vars (or 0 if empty).
        let avoid = self.vars_range();
        let fresh_start: u64 = avoid.iter().map(|v| v.idx).max()
            .map(|m| m + 1).unwrap_or(0);
        // HS's `rename`: minVar, maxVar; freshStart from monad; shift =
        // freshStart - minVar; new idx = old idx + shift (signed).
        let vs_min: u64 = vs_new.iter().map(|v| v.idx).min().unwrap();
        // Signed math because shift may go negative when fresh_start < vs_min
        // (e.g., self is empty so fresh_start=0 but vs_min > 0).  This is
        // a faithful translation of HS's Integer math.
        let shift: i128 = fresh_start as i128 - vs_min as i128;
        let new_entries: Vec<(LVar, VTerm<C, LVar>)> = vs_new.iter()
            .map(|v| {
                let new_idx_signed: i128 = v.idx as i128 + shift;
                let new_idx: u64 = if new_idx_signed < 0 { 0 }
                    else if new_idx_signed > u64::MAX as i128 { u64::MAX }
                    else { new_idx_signed as u64 };
                let v_new = LVar {
                    name: v.name,
                    sort: v.sort,
                    idx: new_idx,
                };
                (v.clone(), Term::Lit(Lit::Var(v_new)))
            })
            .collect();
        let mut combined: Vec<(LVar, VTerm<C, LVar>)> = self.to_list();
        combined.extend(new_entries);
        Self::from_list(combined)
    }

    /// HS-faithful `freshToFreeAvoidingFast`:  rename all range vars
    /// uniformly via HS's `rename` shift (freshStart - minVar), where
    /// `freshStart` = `succ . maxIdx . avoid` and `minVar`/`maxVar` are
    /// across the bundled range terms.  Mirrors
    /// `Term.Substitution.freshToFreeAvoidingFast` (Substitution.hs:77-92).
    ///
    /// Differs from `fresh_to_free_avoiding` (preserve-set form): this one
    /// uses HS's UNIFORM SHIFT (preserving relative ordering of range-var
    /// idxs) rather than dense-packed sequential allocation.  Required for
    /// `compose_vfresh` to produce structurally-equivalent SubstVFresh
    /// shapes per variant.
    ///
    /// `fresh_start` is the precomputed `succ . maxIdx . frees(avoid)` the
    /// caller would otherwise build a set/list to derive: it is the ONLY thing
    /// the old `avoid: &[LVar]` argument was used for (its max idx + 1), so we
    /// take it directly and skip materialising the avoid collection.
    pub fn fresh_to_free_uniform_shift(&self, fresh_start: u64)
        -> crate::subst::Subst<C, LVar>
    {
        use std::collections::BTreeMap;
        use crate::subst::Subst;
        // Collect ALL distinct range vars in insertion order.
        let mut range_vars: Vec<LVar> = Vec::new();
        let mut seen: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        for t in self.range() {
            for w in crate::vterm::vars_vterm(t) {
                if seen.insert(w.clone()) {
                    range_vars.push(w);
                }
            }
        }
        if range_vars.is_empty() {
            // No range vars to rename — just downgrade.
            let pairs: Vec<(LVar, VTerm<C, LVar>)> = self.to_list();
            return Subst::from_list(pairs);
        }
        // HS: `evalFreshAvoiding t` initial counter = succ . maxIdx . frees t,
        // precomputed by the caller and handed in as `fresh_start`.
        let min_idx = range_vars.iter().map(|v| v.idx).min().unwrap();
        let shift: i128 = fresh_start as i128 - min_idx as i128;
        let mut rename: BTreeMap<LVar, LVar> = BTreeMap::new();
        for old in &range_vars {
            let new_idx_signed: i128 = old.idx as i128 + shift;
            let new_idx: u64 = if new_idx_signed < 0 { 0 }
                else if new_idx_signed > u64::MAX as i128 { u64::MAX }
                else { new_idx_signed as u64 };
            let new = LVar {
                name: old.name,
                sort: old.sort,
                idx: new_idx,
            };
            rename.insert(old.clone(), new);
        }
        let mut pairs: Vec<(LVar, VTerm<C, LVar>)> = Vec::new();
        for (v, t) in self.to_list() {
            let renamed = rename_lvars_in_vterm(&t, &rename);
            pairs.push((v, renamed));
        }
        Subst::from_list(pairs)
    }

    /// `freshToFree`: convert this VFresh substitution to a free `Subst`
    /// by renaming each range variable to a fresh LVar using indices
    /// obtained from `alloc_idxs` (a MonadFresh substitute — typically
    /// wrapping `MaudeHandle::reserve_idxs`).  Implements the
    /// `freshToFree`/`freshToFreeAvoiding` algorithm
    /// (Substitution.hs:54-72): sort by image size + per-binding name
    /// hints + `importBinding` caching.  (The uniform-shift
    /// `freshToFreeAvoidingFast` at Substitution.hs:77-81 is instead
    /// implemented by `fresh_to_free_uniform_shift`.)
    ///
    /// The reduction layer composes the result into the eq-store's
    /// free substitution so the picked variant's bindings propagate
    /// to rule terms during the next `substSystem` pass.
    pub fn fresh_to_free<F: FnMut(u64) -> u64>(
        &self,
        alloc_idxs: F,
    ) -> crate::subst::Subst<C, LVar> {
        // Default: no preserve set — every range var is treated as a
        // witness and gets renamed.  Suitable when the caller knows
        // there are no live system vars in the range.
        self.fresh_to_free_avoiding(alloc_idxs, &std::collections::BTreeSet::new())
    }

    /// `freshToFreeAvoiding`: convert VFresh → free subst.
    ///
    /// Mirrors Haskell `freshToFreeAvoiding s t = freshToFree s
    /// \`evalFreshAvoiding\` t` (Substitution.hs:71-72, built on
    /// `freshToFree` at 54-66): sorts entries by image size and applies
    /// the per-binding name-hint rule.  It renames every range var
    /// unconditionally (HS has no "preserve" concept — `evalFreshAvoiding`
    /// only seeds the fresh counter above `t`'s max idx, it never skips a
    /// variable).  The `preserve` argument is therefore IGNORED; it is kept
    /// only for signature stability with the callers that build a preserve
    /// set.
    pub fn fresh_to_free_avoiding<F: FnMut(u64) -> u64>(
        &self,
        mut alloc_idxs: F,
        _preserve: &std::collections::BTreeSet<LVar>,
    ) -> crate::subst::Subst<C, LVar> {
        use crate::subst::Subst;
        // HS has NO preserve concept in ANY freshToFree* variant:
        //   - `freshToFree` (Substitution.hs:54-66) imports EVERY range
        //     var to a brand-new fresh var via `importBinding`;
        //   - `freshToFreeAvoiding` (:69-71) is just
        //     `freshToFree s \`evalFreshAvoiding\` t` — `evalFreshAvoiding`
        //     only SEEDS the fresh counter above t's max idx, it never
        //     skips a variable;
        //   - `freshToFreeAvoidingFast` (:74-81) renames all range vars
        //     via `rename ... \`evalFreshAvoiding\` t` — same.
        // We therefore rename every range var unconditionally and ignore
        // `_preserve`.  HS maintains the invariant that VFresh ranges are
        // pure-fresh (composeVFresh's `extendWithRenaming`,
        // Substitution.hs:40-47), so keeping a range var's identity would
        // be unsound: it could fuse a Maude witness with an unrelated live
        // system var that happens to share (name, sort, idx).
        let preserve = std::collections::BTreeSet::new();
        let preserve = &preserve;
        // HS-faithful port (Substitution.hs:54-66):
        //
        //   freshToFree subst = (`evalBindT` noBindings) $ do
        //       let slist = sortOn (size . snd) $ substToListVFresh subst
        //       substFromList <$> mapM convertMapping slist
        //     where
        //       convertMapping (lv,t) = (lv,) <$> mapFrees (Arbitrary importVar) t
        //         where
        //           importVar v = importBinding (\s i -> LVar s (lvarSort v) i) v (namehint v)
        //           namehint v  = case viewTerm t of
        //               Lit (Var _) -> lvarName lv -- keep name of oldvar
        //               _           -> lvarName v
        //
        // Two key behaviours:
        // 1. Sort by image size (singletons first) — gives single-var
        //    images the chance to claim the fresh slot first.
        // 2. Name hint: for a singleton-Var image `(lv, ~x.K)`, name the
        //    fresh from the DOMAIN var's name (`lvarName lv`).  For an
        //    App image like `(lv, h(...))`, the inner vars keep their
        //    ORIGINAL names (`lvarName v`).
        //
        // `evalBindT noBindings` caches rename decisions per VFresh
        // range var: the first binding to claim a range var sets its
        // name+idx; subsequent uses reuse the cached fresh.  This is
        // what makes `~k → ~x.11` followed by `~k.1 → ~x.11` produce a
        // SHARED renamed var (both → ~k.<new>), folding the alpha-
        // equivalence into the free subst.

        // Step 0: sort entries by size of image (smaller first).
        // HS's `sortOn (size . snd)` — stable sort by size.
        let mut slist: Vec<(LVar, VTerm<C, LVar>)> = self.to_list();
        slist.sort_by_key(|(_, t)| term_size(t));

        // Step 1: cache binding map (range var → new var), built
        // incrementally as we walk substs in sorted order.
        let mut rename: BTreeMap<LVar, LVar> = BTreeMap::new();

        // Step 2: process each (lv, t) and rename inner vars per HS
        // semantics.  When t is a singleton Var, use lv's name as hint;
        // otherwise use the inner var's name.
        let mut pairs: Vec<(LVar, VTerm<C, LVar>)> = Vec::with_capacity(slist.len());
        for (lv, t) in slist.into_iter() {
            // Determine the namehint mode based on the OUTER term shape.
            let outer_is_singleton_var = matches!(&t, Term::Lit(Lit::Var(_)));
            let renamed = rename_lvars_with_hint(&t, &mut rename, preserve, &mut alloc_idxs,
                outer_is_singleton_var, &lv);
            pairs.push((lv, renamed));
        }
        Subst::from_list(pairs)
    }
}

/// Compute the "size" of a VTerm — number of leaves + interior App
/// nodes.  HS's `Term.size` for sorting `freshToFree`'s input list.
fn term_size<C, V>(t: &VTerm<C, V>) -> usize {
    match t {
        Term::Lit(_) => 1,
        Term::App(_, args) => 1 + args.iter().map(term_size).sum::<usize>(),
    }
}

/// Walk a VTerm, renaming each var via the rename map.  If a var
/// isn't yet in the rename map, allocate a fresh idx for it and
/// record the binding.  `outer_is_singleton_var` + `lv` together
/// implement HS's `namehint v = if (Lit (Var _) == t) then lvarName lv
/// else lvarName v` rule (Substitution.hs:64-66).
fn rename_lvars_with_hint<C: Ord + Clone, F: FnMut(u64) -> u64>(
    t: &VTerm<C, LVar>,
    rename: &mut BTreeMap<LVar, LVar>,
    preserve: &std::collections::BTreeSet<LVar>,
    alloc_idxs: &mut F,
    outer_is_singleton_var: bool,
    lv: &LVar,
) -> VTerm<C, LVar> {
    match t {
        Term::Lit(Lit::Var(v)) => {
            if preserve.contains(v) {
                Term::Lit(Lit::Var(v.clone()))
            } else if let Some(new) = rename.get(v).cloned() {
                Term::Lit(Lit::Var(new))
            } else {
                // Allocate a fresh idx; name hint depends on outer
                // term shape.
                let idx = alloc_idxs(1);
                let name = if outer_is_singleton_var {
                    lv.name
                } else {
                    v.name
                };
                let new = LVar { name, sort: v.sort, idx };
                rename.insert(v.clone(), new.clone());
                Term::Lit(Lit::Var(new))
            }
        }
        Term::Lit(Lit::Con(c)) => Term::Lit(Lit::Con(c.clone())),
        Term::App(f, args) => {
            let new_args: Vec<_> = args.iter()
                .map(|a| rename_lvars_with_hint(a, rename, preserve, alloc_idxs,
                    outer_is_singleton_var, lv))
                .collect();
            // Route through the smart constructor so AC/C argument lists
            // are re-sorted: freshToFree allocates a brand-new, non-
            // monotone idx per range var, so children that were sorted
            // under the old vars are no longer canonical under the new
            // ones.  HS does the same via `mapFrees (Arbitrary _)
            // (FApp o l) = fApp o <$> ...` (LTerm.hs).  (The sibling
            // `rename_lvars_in_vterm` stays raw — it mirrors HS's
            // Monotone `unsafefApp` path under a uniform, order-
            // preserving shift, where re-sorting is unnecessary.)
            crate::term::f_app(f.clone(), new_args)
        }
    }
}

/// `freeToFreshRaw`: re-tag a free `Subst`'s entries as a `SubstVFresh`.
/// Mirrors HS `Term.Substitution.freeToFreshRaw` (Substitution.hs:84-85):
/// considers all variables in the range as fresh.  No structural change —
/// just a type-level reinterpretation.
pub fn free_to_fresh_raw<C: Ord + Clone>(s: crate::subst::Subst<C, LVar>)
    -> LSubstVFresh<C>
{
    LSubstVFresh::from_list(s.to_list())
}

/// `composeVFresh s1 s2`: composes the fresh substitution `s1` with the
/// free substitution `s2`.  Mirrors HS `Term.Substitution.composeVFresh`
/// (Substitution.hs:41-47):
///
/// ```haskell
/// composeVFresh s1_0 s2 =
///     freeToFreshRaw (s1 `compose` s2)
///   where
///     s1 = freshToFreeAvoidingFast
///             (extendWithRenaming (varsRange s2) s1_0)
///             (s2, s1_0)
/// ```
///
/// Pipeline per variant:
/// 1. `extendWithRenaming (varsRange s2) s1_0` — add renaming entries
///    for s2's range vars not already in s1_0's domain.  Renamings get
///    uniform-shifted fresh idxs above `varsRangeVFresh s1_0`.
/// 2. `freshToFreeAvoidingFast _ (s2, s1_0)` — uniformly shift all range
///    vars above max idx in (s2, s1_0).  Convert to free `Subst`.
/// 3. `s1 \`compose\` s2` — Robinson compose.
/// 4. `freeToFreshRaw` — re-tag range as fresh.
///
/// This is what HS uses per-variant in `variantsProtoRule`
/// (RuleVariants.hs:74-77).  Without this pipeline, two variants whose
/// Maude-back-conversion shapes happen to collide will end up with
/// structurally-identical range vars and collapse at `perform_split`.
pub fn compose_vfresh<C>(
    s1_0: &LSubstVFresh<C>,
    s2: &crate::subst::Subst<C, LVar>,
) -> LSubstVFresh<C>
where
    C: Ord + Clone,
{
    // varsRange s2: vars in s2's range
    let mut vs_in_range_s2: Vec<LVar> = Vec::new();
    let mut seen: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    for t in s2.range() {
        for v in crate::vterm::vars_vterm(t) {
            if seen.insert(v.clone()) {
                vs_in_range_s2.push(v);
            }
        }
    }
    let extended = s1_0.extend_with_renaming(&vs_in_range_s2);
    // Avoid set for freshToFreeAvoidingFast: `evalFreshAvoiding (s2, s1_0)`
    // (Substitution.hs:47) = `frees (s2, s1_0)` = `frees s2 <> frees s1_0`.
    //
    // `frees s2` (s2 :: free LNSubst) walks BOTH domain and range.
    // `frees s1_0` (s1_0 :: LNSubstVFresh) uses `foldFrees (SubstVFresh n
    // LVar) = foldFrees f . M.keys` (SubstVFresh.hs:197) — i.e. ONLY the
    // DOMAIN KEYS, NOT the range (witnesses).  Including s1_0's range here
    // (as the old code did) over-counted the avoid set, so the re-based
    // witnesses came out inflated (Responder_secrecy: the Setup_Key `~k`
    // variant witnesses at ~k.30/42 vs HS's ~k.11/12/15, rotating the
    // 3-way split via `Ord LNSubstVFresh`).
    // `freshToFreeAvoidingFast` only consults the avoid set for its max idx
    // (`succ . maxIdx`), so fold that max directly over the same three sources
    // instead of materialising a BTreeSet + Vec.  Dedup/order are irrelevant
    // to a max, so the resulting `fresh_start` is byte-identical to the old
    // `avoid.iter().map(|v| v.idx).max().map(|m| m + 1).unwrap_or(0)`.
    let mut max_idx: Option<u64> = None;
    let mut bump = |idx: u64| { max_idx = Some(max_idx.map_or(idx, |m| m.max(idx))); };
    // s2's domain
    for v in s2.dom() { bump(v.idx); }
    // s2's range vars
    for t in s2.range() {
        for v in crate::vterm::vars_vterm(t) { bump(v.idx); }
    }
    // s1_0's domain keys ONLY (HS-faithful: frees of a SubstVFresh = keys).
    for v in s1_0.dom() { bump(v.idx); }
    let fresh_start: u64 = max_idx.map(|m| m + 1).unwrap_or(0);
    let s1 = extended.fresh_to_free_uniform_shift(fresh_start);
    let composed = s1.compose(s2);
    free_to_fresh_raw(composed)
}

/// Walk a VTerm, applying a LVar→LVar rename.
fn rename_lvars_in_vterm<C: Clone>(
    t: &VTerm<C, LVar>,
    rename: &BTreeMap<LVar, LVar>,
) -> VTerm<C, LVar> {
    match t {
        Term::Lit(Lit::Var(v)) => {
            let new = rename.get(v).cloned().unwrap_or_else(|| v.clone());
            Term::Lit(Lit::Var(new))
        }
        Term::Lit(other) => Term::Lit(other.clone()),
        Term::App(f, args) => Term::App(
            f.clone(),
            args.iter().map(|a| rename_lvars_in_vterm(a, rename)).collect(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::{LSort, LVar, Name};
    use crate::vterm::var_term;

    type C = Name;

    fn lv(name: &str, idx: u64) -> LVar { LVar::new(name, LSort::Msg, idx) }

    #[test]
    fn empty_substitution() {
        let s: LSubstVFresh<C> = SubstVFresh::empty();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn restrict_filters_keys() {
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 0))),
            (lv("x", 1), var_term(lv("z", 0))),
        ]);
        let r = s.restrict(&[lv("x", 0)]);
        assert_eq!(r.len(), 1);
    }

    #[test]
    fn renaming_detection() {
        // `x ~> y` — straightforward rename; should be detected as such
        // when no other entry mentions `y`.
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 0))),
        ]);
        assert!(s.is_renamed_var(&lv("x", 0)));
        assert!(s.is_renaming());

        // After adding a second entry that mentions `y`, `x ~> y` is no
        // longer a clean rename.
        let s2: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 0))),
            (lv("z", 0), var_term(lv("y", 0))),
        ]);
        assert!(!s2.is_renamed_var(&lv("x", 0)));
    }

    #[test]
    fn fresh_to_free_ignores_preserve_set() {
        use std::collections::BTreeSet;
        // HS has no "preserve" concept: every range var is renamed
        // unconditionally (Substitution.hs:54-72). Even when the range var
        // is passed in `preserve`, the result must NOT keep its identity.
        let s: LSubstVFresh<C> = SubstVFresh::from_list(vec![
            (lv("x", 0), var_term(lv("y", 5))),
        ]);
        let mut preserve: BTreeSet<LVar> = BTreeSet::new();
        preserve.insert(lv("y", 5));
        // Allocator hands out a fixed, clearly-distinct fresh idx.
        let free = s.fresh_to_free_avoiding(|_| 99, &preserve);
        let img = free.image_of(&lv("x", 0)).expect("x.0 must be mapped");
        match img {
            Term::Lit(Lit::Var(v)) => {
                // Renamed to the freshly-allocated idx, NOT the preserved y.5.
                assert_eq!(v.idx, 99);
                assert_ne!(*v, lv("y", 5));
            }
            other => panic!("expected a renamed var, got {other:?}"),
        }
    }
}
