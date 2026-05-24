//! Port of `Term.Substitution.SubstVFresh` from
//! `lib/term/src/Term/Substitution/SubstVFresh.hs`.
//!
//! Substitutions whose range variables are considered fresh — such
//! substitutions cannot be applied directly; the caller must first convert
//! them to a regular `Subst` by re-naming away from existing free vars.

use std::collections::BTreeMap;

use crate::lterm::{LVar, Name};
use crate::vterm::{Lit, VTerm};
use crate::term::{f_app_list, Term};

// `PartialOrd` / `Ord` derived to mirror Haskell's `deriving (Ord, ..)` on
// `SubstVFresh c v` (LTerm.hs).  Haskell's `S.toList` in `performSplit`
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
    pub fn is_empty(&self) -> bool { self.map.is_empty() }
    pub fn len(&self) -> usize { self.map.len() }
}

impl<C: Ord + Clone> LSubstVFresh<C> {
    /// `varsRangeVFresh`: every variable that appears in any range term.
    pub fn vars_range(&self) -> Vec<LVar> {
        let collected: Vec<VTerm<C, LVar>> = self.range().cloned().collect();
        let bundled: VTerm<C, LVar> = f_app_list(collected);
        crate::vterm::vars_vterm(&bundled)
    }

    /// `isRenamedVar`: the binding for `v` is just a sort-preserving
    /// rename, and the target variable doesn't appear elsewhere.
    pub fn is_renamed_var(&self, v: &LVar) -> bool {
        let Some(t) = self.image_of(v) else { return false; };
        let Term::Lit(Lit::Var(target)) = t else { return false; };
        if target.sort != v.sort { return false; }
        // target must not appear in any other range entry.
        let others: Vec<VTerm<C, LVar>> = self
            .map
            .iter()
            .filter(|(w, _)| *w != v)
            .map(|(_, t)| t.clone())
            .collect();
        let bundle: VTerm<C, LVar> = f_app_list(others);
        !crate::vterm::occurs_vterm(target, &bundle)
    }

    /// `isRenaming`: every entry is a rename.
    pub fn is_renaming(&self) -> bool {
        self.map.keys().all(|v| self.is_renamed_var(v))
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
                    name: v.name.clone(),
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
    pub fn fresh_to_free_uniform_shift(&self, avoid: &[LVar])
        -> crate::subst::Subst<C, LVar>
    {
        use std::collections::BTreeMap;
        use crate::subst::Subst;
        // Collect ALL distinct range vars in insertion order.
        let mut range_vars: Vec<LVar> = Vec::new();
        let mut seen: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        for (_v, t) in self.to_list() {
            for w in crate::vterm::vars_vterm(&t) {
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
        // HS: `evalFreshAvoiding t` initial counter = succ . maxIdx . frees t.
        let fresh_start: u64 = avoid.iter().map(|v| v.idx).max()
            .map(|m| m + 1).unwrap_or(0);
        let min_idx = range_vars.iter().map(|v| v.idx).min().unwrap();
        let shift: i128 = fresh_start as i128 - min_idx as i128;
        let mut rename: BTreeMap<LVar, LVar> = BTreeMap::new();
        for old in &range_vars {
            let new_idx_signed: i128 = old.idx as i128 + shift;
            let new_idx: u64 = if new_idx_signed < 0 { 0 }
                else if new_idx_signed > u64::MAX as i128 { u64::MAX }
                else { new_idx_signed as u64 };
            let new = LVar {
                name: old.name.clone(),
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

    /// `freshToFreeAvoidingFast`: convert this VFresh substitution to a
    /// free `Subst` by renaming each range variable to a fresh LVar
    /// using indices obtained from `alloc_idxs` (a MonadFresh substitute
    /// — typically wrapping `MaudeHandle::reserve_idxs`).  Mirrors
    /// `Term.Substitution.freshToFreeAvoidingFast` (Substitution.hs:77-92).
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

    /// `freshToFreeAvoidingFast`: convert VFresh → free subst, but
    /// PRESERVE any range var that's in `preserve` — those are live
    /// system vars (not fresh witnesses) and renaming them would
    /// break sharing with the rest of the system.
    ///
    /// Mirrors Haskell `freshToFreeAvoidingFast s t` which renames
    /// range vars via `rename ... \`evalFreshAvoiding\` t` — Haskell's
    /// `evalFreshAvoiding` avoids vars in `t`, so the renamer simply
    /// skips them.  Our equivalent: pass `varsRange(eq_store.subst)`
    /// (or similar) as `preserve`.
    pub fn fresh_to_free_avoiding<F: FnMut(u64) -> u64>(
        &self,
        mut alloc_idxs: F,
        preserve: &std::collections::BTreeSet<LVar>,
    ) -> crate::subst::Subst<C, LVar> {
        use crate::subst::Subst;
        // Step 1: collect distinct range vars that are NOT in `preserve`.
        // Those that are in `preserve` retain their identity (no rename).
        let mut range_vars: Vec<LVar> = Vec::new();
        for (_v, t) in self.to_list() {
            for w in crate::vterm::vars_vterm(&t) {
                if preserve.contains(&w) { continue; }
                if !range_vars.iter().any(|r| r == &w) {
                    range_vars.push(w);
                }
            }
        }
        // Step 2: allocate fresh indices and build a rename map.
        let need = range_vars.len() as u64;
        let mut rename: BTreeMap<LVar, LVar> = BTreeMap::new();
        if need > 0 {
            let base = alloc_idxs(need);
            for (k, old) in range_vars.into_iter().enumerate() {
                let new = LVar { name: old.name.clone(),
                                 sort: old.sort,
                                 idx: base + (k as u64) };
                rename.insert(old, new);
            }
        }
        // Step 3: rewrite each (v, t) by renaming non-preserved vars.
        let mut pairs: Vec<(LVar, VTerm<C, LVar>)> = Vec::new();
        for (v, t) in self.to_list() {
            let renamed = rename_lvars_in_vterm(&t, &rename);
            pairs.push((v, renamed));
        }
        Subst::from_list(pairs)
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
/// structurally-identical range vars and collapse at `perform_split`
/// (see [[project-split-case-divergence-root]]).
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
    // Avoid set for freshToFreeAvoidingFast: vars in (s2, s1_0).
    // HS: `evalFreshAvoiding (s2, s1_0)` — frees of the tuple.
    let mut avoid_set: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    // s2's domain
    for v in s2.dom() { avoid_set.insert(v.clone()); }
    // s2's range vars
    for t in s2.range() {
        for v in crate::vterm::vars_vterm(t) { avoid_set.insert(v); }
    }
    // s1_0's domain
    for v in s1_0.dom() { avoid_set.insert(v.clone()); }
    // s1_0's range vars
    for v in s1_0.vars_range() { avoid_set.insert(v); }
    let avoid: Vec<LVar> = avoid_set.into_iter().collect();
    let s1 = extended.fresh_to_free_uniform_shift(&avoid);
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
}
