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

#[derive(Debug, Clone, PartialEq, Eq)]
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
