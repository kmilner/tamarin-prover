//! Port of `Term.Substitution.SubstVFree` (the *generic* part — no LTerm
//! dependency yet) from `lib/term/src/Term/Substitution/SubstVFree.hs`.
//!
//! We model a substitution as a `BTreeMap<V, VTerm<C, V>>` and apply it via
//! [`apply_vterm`], which preserves AC normal form by routing through the
//! smart constructors in [`crate::term`].
//!
//! The Haskell `Apply` typeclass and the `LSubst`/`LNSubst` aliases live in
//! later modules that depend on `LTerm`.

use std::collections::BTreeMap;

use crate::function_symbols::FunSym;
use crate::term::{f_app_ac, f_app_c, f_app_list, f_app_no_eq, lit, Term};
use crate::vterm::{Lit, VTerm};

/// A substitution mapping variables of type `V` to terms of type
/// `VTerm<C, V>`. The Haskell newtype is kept transparent here — callers
/// usually want to inspect or build the mapping.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Subst<C, V> {
    map: BTreeMap<V, VTerm<C, V>>,
}

impl<C, V> Default for Subst<C, V> {
    fn default() -> Self { Subst { map: BTreeMap::new() } }
}

impl<C, V> Subst<C, V>
where
    C: Ord + Clone,
    V: Ord + Clone,
{
    pub fn empty() -> Self { Subst::default() }

    /// `substFromList`: drop trivial `x ~> x` mappings, then build.
    pub fn from_list(pairs: impl IntoIterator<Item = (V, VTerm<C, V>)>) -> Self {
        let mut m = BTreeMap::new();
        for (v, t) in pairs {
            if !equal_to_var(&t, &v) {
                m.insert(v, t);
            }
        }
        Subst { map: m }
    }

    /// `substFromMap`: drop trivial `x ~> x` mappings.
    pub fn from_map(m: BTreeMap<V, VTerm<C, V>>) -> Self {
        let m = m.into_iter().filter(|(v, t)| !equal_to_var(t, v)).collect();
        Subst { map: m }
    }

    pub fn dom(&self) -> impl Iterator<Item = &V> { self.map.keys() }
    pub fn range(&self) -> impl Iterator<Item = &VTerm<C, V>> { self.map.values() }
    pub fn image_of(&self, v: &V) -> Option<&VTerm<C, V>> { self.map.get(v) }
    pub fn to_list(&self) -> Vec<(V, VTerm<C, V>)> {
        self.map.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }
    pub fn is_empty(&self) -> bool { self.map.is_empty() }
    pub fn len(&self) -> usize { self.map.len() }

    /// `restrict vars`: keep only mappings whose key is in `vars`.
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
        Subst { map }
    }

    /// `mapRange f`: rewrite every range element with `f`, dropping any
    /// resulting trivial `x ~> x` entries.
    pub fn map_range<F: FnMut(VTerm<C, V>) -> VTerm<C, V>>(&self, mut f: F) -> Self {
        let map = self
            .map
            .iter()
            .filter_map(|(v, t)| {
                let t2 = f(t.clone());
                if equal_to_var(&t2, v) { None } else { Some((v.clone(), t2)) }
            })
            .collect();
        Subst { map }
    }

    /// `applySubst self other` = apply `self` to the range of `other`.
    pub fn apply_subst(&self, other: &Self) -> Self {
        other.map_range(|t| apply_vterm(self, t))
    }

    /// `compose s1 s2` = `s1 . s2`. Effect: applying the result is the same
    /// as applying `s2` then `s1`.
    pub fn compose(&self, other: &Self) -> Self {
        let mut composed = self.apply_subst(other).map.clone();
        // Add bindings from `self` whose domain is not already in `other`.
        for (v, t) in &self.map {
            if !other.map.contains_key(v) {
                composed.insert(v.clone(), t.clone());
            }
        }
        Subst { map: composed }
    }
}

/// Whether `t` is just the literal variable `v`.
fn equal_to_var<C, V: PartialEq>(t: &VTerm<C, V>, v: &V) -> bool {
    matches!(t, Term::Lit(Lit::Var(w)) if w == v)
}

/// `applyLit`: substitute a single literal.
pub fn apply_lit<C: Ord + Clone, V: Ord + Clone>(s: &Subst<C, V>, l: &Lit<C, V>) -> VTerm<C, V> {
    match l {
        Lit::Var(v) => match s.image_of(v) {
            Some(t) => t.clone(),
            None => lit(Lit::Var(v.clone())),
        },
        Lit::Con(c) => lit(Lit::Con(c.clone())),
    }
}

/// `applyVTerm`: substitute through a whole term, re-AC-normalising.
pub fn apply_vterm<C: Ord + Clone, V: Ord + Clone>(
    s: &Subst<C, V>,
    t: VTerm<C, V>,
) -> VTerm<C, V> {
    match t {
        Term::Lit(l) => apply_lit(s, &l),
        Term::App(fsym, args) => {
            let mapped: Vec<VTerm<C, V>> =
                args.into_iter().map(|a| apply_vterm(s, a)).collect();
            match fsym {
                FunSym::Ac(o) => f_app_ac(o, mapped),
                FunSym::C(o) => f_app_c(o, mapped),
                FunSym::NoEq(o) => f_app_no_eq(o, mapped),
                FunSym::List => f_app_list(mapped),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{pair_sym, AcSym};
    use crate::term::{f_app_ac, f_app_no_eq};
    use crate::vterm::{const_term, var_term};

    type C = u32;
    type V = &'static str;

    #[test]
    fn empty_substitution_is_identity() {
        let s: Subst<C, V> = Subst::empty();
        let t: VTerm<C, V> = f_app_no_eq(pair_sym(), vec![var_term("x"), const_term(1)]);
        assert_eq!(apply_vterm(&s, t.clone()), t);
    }

    #[test]
    fn from_list_drops_trivial() {
        let s: Subst<C, V> =
            Subst::from_list(vec![("x", var_term("x")), ("y", const_term(1))]);
        // `x ~> x` is dropped, only `y ~> 1` remains.
        assert_eq!(s.dom().copied().collect::<Vec<_>>(), vec!["y"]);
    }

    #[test]
    fn apply_replaces_variables() {
        let s: Subst<C, V> = Subst::from_list(vec![("x", const_term(7))]);
        let t: VTerm<C, V> = f_app_no_eq(pair_sym(), vec![var_term("x"), var_term("y")]);
        let out = apply_vterm(&s, t);
        assert_eq!(
            out,
            f_app_no_eq(pair_sym(), vec![const_term(7), var_term("y")])
        );
    }

    #[test]
    fn apply_preserves_ac_normalization() {
        // mult(x, 3) with {x ~> 1} should become mult(1, 3) — sorted.
        let t: VTerm<C, V> =
            f_app_ac(AcSym::Mult, vec![var_term("x"), const_term(3)]);
        let s: Subst<C, V> = Subst::from_list(vec![("x", const_term(1))]);
        let out = apply_vterm(&s, t);
        // Substitution may reorder; arguments must be sorted.
        if let Term::App(_, ts) = out {
            assert_eq!(ts, vec![const_term(1), const_term(3)]);
        } else {
            panic!("expected AC application");
        }
    }

    #[test]
    fn compose_applies_right_then_left() {
        // s1 = {x ~> y}, s2 = {y ~> 1}. Then (s1 ∘ s2)(x) should equal
        // s1(s2(x)) = s1(x) = y, but `compose` uses Haskell semantics:
        // `compose s1 s2` is `s1.s2` — applying the result has the same
        // effect as `s1(s2(t))`.
        let s1: Subst<C, V> = Subst::from_list(vec![("x", var_term("y"))]);
        let s2: Subst<C, V> = Subst::from_list(vec![("y", const_term(1))]);
        let composed = s1.compose(&s2);
        let t: VTerm<C, V> = var_term("x");
        // Per Haskell docstring: applying composed to t == s1(s2(t)).
        // s2(x) = x (no binding), s1(x) = y. So composed(x) = y.
        // But the convention is the *other* direction: s1.s2 means s1
        // *after* s2; i.e. composed(x) = s1(s2(x)) = s1(x) = y.
        assert_eq!(apply_vterm(&composed, t), var_term("y"));
        // And for y: s2(y) = 1, s1(1) = 1.
        let t: VTerm<C, V> = var_term("y");
        assert_eq!(apply_vterm(&composed, t), const_term(1));
    }

    #[test]
    fn restrict_filters_domain() {
        let s: Subst<C, V> = Subst::from_list(vec![
            ("x", const_term(1)),
            ("y", const_term(2)),
            ("z", const_term(3)),
        ]);
        let r = s.restrict(&["x", "z"]);
        let dom: Vec<&V> = r.dom().collect();
        assert_eq!(dom, vec![&"x", &"z"]);
    }
}
