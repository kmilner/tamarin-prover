//! Port of `Term.Term.Raw` from `lib/term/src/Term/Term/Raw.hs`.
//!
//! The core term datatype with its smart constructors and view types.
//! AC operators (Mult, Xor, Union, NatPlus) are normalised by [`f_app`]:
//! arguments are flattened across nested same-symbol applications and
//! sorted into a canonical order.

use crate::function_symbols::{AcSym, CSym, FunSym, NoEqSym};
use std::sync::Arc;

/// Diff annotation — whether the left or right interpretation of `diff` is
/// in scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DiffType {
    Left,
    Right,
    None,
    Both,
}

/// A term over literal type `A`. Construct via [`lit`] / [`f_app`] /
/// [`f_app_no_eq`] / [`f_app_list`] — never via the variants directly,
/// because [`Term::App`] expects AC-normalised argument lists.
///
/// Children of [`Term::App`] are held in an `Arc<[_]>` so that cloning a
/// `Term` is O(1) (one atomic refcount bump on `Arc<[_]>`) instead of a
/// recursive deep clone.  This mirrors GHC's structural sharing of term
/// subtrees: a `Term` in Haskell is a pointer-sized value that is shared
/// across many sites by reference, never deep-copied.  Profiling shows
/// that with the prior `Vec<Term<A>>` children, ~50% of solver CPU was
/// spent in `Term::clone` / `mi_malloc` / `mi_free` on the hot path
/// `subst_system_once → Goal::clone → Fact::clone → Vec::clone →
/// Term::clone`.  The `Arc<[_]>` form makes that O(1).
///
/// Reading (`args.iter()`, `args.len()`, `args[i]`, `&args[..]`) is
/// unchanged because `Arc<[_]>` derefs to `[_]`.  Construction sites
/// convert via `vec.into()` (or `Arc::from(vec)`); destructure-and-
/// consume patterns use `args.iter().cloned()` (each child clone is
/// itself O(1)).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term<A> {
    Lit(A),
    App(FunSym, Arc<[Term<A>]>),
}

/// Mirror view that distinguishes the two cases — kept for parity with the
/// Haskell `TermView`. Since Rust's `match` already lets you destructure
/// `Term::Lit`/`Term::App` directly, this is mostly here for documentation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TermView<'a, A> {
    Lit(&'a A),
    App(&'a FunSym, &'a [Term<A>]),
}

impl<A> Term<A> {
    pub fn view(&self) -> TermView<'_, A> {
        match self {
            Term::Lit(l) => TermView::Lit(l),
            Term::App(s, ts) => TermView::App(s, ts),
        }
    }
}

// =============================================================================
// Smart constructors
// =============================================================================

/// `lit l`: build a literal term.
pub fn lit<A>(l: A) -> Term<A> { Term::Lit(l) }

/// `fApp fsym ts`: smart constructor that AC-normalises when needed.
///
/// Pre-condition: every term in `ts` must already be AC-normalised.
pub fn f_app<A: Ord + Clone>(fsym: FunSym, ts: Vec<Term<A>>) -> Term<A> {
    match fsym {
        FunSym::Ac(s) => f_app_ac(s, ts),
        FunSym::C(c) => f_app_c(c, ts),
        FunSym::List => Term::App(FunSym::List, ts.into()),
        FunSym::NoEq(_) => Term::App(fsym, ts.into()),
    }
}

/// AC smart constructor: flattens nested same-symbol applications, sorts
/// the resulting argument list, and unwraps singletons.
pub fn f_app_ac<A: Ord + Clone>(sym: AcSym, args: Vec<Term<A>>) -> Term<A> {
    if args.is_empty() {
        panic!("f_app_ac: empty argument list");
    }
    if args.len() == 1 {
        return args.into_iter().next().unwrap();
    }
    let target = FunSym::Ac(sym);
    let mut flat: Vec<Term<A>> = Vec::with_capacity(args.len());
    for a in args {
        match a {
            Term::App(ref s, ref children) if *s == target => {
                flat.extend(children.iter().cloned());
            }
            _ => flat.push(a),
        }
    }
    flat.sort();
    Term::App(target, flat.into())
}

/// Commutative (non-associative) smart constructor: just sorts arguments.
pub fn f_app_c<A: Ord + Clone>(sym: CSym, mut args: Vec<Term<A>>) -> Term<A> {
    args.sort();
    Term::App(FunSym::C(sym), args.into())
}

/// Free (NoEq) smart constructor.
pub fn f_app_no_eq<A>(sym: NoEqSym, args: Vec<Term<A>>) -> Term<A> {
    Term::App(FunSym::NoEq(sym), args.into())
}

/// `LIST` smart constructor.
pub fn f_app_list<A>(args: Vec<Term<A>>) -> Term<A> {
    Term::App(FunSym::List, args.into())
}

/// Direct constructor — caller must ensure AC normalisation themselves.
pub fn unsafe_f_app<A>(fsym: FunSym, args: Vec<Term<A>>) -> Term<A> {
    Term::App(fsym, args.into())
}

// =============================================================================
// Subterm tests / counts
// =============================================================================

pub fn is_subterm<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> bool {
    if needle == haystack { return true; }
    is_proper_subterm(needle, haystack)
}

pub fn is_proper_subterm<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> bool {
    match haystack {
        Term::App(_, ts) => ts.iter().any(|t| is_subterm(needle, t)),
        Term::Lit(_) => false,
    }
}

pub fn count_subterms<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> usize {
    if needle == haystack { return 1; }
    count_proper_subterms(needle, haystack)
}

pub fn count_proper_subterms<A: PartialEq>(needle: &Term<A>, haystack: &Term<A>) -> usize {
    match haystack {
        Term::App(_, ts) => ts.iter().map(|t| count_subterms(needle, t)).sum(),
        Term::Lit(_) => 0,
    }
}

// =============================================================================
// Replacement helpers (top-down)
// =============================================================================

pub fn replace_subterm<A: Clone, F: FnMut(Term<A>) -> Term<A>>(
    f: &mut F,
    t: Term<A>,
) -> Term<A> {
    let new = f(t);
    match new {
        Term::Lit(_) => new,
        Term::App(s, ts) => {
            let new_ts: Vec<Term<A>> =
                ts.iter().cloned().map(|c| replace_subterm(f, c)).collect();
            Term::App(s, new_ts.into())
        }
    }
}

pub fn replace_proper_subterm<A: Clone, F: FnMut(Term<A>) -> Term<A>>(
    f: &mut F,
    t: Term<A>,
) -> Term<A> {
    match t {
        Term::App(s, ts) => {
            let new_ts: Vec<Term<A>> =
                ts.iter().cloned().map(|c| replace_subterm(f, c)).collect();
            Term::App(s, new_ts.into())
        }
        Term::Lit(_) => t,
    }
}

// =============================================================================
// Sized: structural size including AC arg count.
// =============================================================================

pub trait Sized {
    fn size(&self) -> usize;
}

impl<A: Sized> Sized for Term<A> {
    fn size(&self) -> usize {
        match self {
            Term::Lit(a) => a.size(),
            Term::App(_, ts) => ts.iter().map(|t| t.size()).sum::<usize>() + 1,
        }
    }
}

// Sensible default impls for the literal types we'll actually use.
impl Sized for u64 { fn size(&self) -> usize { 1 } }
impl Sized for i64 { fn size(&self) -> usize { 1 } }
impl Sized for String { fn size(&self) -> usize { 1 } }
impl Sized for &str { fn size(&self) -> usize { 1 } }

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function_symbols::{exp_sym, pair_sym, AcSym, CSym, FunSym};

    fn nat(n: u64) -> Term<u64> { lit(n) }

    #[test]
    fn ac_flattens_and_sorts() {
        // mult(mult(3, 1), 2) → mult(1, 2, 3)
        let inner = f_app_ac(AcSym::Mult, vec![nat(3), nat(1)]);
        let outer = f_app_ac(AcSym::Mult, vec![inner, nat(2)]);
        match outer {
            Term::App(FunSym::Ac(AcSym::Mult), ref ts) => {
                let lits: Vec<u64> = ts.iter().map(|t| match t {
                    Term::Lit(n) => *n,
                    _ => unreachable!(),
                }).collect();
                assert_eq!(lits, vec![1, 2, 3]);
            }
            _ => panic!("expected AC Mult application"),
        }
    }

    #[test]
    fn ac_singleton_unwrap() {
        let t = f_app_ac(AcSym::Mult, vec![nat(7)]);
        assert_eq!(t, nat(7));
    }

    #[test]
    fn ac_flattening_is_idempotent() {
        let t1 = f_app_ac(AcSym::Xor, vec![nat(1), nat(2), nat(3)]);
        let t2 = f_app_ac(AcSym::Xor, vec![t1.clone(), nat(0)]);
        // Should be a single Xor with [0,1,2,3].
        match t2 {
            Term::App(FunSym::Ac(AcSym::Xor), ts) => {
                assert_eq!(ts.len(), 4);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn c_sorts_arguments() {
        let t = f_app_c(CSym::EMap, vec![nat(2), nat(1)]);
        match t {
            Term::App(FunSym::C(CSym::EMap), ts) => {
                assert_eq!(&*ts, &[nat(1), nat(2)]);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn no_eq_preserves_order() {
        // pair(1, 2) keeps argument order; pair is not commutative.
        let t = f_app_no_eq(pair_sym(), vec![nat(1), nat(2)]);
        match t {
            Term::App(FunSym::NoEq(s), ts) => {
                assert_eq!(s, pair_sym());
                assert_eq!(&*ts, &[nat(1), nat(2)]);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn subterm_basics() {
        let inner = f_app_no_eq(pair_sym(), vec![nat(1), nat(2)]);
        let outer = f_app_no_eq(exp_sym(), vec![inner.clone(), nat(3)]);
        assert!(is_subterm(&inner, &outer));
        assert!(is_subterm(&nat(2), &outer));
        assert!(!is_subterm(&nat(99), &outer));
        // A term is its own subterm but not its own proper subterm.
        assert!(is_subterm(&outer, &outer));
        assert!(!is_proper_subterm(&outer, &outer));
    }

    #[test]
    fn count_subterms_counts_occurrences() {
        // pair(x, pair(x, y)) contains x twice.
        let x = nat(1);
        let y = nat(2);
        let inner = f_app_no_eq(pair_sym(), vec![x.clone(), y.clone()]);
        let outer = f_app_no_eq(pair_sym(), vec![x.clone(), inner]);
        assert_eq!(count_subterms(&x, &outer), 2);
        assert_eq!(count_subterms(&y, &outer), 1);
    }

    #[test]
    fn replace_subterm_top_down() {
        let t = f_app_no_eq(pair_sym(), vec![nat(1), nat(2)]);
        let mut f = |t: Term<u64>| match t {
            Term::Lit(n) => Term::Lit(n + 10),
            other => other,
        };
        let r = replace_subterm(&mut f, t);
        match r {
            Term::App(_, ts) => {
                assert_eq!(&*ts, &[nat(11), nat(12)]);
            }
            _ => panic!(),
        }
    }

    // =========================================================================
    // Haskell-faithfulness invariants for AC/C/NoEq term constructors.
    // =========================================================================

    /// AC terms with the same multiset are *equal* mod-AC: `+(a, b)` and
    /// `+(b, a)` get sorted to the same canonical form, so structural
    /// equality holds.  Haskell-faithful: AC canonicalization happens at
    /// construction time (`fAppAC` in Term/Term/Raw.hs).
    #[test]
    fn ac_terms_are_equal_modulo_argument_order() {
        let t1 = f_app_ac(AcSym::Mult, vec![nat(7), nat(2), nat(5)]);
        let t2 = f_app_ac(AcSym::Mult, vec![nat(5), nat(7), nat(2)]);
        let t3 = f_app_ac(AcSym::Mult, vec![nat(2), nat(5), nat(7)]);
        assert_eq!(t1, t2,
            "AC terms with same multiset of args must compare equal — \
             smart constructor canonicalizes order");
        assert_eq!(t1, t3);
    }

    /// AC vs C distinction: C terms ARE sorted but NOT flattened.  NoEq
    /// terms preserve argument order.
    #[test]
    fn ac_flattens_but_c_does_not() {
        // AC: mult(mult(1,2), 3) → mult(1,2,3) — flat.
        let nested_ac = f_app_ac(AcSym::Mult, vec![
            f_app_ac(AcSym::Mult, vec![nat(1), nat(2)]),
            nat(3),
        ]);
        match &nested_ac {
            Term::App(FunSym::Ac(AcSym::Mult), ts) => {
                assert_eq!(ts.len(), 3, "AC must flatten nested same-sym");
            }
            _ => panic!(),
        }
        // C is non-associative; nested EMap doesn't flatten.
        let nested_c = f_app_c(CSym::EMap, vec![
            f_app_c(CSym::EMap, vec![nat(1), nat(2)]),
            nat(3),
        ]);
        match &nested_c {
            Term::App(FunSym::C(CSym::EMap), ts) => {
                assert_eq!(ts.len(), 2, "C must NOT flatten — non-associative");
            }
            _ => panic!(),
        }
    }

    /// `f_app_ac` panics on empty argument list — matching Haskell's
    /// `fAppAC` which is undefined on []. Empty AC terms are nonsensical
    /// (there's no identity element at the term layer).
    #[test]
    #[should_panic(expected = "empty argument list")]
    fn ac_panics_on_empty_args() {
        let _: Term<u64> = f_app_ac(AcSym::Mult, vec![]);
    }

    /// Lit::Con < Lit::Var: constants sort before variables.
    /// VTerm.hs:56: `data Lit c v = Con c | Var v`.
    ///
    /// This matters for `f_app_ac`/`f_app_c` argument sorting: if a
    /// term mixes constants and variables, constants always sort first.
    /// Downstream code in atom_valuation expects constants in fixed
    /// positions when matching.
    #[test]
    fn lit_con_sorts_before_lit_var() {
        use crate::lterm::{LNTerm, LVar, LSort, Name, NameTag, NameId};
        use crate::vterm::Lit;

        // Variant tags: Con=0, Var=1 in Haskell decl order.
        let pub_a = Name { tag: NameTag::Pub, id: NameId::new("a") };
        let v_x = LVar::new("x", LSort::Msg, 0);
        let con: LNTerm = Term::Lit(Lit::Con(pub_a));
        let var: LNTerm = Term::Lit(Lit::Var(v_x));
        assert!(con < var,
                "Lit::Con must sort before Lit::Var (Haskell decl order). \
                 AC term canonicalization relies on this — `+(x, 'a')` \
                 canonicalizes to `+('a', x)`.");
    }

    /// `BVar::Bound < BVar::Free` from LTerm.hs:451-453 declaration order.
    /// `data BVar v = Bound Integer | Free v`
    ///
    /// This drives the BTreeMap key order for guarded-formula
    /// binders/bound-var lookup — when we de Bruijn-index a formula's
    /// quantified variables, the bound positions sort before any free
    /// occurrences.
    #[test]
    fn bvar_bound_sorts_before_bvar_free() {
        use crate::lterm::{BVar, LVar, LSort};
        let bound: BVar<LVar> = BVar::Bound(5);
        let free: BVar<LVar> = BVar::Free(LVar::new("x", LSort::Msg, 0));
        assert!(bound < free,
                "BVar::Bound must sort before BVar::Free \
                 (Haskell LTerm.hs:451 declaration order)");
    }
}
