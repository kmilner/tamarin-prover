//! Port of `Term.Term.Raw` from `lib/term/src/Term/Term/Raw.hs`.
//!
//! The core term datatype with its smart constructors and view types.
//! AC operators (Mult, Xor, Union, NatPlus) are normalised by [`f_app`]:
//! arguments are flattened across nested same-symbol applications and
//! sorted into a canonical order.

use crate::function_symbols::{AcSym, CSym, FunSym, NoEqSym};

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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term<A> {
    Lit(A),
    App(FunSym, Vec<Term<A>>),
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
        FunSym::List => Term::App(FunSym::List, ts),
        FunSym::NoEq(_) => Term::App(fsym, ts),
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
    Term::App(target, flat)
}

/// Commutative (non-associative) smart constructor: just sorts arguments.
pub fn f_app_c<A: Ord + Clone>(sym: CSym, mut args: Vec<Term<A>>) -> Term<A> {
    args.sort();
    Term::App(FunSym::C(sym), args)
}

/// Free (NoEq) smart constructor.
pub fn f_app_no_eq<A>(sym: NoEqSym, args: Vec<Term<A>>) -> Term<A> {
    Term::App(FunSym::NoEq(sym), args)
}

/// `LIST` smart constructor.
pub fn f_app_list<A>(args: Vec<Term<A>>) -> Term<A> {
    Term::App(FunSym::List, args)
}

/// Direct constructor — caller must ensure AC normalisation themselves.
pub fn unsafe_f_app<A>(fsym: FunSym, args: Vec<Term<A>>) -> Term<A> {
    Term::App(fsym, args)
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
                ts.into_iter().map(|c| replace_subterm(f, c)).collect();
            Term::App(s, new_ts)
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
                ts.into_iter().map(|c| replace_subterm(f, c)).collect();
            Term::App(s, new_ts)
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
                assert_eq!(ts, vec![nat(1), nat(2)]);
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
                assert_eq!(ts, vec![nat(1), nat(2)]);
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
                assert_eq!(ts, vec![nat(11), nat(12)]);
            }
            _ => panic!(),
        }
    }
}
