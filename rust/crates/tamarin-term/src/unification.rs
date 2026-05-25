//! Port of the *non-AC* portion of `Term.Unification` from
//! `lib/term/src/Term/Unification.hs`.
//!
//! Tamarin performs unification in two phases: free unification with
//! delayed AC equations, then ships the AC equations off to Maude. Without
//! a Maude bridge we can only soundly handle the AC-free case — if the
//! input contains AC operators we return `None` (no unifier found) rather
//! than risking an unsound result.
//!
//! Matching follows the same split.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::function_symbols::FunSym;
use crate::lterm::{sort_compare, sort_of_lterm, LSort, LTerm, LVar, Name};
use crate::rewriting::{Equal, Match};
use crate::subst::{apply_vterm, Subst};
use crate::term::Term;
use crate::vterm::Lit;

/// Source of fresh witness indices for the local non-AC unifier.
///
/// Wraps either a private local counter (legacy "per-call" behaviour,
/// kept for callers that don't have a shared counter) or a shared
/// `AtomicU64` (the Haskell-faithful `MonadFresh` path, used by
/// `MaudeHandle::unify_with_avoid`).  Allocating from a shared counter
/// guarantees indices are globally unique across all calls in a proof
/// session — the fix for the TESLA::authentic_reachable
/// `~mw:Pub:17` / `~mw:Msg:17` cross-call collision.
// Carrier kept around because callers thread it through `unify_raw`
// for future use (e.g. minting witnesses when sort narrowing is
// extended past the current named-var-orientation logic).  The
// fields/method are reserved for that path.
#[allow(dead_code)]
enum FreshSrc<'a> {
    Local(u64),
    Shared(&'a AtomicU64),
}

#[allow(dead_code)]
impl<'a> FreshSrc<'a> {
    fn next(&mut self) -> u64 {
        match self {
            FreshSrc::Local(c) => {
                let v = 1_000_000_000 + *c;
                *c += 1;
                v
            }
            FreshSrc::Shared(a) => a.fetch_add(1, Ordering::SeqCst),
        }
    }
}

#[derive(Debug)]
pub enum UnifyError {
    NoUnifier,
    /// AC equation encountered — unsupported without Maude.
    NeedsAC,
}

/// `unifyLTermNoAC` — non-AC unification. Returns a single most-general
/// unifier or `Err(UnifyError::NoUnifier)` / `Err(UnifyError::NeedsAC)`.
///
/// **Sort narrowing**: when two LVars have disjoint sub-sorts, the
/// unifier mints a fresh `~mw` witness at the narrower sort and binds
/// both inputs to it.  This mirrors Maude's order-sorted output shape
/// so the downstream eq-store + freshen_witness_range pipeline can
/// treat local unifier output and Maude output uniformly.  The
/// witness index starts at `u64::MAX - n` for the n-th witness so
/// callers can recognise and re-fresh them globally.
pub fn unify_lterm_no_ac<C, F>(
    sort_of_const: &F,
    eqs: Vec<Equal<LTerm<C>>>,
) -> Result<Subst<C, LVar>, UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let mut acc: BTreeMap<LVar, LTerm<C>> = BTreeMap::new();
    let mut src = FreshSrc::Local(0);
    for Equal { lhs, rhs } in eqs {
        unify_raw(sort_of_const, &mut acc, lhs, rhs, &mut src)?;
    }
    Ok(Subst::from_map(acc))
}

/// Convenience: `unifyLNTermNoAC`.
pub fn unify_lnterm_no_ac(
    eqs: Vec<Equal<crate::lterm::LNTerm>>,
) -> Result<Subst<Name, LVar>, UnifyError> {
    unify_lterm_no_ac(&|n: &Name| crate::lterm::sort_of_name(n), eqs)
}

/// Variant that draws witness idxs from a shared atomic counter
/// (Haskell `MonadFresh`).  Use this when calling from inside a Maude
/// bridge so witnesses get globally-unique idxs across all unify
/// calls — preventing the cross-call collision class.
pub fn unify_lnterm_no_ac_with_counter(
    eqs: Vec<Equal<crate::lterm::LNTerm>>,
    counter: &AtomicU64,
) -> Result<Subst<Name, LVar>, UnifyError> {
    let sort_of_const = |n: &Name| crate::lterm::sort_of_name(n);
    let mut acc: BTreeMap<LVar, LTerm<Name>> = BTreeMap::new();
    let mut src = FreshSrc::Shared(counter);
    for Equal { lhs, rhs } in eqs {
        unify_raw(&sort_of_const, &mut acc, lhs, rhs, &mut src)?;
    }
    Ok(Subst::from_map(acc))
}

/// `unifiableLNTermsNoAC`: shorthand for "is there a unifier?".
pub fn unifiable_lnterms_no_ac(
    a: crate::lterm::LNTerm,
    b: crate::lterm::LNTerm,
) -> bool {
    matches!(unify_lnterm_no_ac(vec![Equal::new(a, b)]), Ok(_))
}

fn unify_raw<C, F>(
    sort_of_const: &F,
    acc: &mut BTreeMap<LVar, LTerm<C>>,
    lhs: LTerm<C>,
    rhs: LTerm<C>,
    src: &mut FreshSrc<'_>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let snapshot = Subst::from_map(acc.clone());
    let l = apply_vterm(&snapshot, lhs);
    let r = apply_vterm(&snapshot, rhs);

    match (&l, &r) {
        (Term::Lit(Lit::Var(vl)), Term::Lit(Lit::Var(vr))) if vl == vr => Ok(()),
        (Term::Lit(Lit::Var(vl)), Term::Lit(Lit::Var(vr))) => {
            // Haskell-faithful var-var orientation (Unification.hs:240-246):
            //   same-sort   → if vl < vr then elim vr l else elim vl r
            //   vl ⊇ vr     → elim vl r   (broader becomes KEY)
            //   otherwise   → elim vr l   (broader becomes KEY)
            //
            // For same-sort, LARGER-idx becomes KEY; smaller-idx
            // becomes value.  This is the orientation that makes
            // `restrict stableVars` (Sources.hs:118) and `applySource`
            // (Sources.hs:178) work — stable pattern vars (small idx)
            // stay on the value side and get dropped by the key-filter.
            use std::cmp::Ordering;
            match sort_compare(vl.sort, vr.sort) {
                Some(Ordering::Equal) => {
                    // Haskell `unifyRaw` (Unification.hs:241):
                    //   `if vl < vr then elim vr l else elim vl r`
                    // Larger-idx becomes KEY, smaller-idx becomes value.
                    let (key, val) = if vl < vr {
                        (vr.clone(), Term::Lit(Lit::Var(vl.clone())))
                    } else {
                        (vl.clone(), Term::Lit(Lit::Var(vr.clone())))
                    };
                    eliminate(sort_of_const, acc, key, val)
                }
                Some(Ordering::Greater) => {
                    // vl > vr (vl is broader) → bind vl to vr.
                    eliminate(sort_of_const, acc,
                        vl.clone(), Term::Lit(Lit::Var(vr.clone())))
                }
                Some(Ordering::Less) => {
                    // vl < vr (vr is broader) → bind vr to vl.
                    eliminate(sort_of_const, acc,
                        vr.clone(), Term::Lit(Lit::Var(vl.clone())))
                }
                None => Err(UnifyError::NoUnifier),
            }
        }
        (Term::Lit(Lit::Var(vl)), _) => eliminate(sort_of_const, acc, vl.clone(), r.clone()),
        (_, Term::Lit(Lit::Var(vr))) => eliminate(sort_of_const, acc, vr.clone(), l.clone()),
        (Term::Lit(Lit::Con(cl)), Term::Lit(Lit::Con(cr))) => {
            if cl == cr { Ok(()) } else { Err(UnifyError::NoUnifier) }
        }
        (Term::App(FunSym::NoEq(lf), la), Term::App(FunSym::NoEq(rf), ra))
            if lf == rf && la.len() == ra.len() =>
        {
            for (a, b) in la.clone().into_iter().zip(ra.clone()) {
                unify_raw(sort_of_const, acc, a, b, src)?;
            }
            Ok(())
        }
        (Term::App(FunSym::List, la), Term::App(FunSym::List, ra)) if la.len() == ra.len() => {
            for (a, b) in la.clone().into_iter().zip(ra.clone()) {
                unify_raw(sort_of_const, acc, a, b, src)?;
            }
            Ok(())
        }
        (Term::App(FunSym::Ac(_), _), _) | (_, Term::App(FunSym::Ac(_), _)) => {
            Err(UnifyError::NeedsAC)
        }
        (Term::App(FunSym::C(_), _), _) | (_, Term::App(FunSym::C(_), _)) => {
            Err(UnifyError::NeedsAC)
        }
        _ => Err(UnifyError::NoUnifier),
    }
}

/// Haskell-faithful factored unification: same as `unify_raw` but
/// **pushes AC/C equations to a delayed list** instead of returning
/// `NeedsAC`.  Mirrors Haskell's `unifyRaw` (Unification.hs:230-280)
/// which uses `tell [Equal l r]` from a writer monad to delay AC.
///
/// Also uses Haskell's same-sort var-var orientation: when `vl < vr`
/// (under idx-first Ord), `elim vr l` — i.e., **larger-idx becomes
/// the KEY**, smaller-idx the value.  This is the orientation Haskell's
/// `restrict stableVars` (Sources.hs:118) and `applySource` (Sources.hs:178)
/// depend on: stable pattern vars (small idx) stay on the value side so
/// they're never keys and never survive the post-saturate key-filter.
fn unify_raw_factored<C, F>(
    sort_of_const: &F,
    acc: &mut BTreeMap<LVar, LTerm<C>>,
    delayed: &mut Vec<Equal<LTerm<C>>>,
    lhs: LTerm<C>,
    rhs: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let snapshot = Subst::from_map(acc.clone());
    let l = apply_vterm(&snapshot, lhs);
    let r = apply_vterm(&snapshot, rhs);

    match (&l, &r) {
        (Term::Lit(Lit::Var(vl)), Term::Lit(Lit::Var(vr))) if vl == vr => Ok(()),
        (Term::Lit(Lit::Var(vl)), Term::Lit(Lit::Var(vr))) => {
            use std::cmp::Ordering;
            match sort_compare(vl.sort, vr.sort) {
                Some(Ordering::Equal) => {
                    // Haskell: `if vl < vr then elim vr l else elim vl r`
                    // (Unification.hs:241).  Under idx-first Ord LVar
                    // (LTerm.hs:521-523), `vl < vr` iff `vl.idx < vr.idx`
                    // (modulo same sort/name).  `elim vr l` makes `vr`
                    // the KEY mapped to `l` (which is the LVar form of
                    // `vl`).  So **larger-idx becomes KEY**, smaller-idx
                    // becomes value.
                    let (key, val) = if vl < vr {
                        (vr.clone(), Term::Lit(Lit::Var(vl.clone())))
                    } else {
                        (vl.clone(), Term::Lit(Lit::Var(vr.clone())))
                    };
                    eliminate(sort_of_const, acc, key, val)
                }
                Some(Ordering::Greater) => {
                    // vl > vr in sort (vl is broader) → bind vl to vr.
                    eliminate(sort_of_const, acc,
                        vl.clone(), Term::Lit(Lit::Var(vr.clone())))
                }
                Some(Ordering::Less) => {
                    // vl < vr in sort (vr is broader) → bind vr to vl.
                    eliminate(sort_of_const, acc,
                        vr.clone(), Term::Lit(Lit::Var(vl.clone())))
                }
                None => Err(UnifyError::NoUnifier),
            }
        }
        (Term::Lit(Lit::Var(vl)), _) => eliminate(sort_of_const, acc, vl.clone(), r.clone()),
        (_, Term::Lit(Lit::Var(vr))) => eliminate(sort_of_const, acc, vr.clone(), l.clone()),
        (Term::Lit(Lit::Con(cl)), Term::Lit(Lit::Con(cr))) => {
            if cl == cr { Ok(()) } else { Err(UnifyError::NoUnifier) }
        }
        (Term::App(FunSym::NoEq(lf), la), Term::App(FunSym::NoEq(rf), ra))
            if lf == rf && la.len() == ra.len() =>
        {
            for (a, b) in la.clone().into_iter().zip(ra.clone()) {
                unify_raw_factored(sort_of_const, acc, delayed, a, b)?;
            }
            Ok(())
        }
        (Term::App(FunSym::List, la), Term::App(FunSym::List, ra)) if la.len() == ra.len() => {
            for (a, b) in la.clone().into_iter().zip(ra.clone()) {
                unify_raw_factored(sort_of_const, acc, delayed, a, b)?;
            }
            Ok(())
        }
        (Term::App(FunSym::Ac(_), _), _) | (_, Term::App(FunSym::Ac(_), _)) => {
            // Haskell: `tell [Equal l r]` — delay for Maude.
            delayed.push(Equal { lhs: l.clone(), rhs: r.clone() });
            Ok(())
        }
        (Term::App(FunSym::C(_), _), _) | (_, Term::App(FunSym::C(_), _)) => {
            // Haskell: `tell [Equal l r]` — delay for Maude.
            delayed.push(Equal { lhs: l.clone(), rhs: r.clone() });
            Ok(())
        }
        _ => Err(UnifyError::NoUnifier),
    }
}

/// `unifyLTermFactored` port (Unification.hs:107-120).  Returns the
/// non-AC substitution and the residual AC equations (already with
/// the non-AC subst applied).  Callers ship the residuals to Maude.
///
/// Returns `None` if the non-AC fragment is unsatisfiable.
pub fn unify_lterm_factored<C, F>(
    sort_of_const: &F,
    eqs: Vec<Equal<LTerm<C>>>,
) -> Option<(Subst<C, LVar>, Vec<Equal<LTerm<C>>>)>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let mut acc: BTreeMap<LVar, LTerm<C>> = BTreeMap::new();
    let mut delayed: Vec<Equal<LTerm<C>>> = Vec::new();
    for Equal { lhs, rhs } in eqs {
        match unify_raw_factored(sort_of_const, &mut acc, &mut delayed, lhs, rhs) {
            Ok(()) => {}
            Err(UnifyError::NoUnifier) => return None,
            // unify_raw_factored never returns NeedsAC.
            Err(UnifyError::NeedsAC) => return None,
        }
    }
    let subst = Subst::from_map(acc);
    // Apply the freshly-built subst to the delayed residuals so Maude
    // sees the most-refined form (mirrors Haskell's
    // `map (applyVTerm subst <$>) leqs`).
    let delayed = delayed.into_iter().map(|Equal { lhs, rhs }| Equal {
        lhs: apply_vterm(&subst, lhs),
        rhs: apply_vterm(&subst, rhs),
    }).collect();
    Some((subst, delayed))
}

/// Convenience for `LNTerm`s.
pub fn unify_lnterm_factored(
    eqs: Vec<Equal<crate::lterm::LNTerm>>,
) -> Option<(Subst<Name, LVar>, Vec<Equal<crate::lterm::LNTerm>>)> {
    unify_lterm_factored(&|n: &Name| crate::lterm::sort_of_name(n), eqs)
}

fn eliminate<C, F>(
    sort_of_const: &F,
    acc: &mut BTreeMap<LVar, LTerm<C>>,
    v: LVar,
    t: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    if occurs_lvar(&v, &t) {
        return Err(UnifyError::NoUnifier);
    }
    if !sort_geq_lterm(sort_of_const, &v, &t) {
        return Err(UnifyError::NoUnifier);
    }
    // Substitute `v ~> t` through the existing accumulator.
    let s = Subst::from_list(vec![(v.clone(), t.clone())]);
    let updated: BTreeMap<LVar, LTerm<C>> = acc
        .iter()
        .map(|(k, ts)| (k.clone(), apply_vterm(&s, ts.clone())))
        .collect();
    *acc = updated;
    acc.insert(v, t);
    Ok(())
}

/// `occurs v t` for an `LTerm` — direct recursion (avoids the generic
/// `HasFrees` machinery so we don't have to thread its trait bounds).
fn occurs_lvar<C>(v: &LVar, t: &LTerm<C>) -> bool {
    match t {
        Term::Lit(Lit::Var(w)) => w == v,
        Term::Lit(Lit::Con(_)) => false,
        Term::App(_, args) => args.iter().any(|a| occurs_lvar(v, a)),
    }
}

fn sort_geq_lterm<C, F: Fn(&C) -> LSort>(sort_of_const: &F, v: &LVar, t: &LTerm<C>) -> bool {
    let s_t = sort_of_lterm(t, |c| sort_of_const(c));
    let s_v = v.sort;
    if s_v == s_t { return true; }
    if s_v == LSort::Node || s_t == LSort::Node { return false; }
    matches!(sort_compare(s_v, s_t), Some(std::cmp::Ordering::Equal | std::cmp::Ordering::Greater))
}

// =============================================================================
// Free matching (no AC).
// =============================================================================

/// `solveMatchLNTermNoAC`: solve a matching problem in the AC-free
/// fragment. Returns the resulting substitution or `None` if either no
/// matcher exists or an AC equation is encountered.
pub fn solve_match_lterm_no_ac<C, F>(
    sort_of_const: &F,
    problem: Match<LTerm<C>>,
) -> Option<Subst<C, LVar>>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    let pairs = problem.flatten()?;
    let mut mapping: BTreeMap<LVar, LTerm<C>> = BTreeMap::new();
    for (term, pattern) in pairs {
        match_raw(sort_of_const, &mut mapping, term, pattern).ok()?;
    }
    Some(Subst::from_map(mapping))
}

fn match_raw<C, F>(
    sort_of_const: &F,
    mapping: &mut BTreeMap<LVar, LTerm<C>>,
    t: LTerm<C>,
    p: LTerm<C>,
) -> Result<(), UnifyError>
where
    C: Ord + Clone,
    F: Fn(&C) -> LSort,
{
    match p {
        Term::Lit(Lit::Var(vp)) => {
            if let Some(existing) = mapping.get(&vp) {
                if existing == &t { return Ok(()); }
                return Err(UnifyError::NoUnifier);
            }
            if !sort_geq_lterm(sort_of_const, &vp, &t) {
                return Err(UnifyError::NoUnifier);
            }
            mapping.insert(vp, t);
            Ok(())
        }
        Term::Lit(Lit::Con(cp)) => match t {
            Term::Lit(Lit::Con(ct)) if ct == cp => Ok(()),
            _ => Err(UnifyError::NoUnifier),
        },
        Term::App(FunSym::NoEq(pf), pargs) => match t {
            Term::App(FunSym::NoEq(tf), targs) if tf == pf && targs.len() == pargs.len() => {
                for (a, b) in targs.into_iter().zip(pargs) {
                    match_raw(sort_of_const, mapping, a, b)?;
                }
                Ok(())
            }
            _ => Err(UnifyError::NoUnifier),
        },
        Term::App(FunSym::List, pargs) => match t {
            Term::App(FunSym::List, targs) if targs.len() == pargs.len() => {
                for (a, b) in targs.into_iter().zip(pargs) {
                    match_raw(sort_of_const, mapping, a, b)?;
                }
                Ok(())
            }
            _ => Err(UnifyError::NoUnifier),
        },
        Term::App(FunSym::Ac(_), _) | Term::App(FunSym::C(_), _) => Err(UnifyError::NeedsAC),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{msg_var, pair, pk};
    use crate::lterm::LNTerm;

    #[test]
    fn unify_two_distinct_variables() {
        let x: LNTerm = msg_var("x", 0);
        let y: LNTerm = msg_var("y", 0);
        let s = unify_lnterm_no_ac(vec![Equal::new(x, y)]).unwrap();
        assert!(!s.is_empty());
    }

    #[test]
    fn unify_var_with_term() {
        let x: LNTerm = msg_var("x", 0);
        let p: LNTerm = pair(msg_var("a", 0), msg_var("b", 0));
        let s = unify_lnterm_no_ac(vec![Equal::new(x.clone(), p.clone())]).unwrap();
        assert_eq!(apply_vterm(&s, x), p);
    }

    #[test]
    fn unify_fails_on_constructor_mismatch() {
        // pair(x,y) vs pk(x): can't unify, different constructors.
        let lhs: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let rhs: LNTerm = pk(msg_var("z", 0));
        assert!(unify_lnterm_no_ac(vec![Equal::new(lhs, rhs)]).is_err());
    }

    #[test]
    fn unify_occurs_check() {
        // x = pair(x, y) — should fail (x occurs in RHS).
        let x: LNTerm = msg_var("x", 0);
        let rhs: LNTerm = pair(x.clone(), msg_var("y", 0));
        assert!(unify_lnterm_no_ac(vec![Equal::new(x, rhs)]).is_err());
    }

    #[test]
    fn match_pattern_variable_against_constant_term() {
        // Match: term=pair(a,b), pattern=pair(x,y).
        let t: LNTerm = pair(msg_var("a", 0), msg_var("b", 0));
        let p: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let problem = Match::match_with(t.clone(), p);
        let s = solve_match_lterm_no_ac(&|n| crate::lterm::sort_of_name(n), problem).unwrap();
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn match_fails_on_different_arity() {
        let t: LNTerm = pk(msg_var("a", 0));
        let p: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let problem = Match::match_with(t, p);
        assert!(solve_match_lterm_no_ac(&|n| crate::lterm::sort_of_name(n), problem).is_none());
    }
}

// =============================================================================
// Haskell-faithfulness invariants
// =============================================================================
//
// These tests pin semantic choices we missed during the initial port and
// only caught after weeks of mis-directed debugging.  The cost of getting
// any of these wrong is a silent divergence — the wrong unifier "works"
// in the logical sense (produces equivalent equality classes) but the
// SHAPE of the result differs, which downstream code can implicitly
// depend on.
//
// If any of these tests fails, STOP and investigate before chasing a
// downstream symptom — the root is here at the term layer.
//
// References to Haskell source are checked-in as of the May 2026 port
// state; line numbers may drift but the contracts shouldn't.
#[cfg(test)]
mod haskell_invariants {
    use super::*;
    use crate::builtin::{fresh_var, msg_var, pair, pub_var};
    use crate::lterm::{LNTerm, LSort, LVar};
    use crate::vterm::Lit;

    /// Helper: extract the LVar from an `LNTerm` known to be a var lit.
    fn as_var(t: &LNTerm) -> &LVar {
        match t {
            Term::Lit(Lit::Var(v)) => v,
            _ => panic!("expected var, got {:?}", t),
        }
    }

    // -------------------------------------------------------------------
    // 1. `Ord LVar` is idx-first (LTerm.hs:521-523).
    //
    //    The most-easily-missed semantic choice.  Rust's `#[derive(Ord)]`
    //    gives name-first lexicographic order, which is the *opposite*
    //    of Haskell.  Without this, `restrict stableVars` produces
    //    different post-filter substitutions, `BTreeMap<LVar, _>`
    //    iteration order differs, and `applySource` enters the wrong
    //    branch.
    //
    //    Comment from Haskell: "An ord instance that prefers the
    //    'lvarIdx' over the 'lvarName'."
    // -------------------------------------------------------------------

    #[test]
    fn lvar_ord_is_idx_first_then_sort_then_name() {
        // Same name, different idx — idx breaks the tie.
        let a = LVar::new("x", LSort::Msg, 1);
        let b = LVar::new("x", LSort::Msg, 5);
        assert!(a < b, "smaller idx must be < larger idx (same name)");

        // Different name, smaller idx beats larger name.
        // If Ord were name-first, "z.1" > "a.5".  Haskell-faithful:
        // idx-first means "z.1" < "a.5".
        let za = LVar::new("z", LSort::Msg, 1);
        let aa = LVar::new("a", LSort::Msg, 5);
        assert!(za < aa, "name 'z' idx 1 must be < name 'a' idx 5 (idx-first)");

        // Same idx and sort, name as tiebreaker.
        let ax = LVar::new("a", LSort::Msg, 3);
        let bx = LVar::new("b", LSort::Msg, 3);
        assert!(ax < bx, "name 'a' < name 'b' when idx and sort tie");

        // Same idx and name, sort as tiebreaker.  LSort derive Ord puts
        // Pub < Fresh < Msg < Node < Nat (declaration order).  Haskell's
        // sort enum order is also declaration-based.
        let pa = LVar::new("a", LSort::Pub, 3);
        let fa = LVar::new("a", LSort::Fresh, 3);
        assert!(pa < fa, "Pub < Fresh as sort tiebreaker");
    }

    #[test]
    fn lvar_ord_btreemap_iteration_is_idx_first() {
        // BTreeMap<LVar, ...> iteration order matters for goal-ranking
        // and subst.dom() iteration.  Insert in name order, expect
        // idx-first iteration.
        let mut m = std::collections::BTreeMap::new();
        m.insert(LVar::new("z", LSort::Msg, 1), 'a');
        m.insert(LVar::new("a", LSort::Msg, 10), 'b');
        m.insert(LVar::new("m", LSort::Msg, 5), 'c');
        let keys_in_order: Vec<u64> = m.keys().map(|k| k.idx).collect();
        assert_eq!(keys_in_order, vec![1, 5, 10],
                   "BTreeMap iterates LVars in idx order, NOT name order");
    }

    // -------------------------------------------------------------------
    // 2. Same-sort var-var unification: larger-idx becomes the KEY.
    //
    //    Haskell `unifyRaw` (Unification.hs:241):
    //        (sl, sr) | sl == sr -> if vl < vr then elim vr l else elim vl r
    //    `elim v t` makes `v` the KEY mapped to `t`.  So when vl < vr
    //    (vl has smaller idx under idx-first Ord), eliminate vr →
    //    LARGER-idx is the KEY.
    //
    //    This is the orientation that makes `restrict stableVars`
    //    (Sources.hs:118) work: stable pattern vars (small idx) stay
    //    on the value side and get dropped by the key-filter.
    // -------------------------------------------------------------------

    #[test]
    fn factored_unify_orients_var_var_with_larger_idx_as_key() {
        // Set up the exact pattern from foo_eligibility's saturate:
        // unify `t.1 = e.10` (both Msg, t.1 is "stable pattern var",
        // e.10 is "rule-internal").  Haskell convention: e.10 becomes
        // KEY, t.1 stays as value.
        let stable = msg_var("t", 1);
        let rule_internal = msg_var("e", 10);
        let (subst, residuals) =
            unify_lnterm_factored(vec![Equal::new(stable.clone(), rule_internal.clone())])
                .expect("non-AC same-sort vars must unify");
        assert!(residuals.is_empty(), "no AC stuff, no residuals");
        // Larger-idx (e.10) is the key.
        let e_10 = as_var(&rule_internal).clone();
        let t_1  = as_var(&stable).clone();
        assert!(subst.image_of(&e_10).is_some(),
                "Haskell convention: larger-idx (e.10) must be a KEY");
        assert!(subst.image_of(&t_1).is_none(),
                "Haskell convention: smaller-idx (t.1, stable) must NOT be a key — \
                 otherwise `restrict stableVars` would keep it and downstream \
                 applySource would see a baked-in binding instead of an \
                 unbound stable var");
    }

    #[test]
    fn factored_unify_same_sort_order_independent_of_input_order() {
        // The orientation depends on Ord LVar, not the order of LHS/RHS
        // in the equation.  Swap and confirm same result.
        let stable = msg_var("t", 1);
        let rule_internal = msg_var("e", 10);

        let (s1, _) = unify_lnterm_factored(vec![Equal::new(
            stable.clone(), rule_internal.clone()
        )]).unwrap();
        let (s2, _) = unify_lnterm_factored(vec![Equal::new(
            rule_internal.clone(), stable.clone()
        )]).unwrap();

        let e_10 = as_var(&rule_internal).clone();
        // Both directions: e.10 (larger idx) is the key, regardless of
        // whether it was on lhs or rhs of the equation.
        assert!(s1.image_of(&e_10).is_some());
        assert!(s2.image_of(&e_10).is_some());
        assert_eq!(s1, s2, "orientation is determined by Ord LVar, not input order");
    }

    #[test]
    fn factored_unify_orients_var_var_per_haskell_when_idxs_tie() {
        // When idx ties, Haskell falls back to sort then name.  Two Msg
        // vars same idx, different names: name is final tiebreaker.
        let alpha = msg_var("a", 3);
        let beta  = msg_var("b", 3);
        let (subst, _) = unify_lnterm_factored(vec![Equal::new(
            alpha.clone(), beta.clone()
        )]).unwrap();
        let a_3 = as_var(&alpha).clone();
        let b_3 = as_var(&beta).clone();
        // Ord: a.3 < b.3 (idx tie → sort tie → name 'a' < 'b').
        // unifyRaw: vl=a.3, vr=b.3, vl<vr, elim vr l → b.3 is key.
        assert!(subst.image_of(&b_3).is_some(),
                "tiebreaker via name: 'b' (later) becomes key");
        assert!(subst.image_of(&a_3).is_none());
    }

    // -------------------------------------------------------------------
    // 3. Cross-sort var-var unification: narrower sort is the value.
    //
    //    Haskell `unifyRaw` (Unification.hs:243-246):
    //        _ | sortGeqLTerm sortOf vl r -> elim vl r
    //          | _                        -> elim vr l
    //    When vl's sort ⊇ vr's sort, vl is bound to vr — the broader
    //    var becomes the KEY mapping to the narrower one.
    // -------------------------------------------------------------------

    #[test]
    fn factored_unify_cross_sort_binds_broader_to_narrower() {
        // Msg ⊃ Fresh, so Msg var must be bound to Fresh var, not the
        // reverse.  (If reversed, a Fresh var would end up mapped to
        // a Msg term — sort would be widened illegally.)
        let m: LNTerm = msg_var("m", 5);
        let f: LNTerm = fresh_var("k", 100);

        let (subst, _) = unify_lnterm_factored(vec![Equal::new(
            m.clone(), f.clone()
        )]).unwrap();

        let m_v = as_var(&m).clone();
        let f_v = as_var(&f).clone();
        // The Msg var (broader sort) must be the KEY.
        assert!(subst.image_of(&m_v).is_some(),
                "broader sort (Msg) must be the KEY mapping to narrower (Fresh)");
        assert!(subst.image_of(&f_v).is_none(),
                "narrower sort (Fresh) must NOT be a key");
    }

    #[test]
    fn factored_unify_pub_msg_binds_msg_to_pub() {
        // Same principle: Pub ⊂ Msg.
        let m: LNTerm = msg_var("m", 5);
        let p: LNTerm = pub_var("A", 100);

        let (subst, _) = unify_lnterm_factored(vec![Equal::new(
            m.clone(), p.clone()
        )]).unwrap();

        let m_v = as_var(&m).clone();
        let p_v = as_var(&p).clone();
        assert!(subst.image_of(&m_v).is_some(), "Msg (broader) is key");
        assert!(subst.image_of(&p_v).is_none(), "Pub (narrower) is value");
    }

    #[test]
    fn factored_unify_pub_fresh_no_unifier() {
        // Pub and Fresh are incomparable sorts — should fail.
        let p: LNTerm = pub_var("A", 1);
        let f: LNTerm = fresh_var("k", 2);
        let result = unify_lnterm_factored(vec![Equal::new(p, f)]);
        assert!(result.is_none(),
                "Pub and Fresh are incomparable; unification must fail \
                 (Haskell `unifyRaw` mzeros, returning Nothing)");
    }

    // -------------------------------------------------------------------
    // 4. Var-vs-term: the var is always the KEY.
    //
    //    Haskell `unifyRaw` (Unification.hs:248-249):
    //        (Lit (Var vl), _           ) -> elim vl r
    //        (_,            Lit (Var vr)) -> elim vr l
    //    Both arms: the var (vl or vr) is the KEY, the term is the value.
    // -------------------------------------------------------------------

    #[test]
    fn factored_unify_var_vs_app_binds_var_to_app() {
        // unify `x = pair(a, b)` → subst {x → pair(a, b)}, regardless
        // of which side x is on.
        let x = msg_var("x", 5);
        let p = pair(msg_var("a", 10), msg_var("b", 20));

        let (s1, _) = unify_lnterm_factored(vec![Equal::new(x.clone(), p.clone())]).unwrap();
        let (s2, _) = unify_lnterm_factored(vec![Equal::new(p.clone(), x.clone())]).unwrap();

        let x_v = as_var(&x).clone();
        assert_eq!(s1.image_of(&x_v), Some(&p));
        assert_eq!(s2.image_of(&x_v), Some(&p));
        assert_eq!(s1, s2);
    }

    // -------------------------------------------------------------------
    // 5. `unifyLTermFactored` separates non-AC from AC residuals.
    //
    //    Haskell (Unification.hs:107-120):
    //        unifyLTermFactored sortOf eqs = ... do
    //            solve h $ execRWST unif sortOf M.empty
    //        unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
    //        solve _ (Just (m, [])) = (substFromMap m, [emptySubstVFresh])
    //
    //    For AC-free input, returns the local subst with EMPTY residuals.
    //    For mixed input, returns (local subst, residuals) where the
    //    residuals are AC equations only.
    // -------------------------------------------------------------------

    #[test]
    fn factored_unify_returns_empty_residuals_on_ac_free_input() {
        // All non-AC: pair + msg_var, no XOR/mset/DH/nat/BP.
        let p1: LNTerm = pair(msg_var("a", 1), msg_var("b", 2));
        let p2: LNTerm = pair(msg_var("x", 10), msg_var("y", 20));
        let (subst, residuals) = unify_lnterm_factored(vec![
            Equal::new(p1, p2)
        ]).expect("non-AC pair-pair must unify");
        assert!(residuals.is_empty(),
                "AC-free input → empty residuals (matches Haskell's \
                 `solve _ (Just (m, []))` branch).  If this fires, the \
                 unifier is incorrectly classifying something as AC.");
        // Subst has at least the 4 var bindings.
        assert!(!subst.is_empty(), "non-trivial input produces non-empty subst");
    }

    #[test]
    fn factored_unify_trivial_var_eq_self_returns_empty() {
        // `x = x` is trivially true — Haskell short-circuits before
        // emitting a binding.
        let x: LNTerm = msg_var("x", 5);
        let (subst, residuals) = unify_lnterm_factored(vec![
            Equal::new(x.clone(), x)
        ]).expect("x = x must unify trivially");
        assert!(residuals.is_empty());
        assert!(subst.is_empty(),
                "x = x must NOT introduce a self-loop binding");
    }

    #[test]
    fn factored_unify_unsatisfiable_returns_none() {
        // pair(x, y) vs single-arg constructor → no unifier.
        let p: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let k: LNTerm = crate::builtin::pk(msg_var("z", 0));
        assert!(unify_lnterm_factored(vec![Equal::new(p, k)]).is_none());
    }

    // -------------------------------------------------------------------
    // 6. Local non-AC subst with chained var-var: only the final
    //    representative survives as key when both vars are stable.
    //
    //    This is the foo_eligibility-class invariant: when we unify
    //    `m.19 = blind(...)` AFTER having unified `t.1 = m.19`, the
    //    resulting subst should have `t.1 → blind(...)` AND
    //    `m.19 → blind(...)` (eliminate substitutes the value through
    //    the accumulator).
    //
    //    Important: the orientation of `t.1 = m.19` (Haskell-faithful:
    //    m.19 → t.1, so larger-idx is key) means after we then unify
    //    m.19 with blind(...), m.19's existing binding to t.1 doesn't
    //    create a t.1 entry — because applying the eliminate's
    //    `apply_vterm(s, t)` to t.1 (not in m.19→t.1's domain) leaves
    //    t.1 unchanged.  So t.1 stays unbound.
    // -------------------------------------------------------------------

    #[test]
    fn factored_unify_chained_var_var_then_var_term() {
        // Step 1: unify t.1 = m.19.  Haskell: m.19 → t.1.
        // Step 2: unify m.19 = blind(...) (using `pair` as stand-in).
        //         After snapshot apply, m.19 substituted to t.1; then
        //         t.1 = pair(...) eliminates t.1 → pair(...).
        //         The chain: m.19 → t.1 → pair(...).  Eliminate
        //         substitutes t.1 into m.19's value, giving m.19 → pair(...).
        //         So final acc: {m.19 → pair(...), t.1 → pair(...)}.
        //
        // This is exactly the foo_eligibility shape — both bindings
        // exist, but the KEY for the "structural" binding (pair) is on
        // both t.1 AND m.19.
        let t_1 = msg_var("t", 1);
        let m_19 = msg_var("m", 19);
        let blind = pair(msg_var("m", 28), msg_var("r", 28));

        let (subst, _) = unify_lnterm_factored(vec![
            Equal::new(t_1.clone(), m_19.clone()),
            Equal::new(m_19.clone(), blind.clone()),
        ]).unwrap();

        let t_1_v = as_var(&t_1).clone();
        let m_19_v = as_var(&m_19).clone();
        assert_eq!(subst.image_of(&m_19_v), Some(&blind),
                   "m.19 must end bound to the structural term");
        // Crucially, t.1 should ALSO be bound — because eliminate(t.1, pair)
        // happens after snapshot apply of m.19→t.1, so the second eq
        // becomes t.1 = pair(...).  Both bindings end up.
        assert_eq!(subst.image_of(&t_1_v), Some(&blind),
                   "t.1 must also end bound (eliminate adds it as key)");
    }

    // -------------------------------------------------------------------
    // 7. Occurs check (Unification.hs:276): `v `occurs` t` → no unifier.
    // -------------------------------------------------------------------

    #[test]
    fn factored_unify_occurs_check() {
        // x = pair(x, y) — x occurs in RHS → no unifier.
        let x: LNTerm = msg_var("x", 0);
        let rhs: LNTerm = pair(x.clone(), msg_var("y", 0));
        assert!(unify_lnterm_factored(vec![Equal::new(x, rhs)]).is_none());
    }

    // -------------------------------------------------------------------
    // 8. The factored unify and the older `unify_lnterm_no_ac` agree on
    //    orientation for var-vs-non-var (both bind the var to the term)
    //    AND on same-sort var-var (Haskell-faithful: larger-idx is key,
    //    Unification.hs:241).  These tests pin both invariants.
    // -------------------------------------------------------------------

    #[test]
    fn old_and_factored_unify_agree_on_var_vs_term() {
        let x = msg_var("x", 5);
        let p = pair(msg_var("a", 10), msg_var("b", 20));
        let old = unify_lnterm_no_ac(vec![Equal::new(x.clone(), p.clone())]).unwrap();
        let (new_, _) = unify_lnterm_factored(vec![Equal::new(x.clone(), p.clone())]).unwrap();
        assert_eq!(old, new_,
                   "for var-vs-term, both unifiers must produce identical \
                    substs (the var is the key in both)");
    }

    #[test]
    fn old_and_factored_unify_agree_on_same_sort_var_var_orientation() {
        // Both paths follow Haskell `unifyRaw` (Unification.hs:241):
        //   `if vl < vr then elim vr l else elim vl r`
        // i.e. LARGER-idx becomes KEY, smaller-idx becomes value.
        let small = msg_var("t", 1);   // small idx, "stable"
        let large = msg_var("e", 10);  // large idx

        let old = unify_lnterm_no_ac(vec![Equal::new(small.clone(), large.clone())]).unwrap();
        let (new_, _) = unify_lnterm_factored(vec![Equal::new(small.clone(), large.clone())]).unwrap();

        let small_v = as_var(&small).clone();
        let large_v = as_var(&large).clone();

        // Haskell-faithful: larger-idx is key in BOTH paths.
        assert!(old.image_of(&large_v).is_some(),
                "`unify_raw`: larger-idx (e.10) is the key");
        assert!(old.image_of(&small_v).is_none());
        assert!(new_.image_of(&large_v).is_some(),
                "`unify_raw_factored`: larger-idx (e.10) is the key");
        assert!(new_.image_of(&small_v).is_none());

        assert_eq!(old, new_,
                   "Both unifiers must produce identical substs \
                    (Haskell-faithful: Unification.hs:241).");
    }
}
