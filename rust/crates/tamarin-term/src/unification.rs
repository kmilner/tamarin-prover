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
enum FreshSrc<'a> {
    Local(u64),
    Shared(&'a AtomicU64),
}

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
            // Maude emits a fresh witness at the narrower sub-sort for
            // EVERY var-var pair (verified empirically — even
            // `x:Msg idx 0 =? y:Msg idx 1` becomes
            // `{x → ~mw:Msg w, y → ~mw:Msg w}`, not `y → x`).  The
            // witness-heavy shape is what downstream eq-store /
            // freshen_witness_range / subst-system expect.  When sorts
            // are disjoint (Pub vs Fresh, etc.) no unifier exists.
            use std::cmp::Ordering;
            let narrower_sort = match sort_compare(vl.sort, vr.sort) {
                Some(Ordering::Equal) => vl.sort,
                Some(Ordering::Greater) => vr.sort,
                Some(Ordering::Less) => vl.sort,
                None => return Err(UnifyError::NoUnifier),
            };
            let w = LVar {
                name: "~mw".to_string(),
                sort: narrower_sort,
                idx: src.next(),
            };
            let wt: LTerm<C> = Term::Lit(Lit::Var(w));
            eliminate(sort_of_const, acc, vl.clone(), wt.clone())?;
            eliminate(sort_of_const, acc, vr.clone(), wt)
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
