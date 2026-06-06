//! Port of `Term.Subsumption` — subsumption ordering on terms and a
//! canonical form for fresh-range substitutions.
//!
//! Subsumption: `t1 ≤ t2` iff there exists a substitution `s` such that
//! `s(t1) =AC= t2`. We say `t1` subsumes `t2` when `t1` is the more
//! general (i.e. has at most as much information as) of the two.
//!
//! The Haskell version uses Maude AC matching to decide subsumption.
//! For the Rust port we expose the same shape (`compare_term_subs`)
//! but rely on a callable `match_oracle` so callers can plug in a
//! Maude-driven matcher. A `MaudeHandle`-backed convenience exists
//! too.

use std::cmp::Ordering;
use std::collections::BTreeMap;

use crate::lterm::{LNTerm, LVar};
use crate::maude_proc::{MaudeError, MaudeHandle};
use crate::rewriting::Equal;
use crate::subst_vfresh::LNSubstVFresh;
use crate::term::Term;

/// Compare two terms under the subsumption order modulo the
/// configured equational theory. Returns `None` if the two are
/// incomparable, or `Some(Ord)` otherwise.
///
/// Uses Maude's matcher. `Some(Ordering::Greater)` means `t1` is
/// strictly more specific than `t2` (there's a match `t2 = pattern,
/// t1 = subject`); `Less` is the reverse; `Equal` means both
/// directions match.
pub fn compare_term_subs(
    maude: &MaudeHandle,
    t1: &LNTerm,
    t2: &LNTerm,
) -> Result<Option<Ordering>, MaudeError> {
    // pattern =? subject means we want subject to match pattern.
    let match_12 = maude.match_eqs(&[Equal { lhs: t2.clone(), rhs: t1.clone() }])?;
    let match_21 = maude.match_eqs(&[Equal { lhs: t1.clone(), rhs: t2.clone() }])?;
    Ok(match (match_12.is_empty(), match_21.is_empty()) {
        (true, true) => None,
        (false, true) => Some(Ordering::Greater),
        (true, false) => Some(Ordering::Less),
        (false, false) => Some(Ordering::Equal),
    })
}

/// Subsumption equality.
pub fn eq_term_subs(
    maude: &MaudeHandle,
    t1: &LNTerm,
    t2: &LNTerm,
) -> Result<bool, MaudeError> {
    Ok(matches!(compare_term_subs(maude, t1, t2)?, Some(Ordering::Equal)))
}

/// Counts every variable occurrence across a list of terms — used by
/// `canonize_subst` for ordering.
pub fn var_occurrences(ts: &[LNTerm]) -> BTreeMap<LVar, usize> {
    let mut out: BTreeMap<LVar, usize> = BTreeMap::new();
    fn go(t: &LNTerm, out: &mut BTreeMap<LVar, usize>) {
        match t {
            Term::Lit(crate::vterm::Lit::Var(v)) => {
                *out.entry(v.clone()).or_insert(0) += 1;
            }
            Term::Lit(_) => {}
            Term::App(_, args) => for a in args.iter() { go(a, out); }
        }
    }
    for t in ts { go(t, &mut out); }
    out
}

/// Canonicalise a fresh-range substitution: rename the range
/// variables to a deterministic sequence (`x.1`, `x.2`, ...) using
/// the order of first occurrence (with ties broken by occurrence
/// count, matching Haskell's `sortOn (`lookup` occs)`).
///
/// Two substitutions equivalent modulo renaming will canonicalise to
/// the same value.
pub fn canonize_subst(s: &LNSubstVFresh) -> LNSubstVFresh {
    let range: Vec<LNTerm> = s.range().cloned().collect();
    let occs = var_occurrences(&range);
    let mut range_vars: Vec<LVar> = s.vars_range();
    // Sort by occurrence count (asc) — matches `sortOn` in Haskell.
    range_vars.sort_by_key(|v| occs.get(v).copied().unwrap_or(0));
    // Build renaming: each var → x.<i> with the original sort.
    let mut rename: BTreeMap<LVar, LVar> = BTreeMap::new();
    for (i, v) in range_vars.iter().enumerate() {
        rename.insert(
            v.clone(),
            LVar::new("x".to_string(), v.sort, (i + 1) as u64),
        );
    }
    // Apply renaming to each range term.
    let new_pairs: Vec<(LVar, LNTerm)> = s.to_list().into_iter()
        .map(|(domv, t)| (domv, rename_term(&t, &rename)))
        .collect();
    LNSubstVFresh::from_list(new_pairs)
}

fn rename_term(t: &LNTerm, rename: &BTreeMap<LVar, LVar>) -> LNTerm {
    match t {
        Term::Lit(crate::vterm::Lit::Var(v)) => match rename.get(v) {
            Some(nv) => Term::Lit(crate::vterm::Lit::Var(nv.clone())),
            None => t.clone(),
        },
        Term::Lit(_) => t.clone(),
        Term::App(sym, args) => Term::App(sym.clone(),
            args.iter().map(|a| rename_term(a, rename)).collect()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::LSort;
    use crate::vterm::Lit;

    #[test]
    fn var_occurrences_counts() {
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        let xs = vec![
            Term::Lit(Lit::Var(x.clone())),
            Term::Lit(Lit::Var(x.clone())),
            Term::Lit(Lit::Var(y.clone())),
        ];
        let occs = var_occurrences(&xs);
        assert_eq!(occs[&x], 2);
        assert_eq!(occs[&y], 1);
    }

    #[test]
    fn canonize_renames_range() {
        let x = LVar::new("orig", LSort::Msg, 7);
        let v = LVar::new("v", LSort::Msg, 0);
        let s = LNSubstVFresh::from_list(vec![
            (v, Term::Lit(Lit::Var(x))),
        ]);
        let c = canonize_subst(&s);
        // The range should now be `x.1` (msg-sort).
        let pairs = c.to_list();
        assert_eq!(pairs.len(), 1);
        match &pairs[0].1 {
            Term::Lit(Lit::Var(rv)) => {
                assert_eq!(rv.name, "x");
                assert_eq!(rv.sort, LSort::Msg);
                assert_eq!(rv.idx, 1);
            }
            x => panic!("expected renamed var, got {:?}", x),
        }
    }

    #[test]
    fn canonize_is_idempotent() {
        let x = LVar::new("orig", LSort::Msg, 7);
        let v = LVar::new("v", LSort::Msg, 0);
        let s = LNSubstVFresh::from_list(vec![
            (v, Term::Lit(Lit::Var(x))),
        ]);
        let c1 = canonize_subst(&s);
        let c2 = canonize_subst(&c1);
        assert_eq!(c1, c2);
    }
}
