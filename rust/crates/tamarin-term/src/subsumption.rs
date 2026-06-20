//! Port of `Term.Subsumption` — subsumption ordering on terms and a
//! canonical form for fresh-range substitutions.
//!
//! Subsumption: `t1 ≤ t2` iff there exists a substitution `s` such that
//! `s(t1) =AC= t2`. We say `t1` subsumes `t2` when `t1` is the more
//! general (i.e. has at most as much information as) of the two.
//!
//! The Haskell version uses Maude AC matching to decide subsumption.
//! Likewise here: `compare_term_subs` / `eq_term_subs` decide
//! subsumption by issuing two `maude.match_eqs` calls directly against
//! a `&MaudeHandle`.

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
/// Uses Maude's matcher. Port of HS `compareTermSubs`
/// (`lib/term/src/Term/Subsumption.hs:37-45`):
///
/// ```haskell
/// compareTermSubs t1 t2 = check <$> solveMatchLNTerm (t1 `matchWith` t2)
///                               <*> solveMatchLNTerm (t2 `matchWith` t1)
///   where check (_:_) []    = Just GT
///         check []    (_:_) = Just LT
///         check (_:_) (_:_) = Just EQ
///         check []    []    = Nothing
/// ```
///
/// `matchWith t p = DelayedMatches [(t, p)]` is `(subject, pattern)`
/// (`Definitions.hs:90-93`). So arm A = `t1 matchWith t2` matches
/// **subject t1** against **pattern t2** (∃σ. `t1 =AC σ(t2)`, i.e.
/// `t2` subsumes `t1`); A non-empty + B empty ⇒ `GT`. Hence
/// `Some(Greater)` means `t1` is strictly MORE SPECIFIC than `t2`.
///
/// **Convention trap.** `match_eqs` takes `Equal { lhs = subject,
/// rhs = pattern }` (HS's `Equal subject pattern`, see its doc). So
/// HS's `t1 matchWith t2` ⇒ `Equal { lhs: t1, rhs: t2 }` — keep
/// `lhs = subject`, `rhs = pattern`. Flipping the two would swap
/// `Greater`/`Less` (only `eq_term_subs` is invariant under the swap).
pub fn compare_term_subs(
    maude: &MaudeHandle,
    t1: &LNTerm,
    t2: &LNTerm,
) -> Result<Option<Ordering>, MaudeError> {
    // arm A: `t1 matchWith t2` = subject t1, pattern t2.
    let match_a = maude.match_eqs(&[Equal { lhs: t1.clone(), rhs: t2.clone() }])?;
    // arm B: `t2 matchWith t1` = subject t2, pattern t1.
    let match_b = maude.match_eqs(&[Equal { lhs: t2.clone(), rhs: t1.clone() }])?;
    Ok(match (match_a.is_empty(), match_b.is_empty()) {
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
///
/// NOTE: this is NOT a faithful port of Haskell `varOccurences`
/// (`lib/term/src/Term/Subsumption.hs`), which returns
/// `[(LVar, S.Set Occurence)]` (sets of context paths). Here we only
/// keep an occurrence COUNT per variable.
pub fn var_occurrence_counts(ts: &[LNTerm]) -> BTreeMap<LVar, usize> {
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
/// variables to a deterministic sequence (`x.1`, `x.2`, ...) ordered
/// by the key `(occurrence count, sort, first-occurrence position)`
/// — see lines 167-171.  This intentionally DIVERGES from HS's
/// `canonizeSubst`, which orders by `sortOn (`lookup` occs)` where
/// `occs` keys on a SET of context paths (`S.Set Occurence`,
/// `Occurence = [String]`), not a count; the count-based key here is
/// an alpha-invariant substitute, explained in the block below.
///
/// Two substitutions equivalent modulo renaming will canonicalise to
/// the same value.
///
/// **Alpha-invariance fix.** HS's `canonizeSubst`
/// (lib/term/src/Term/Subsumption.hs:67-77) sorts range vars by
/// `sortOn (`lookup` occs)`, which is stable in Haskell —
/// equal-occurrence ties are broken by the input order from
/// `varsRangeVFresh = varsVTerm . fAppList . rangeVFresh`, i.e.
/// `sortednub` (Ord LVar = idx<>sort<>name).  That tie-break is
/// **not** invariant under alpha-renaming: two alpha-equivalent
/// substs whose witness idxs differ will sort their tied vars in
/// different orders and canonicalise to different terms.
///
/// HS rarely hits this because its witness allocation is
/// deterministic on `avoid_max` — alpha-equivalent inputs land on
/// identical witness layouts.  RS's `applyBound` local unifier
/// (maude_proc.rs:706-717) allocates witness idxs based on the
/// inner unifier's `reserve_idxs` order, which DOES diverge between
/// alpha-equivalent inputs.  Without an alpha-invariant
/// canonicalisation, the post-Maude `BTreeSet<LNSubstVFresh>` dedup
/// in `apply_eq_store` (equation_store.rs:2552-2560) fails to
/// collapse the duplicates HS would catch via `S.fromList`
/// (EquationStore.hs:268).
///
/// The new ordering (asc) is:
///   1. occurrence count — same as HS.
///   2. tie-break by input var SORT (`Ord LSort` derived) —
///      alpha-invariant (alpha doesn't change a var's sort).
///   3. tie-break by FIRST-OCCURRENCE POSITION in a DFS traversal of
///      the range (in domain-key order) — alpha-invariant for the
///      non-AC subterm shape.
///   4. NEVER tie-break by input idx — that's what HS's `sortednub`
///      uses for ties, and it's alpha-variant.
///
/// In addition, range terms are rebuilt via `f_app` after renaming
/// so AC operators (Xor / Mult / Union / NatPlus) re-sort their arg
/// list by the renamed-term Ord.  Maude returns AC operands sorted
/// by input-var idx, which is alpha-variant; re-sorting by renamed
/// labels absorbs that.
pub fn canonize_subst(s: &LNSubstVFresh) -> LNSubstVFresh {
    let range: Vec<LNTerm> = s.range().cloned().collect();
    let occs = var_occurrence_counts(&range);
    // Compute first-occurrence position by DFS-walking the range terms
    // in domain-key order (BTreeMap iteration is by key Ord — stable
    // across alpha since domain vars are not renamed).
    let mut first_pos: BTreeMap<LVar, usize> = BTreeMap::new();
    let mut next_pos: usize = 0;
    fn dfs_pos(t: &LNTerm, fp: &mut BTreeMap<LVar, usize>, np: &mut usize) {
        match t {
            Term::Lit(crate::vterm::Lit::Var(v)) => {
                if !fp.contains_key(v) {
                    fp.insert(v.clone(), *np);
                    *np += 1;
                }
            }
            Term::Lit(_) => {}
            Term::App(_, args) => for a in args.iter() { dfs_pos(a, fp, np); }
        }
    }
    for (_, t) in s.to_list().iter() {
        dfs_pos(t, &mut first_pos, &mut next_pos);
    }
    let mut range_vars: Vec<LVar> = s.vars_range();
    // Sort by (occ count asc, input sort, first-pos) — all
    // alpha-invariant.  See HS's `sortOn (`lookup` occs)` plus the
    // alpha-invariance discussion above.
    range_vars.sort_by_key(|v| (
        occs.get(v).copied().unwrap_or(0),
        v.sort,
        first_pos.get(v).copied().unwrap_or(usize::MAX),
    ));
    // Build renaming: each var → x.<i>.  The renamed var's sort is
    // PRESERVED from the input — two substs that differ only in a
    // witness sort are not alpha-equivalent and must canonicalise
    // distinctly.
    let mut rename: BTreeMap<LVar, LVar> = BTreeMap::new();
    for (i, v) in range_vars.iter().enumerate() {
        rename.insert(
            v.clone(),
            LVar::new("x".to_string(), v.sort, (i + 1) as u64),
        );
    }
    // Apply renaming, using smart constructors so AC operators
    // re-sort their arg list by the new (renamed-term) Ord.
    let new_pairs: Vec<(LVar, LNTerm)> = s.to_list().into_iter()
        .map(|(domv, t)| (domv, rename_term_canonical(&t, &rename)))
        .collect();
    LNSubstVFresh::from_list(new_pairs)
}

/// Like a straight literal rename, but rebuilds App nodes via the
/// smart constructor `f_app`, which sorts AC operator arg lists.
/// Used only for canonical dedup keys, so it's safe to flatten+sort
/// even though `f_app_ac` requires "already AC-normalised" children
/// (the input range terms here are post-Maude, hence already
/// AC-normalised; renaming only substitutes individual vars and
/// doesn't break that).
fn rename_term_canonical(t: &LNTerm, rename: &BTreeMap<LVar, LVar>) -> LNTerm {
    use crate::term::f_app;
    match t {
        Term::Lit(crate::vterm::Lit::Var(v)) => match rename.get(v) {
            Some(nv) => Term::Lit(crate::vterm::Lit::Var(nv.clone())),
            None => t.clone(),
        },
        Term::Lit(_) => t.clone(),
        Term::App(sym, args) => {
            let renamed: Vec<LNTerm> = args.iter()
                .map(|a| rename_term_canonical(a, rename)).collect();
            // f_app dispatches: AC → flatten+sort; C → sort; NoEq/List
            // → straight-through.
            f_app(sym.clone(), renamed)
        }
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
        let occs = var_occurrence_counts(&xs);
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

    /// Regression for CH07::executable splitEqs(2): two alpha-equivalent
    /// substs from the post-Maude variant list were not deduplicated
    /// because `canonize_subst` used the alpha-variant Ord LVar tie-break.
    /// Reconstructed from /tmp/aes_err.log out[0] and out[4] of
    /// SplitId(2) 9 → 7 substs.
    #[test]
    fn canonize_collapses_alpha_equivalent_xor_substs() {
        use crate::function_symbols::{AcSym, FunSym};
        use crate::term::{f_app, Term as T};
        // Domain (identical):
        let dom_r1_1 = LVar::new("r1", LSort::Fresh, 1);
        let dom_r2_1 = LVar::new("r2", LSort::Msg, 1);
        let dom_k_879 = LVar::new("k", LSort::Fresh, 879);
        let dom_r2_880 = LVar::new("r2", LSort::Fresh, 880);
        let dom_r1_881 = LVar::new("r1", LSort::Msg, 881);

        // Subst A (= out[0]): identifies k.879 with r1.1.
        //   r1.1 → A/F, r2.1 → Xor(A, B, C), k.879 → A, r2.880 → B/F,
        //   r1.881 → C/M  where A=r1.884/F, B=r2.1763/F, C=r1.1764/M.
        let wa_a = LVar::new("r1", LSort::Fresh, 884);
        let wa_b = LVar::new("r2", LSort::Fresh, 1763);
        let wa_c = LVar::new("r1", LSort::Msg, 1764);
        let sa = LNSubstVFresh::from_list(vec![
            (dom_r1_1.clone(), T::Lit(Lit::Var(wa_a.clone()))),
            (dom_r2_1.clone(), f_app(FunSym::Ac(AcSym::Xor), vec![
                T::Lit(Lit::Var(wa_a.clone())),
                T::Lit(Lit::Var(wa_b.clone())),
                T::Lit(Lit::Var(wa_c.clone())),
            ])),
            (dom_k_879.clone(), T::Lit(Lit::Var(wa_a))),
            (dom_r2_880.clone(), T::Lit(Lit::Var(wa_b))),
            (dom_r1_881.clone(), T::Lit(Lit::Var(wa_c))),
        ]);

        // Subst B (= out[4]): identifies r1.1 with k.879 (same shape).
        //   r1.1 → C'/F, r2.1 → Xor(A'/M, C', B'), k.879 → C',
        //   r2.880 → B'/F, r1.881 → A'/M
        //   where A'=r1.13617/M, C'=k.13618/F, B'=r2.13619/F.
        let wb_a = LVar::new("r1", LSort::Msg, 13617);
        let wb_c = LVar::new("k", LSort::Fresh, 13618);
        let wb_b = LVar::new("r2", LSort::Fresh, 13619);
        let sb = LNSubstVFresh::from_list(vec![
            (dom_r1_1.clone(), T::Lit(Lit::Var(wb_c.clone()))),
            (dom_r2_1.clone(), f_app(FunSym::Ac(AcSym::Xor), vec![
                T::Lit(Lit::Var(wb_a.clone())),
                T::Lit(Lit::Var(wb_c.clone())),
                T::Lit(Lit::Var(wb_b.clone())),
            ])),
            (dom_k_879.clone(), T::Lit(Lit::Var(wb_c))),
            (dom_r2_880.clone(), T::Lit(Lit::Var(wb_b))),
            (dom_r1_881.clone(), T::Lit(Lit::Var(wb_a))),
        ]);

        let ca = canonize_subst(&sa);
        let cb = canonize_subst(&sb);
        // sa and sb are alpha-equivalent under witness rename — they
        // should canonicalise to the same value.
        assert_eq!(
            ca, cb,
            "alpha-equivalent substs must canonicalise identically.\n\
             ca = {:?}\ncb = {:?}",
            ca.to_list(), cb.to_list()
        );
    }

    /// Substs that differ only in witness SORT must NOT collapse.
    #[test]
    fn canonize_preserves_witness_sort_distinction() {
        let v = LVar::new("v", LSort::Msg, 1);
        let wf = LVar::new("w", LSort::Fresh, 5);
        let wm = LVar::new("w", LSort::Msg, 5);
        let s_fresh = LNSubstVFresh::from_list(vec![
            (v.clone(), Term::Lit(Lit::Var(wf))),
        ]);
        let s_msg = LNSubstVFresh::from_list(vec![
            (v, Term::Lit(Lit::Var(wm))),
        ]);
        let cf = canonize_subst(&s_fresh);
        let cm = canonize_subst(&s_msg);
        assert_ne!(cf, cm,
            "substs that differ only in witness sort must not collapse");
    }
}
