//! Port of `Term.Subsumption` — subsumption ordering on terms.
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

use crate::lterm::LNTerm;
use crate::maude_proc::{MaudeError, MaudeHandle};
use crate::rewriting::Equal;

/// Compare two terms under the subsumption order modulo the
/// configured equational theory. Returns `None` if the two are
/// incomparable, or `Some(Ord)` otherwise.
///
/// Uses Maude's matcher. Port of HS `compareTermSubs`
/// (`Subsumption.hs`):
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
/// (`Definitions.hs`). So arm A = `t1 matchWith t2` matches
/// **subject t1** against **pattern t2** (∃σ. `t1 =AC σ(t2)`, i.e.
/// `t2` subsumes `t1`); A non-empty + B empty ⇒ `GT`. Hence
/// `Some(Greater)` means `t1` is strictly MORE SPECIFIC than `t2`.
///
/// **Convention trap.** `match_eqs` takes `Equal { lhs = subject,
/// rhs = pattern }` (HS's `Equal subject pattern`, see its doc). So
/// HS's `t1 matchWith t2` ⇒ `Equal { lhs: t1, rhs: t2 }` — keep
/// `lhs = subject`, `rhs = pattern`. Flipping the two would swap
/// `Greater`/`Less` (only `eq_term_subs` is invariant under the swap).
///
/// Intentionally retained: faithful HS port (`Subsumption.hs`);
/// exercised by tests but with no production caller yet.
#[allow(dead_code)]
pub(crate) fn compare_term_subs(
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
///
/// Intentionally retained: faithful HS port (`Subsumption.hs`); no
/// caller yet.
#[allow(dead_code)]
pub(crate) fn eq_term_subs(
    maude: &MaudeHandle,
    t1: &LNTerm,
    t2: &LNTerm,
) -> Result<bool, MaudeError> {
    Ok(matches!(compare_term_subs(maude, t1, t2)?, Some(Ordering::Equal)))
}
