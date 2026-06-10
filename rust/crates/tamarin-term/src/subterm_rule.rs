//! Port of `Term.SubtermRule` from `lib/term/src/Term/SubtermRule.hs`.

use crate::lterm::{frees, LNTerm};
use crate::positions::{positions, positions_non_var, Position};
use crate::rewriting::RRule;
use crate::term::Term;

/// Right-hand side of a context subterm rewrite rule.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct StRhs {
    pub positions: Vec<Position>,
    pub term: LNTerm,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CtxtStRule {
    pub lhs: LNTerm,
    pub rhs: StRhs,
}

impl CtxtStRule {
    pub fn new(lhs: LNTerm, rhs: StRhs) -> Self { CtxtStRule { lhs, rhs } }

    pub fn to_rrule(&self) -> RRule<LNTerm> {
        RRule::new(self.lhs.clone(), self.rhs.term.clone())
    }
}

/// Find every position in `haystack` where `needle` occurs.
pub fn find_subterm(haystack: &LNTerm, needle: &LNTerm) -> Vec<Position> {
    fn go(haystack: &LNTerm, needle: &LNTerm, prefix: &mut Vec<i64>, out: &mut Vec<Position>) {
        if haystack == needle {
            out.push(prefix.clone());
            return;
        }
        if let Term::App(_, args) = haystack {
            for (i, a) in args.iter().enumerate() {
                prefix.push(i as i64);
                go(a, needle, prefix, out);
                prefix.pop();
            }
        }
    }
    let mut out = Vec::new();
    let mut prefix = Vec::new();
    go(haystack, needle, &mut prefix, &mut out);
    out
}

/// `findAllSubterms l r`: positions of `r` in `l`, recursing into `r`'s
/// subterms if `r` doesn't occur. Returns `None` if no variable in `r`
/// appears in `l`.
pub fn find_all_subterms(l: &LNTerm, r: &LNTerm) -> Option<Vec<Position>> {
    use crate::vterm::Lit;
    let direct = find_subterm(l, r);
    match r {
        Term::App(_, args) => {
            if !direct.is_empty() { return Some(direct); }
            let mut out = Vec::new();
            for sub in args.iter() {
                let parts = find_all_subterms(l, sub)?;
                out.extend(parts);
            }
            Some(out)
        }
        Term::Lit(Lit::Var(_)) => {
            if direct.is_empty() { None } else { Some(direct) }
        }
        Term::Lit(Lit::Con(_)) => None,
    }
}

/// `rRuleToCtxtStRule`: convert an `RRule` to a `CtxtStRule` if possible.
pub fn rrule_to_ctxt_st_rule(rule: &RRule<LNTerm>) -> Option<CtxtStRule> {
    if frees(&rule.rhs).is_empty() {
        // Pure right-hand-side; positions are constant positions of LHS.
        let positions = if crate::lterm::contains_private(&rule.lhs) {
            positions(&rule.lhs)
        } else {
            // Constant positions: positions in non-variable subterm structure.
            let candidates = positions_non_var(&rule.lhs);
            if candidates.is_empty() { positions(&rule.lhs) } else { candidates }
        };
        return Some(CtxtStRule::new(
            rule.lhs.clone(),
            StRhs { positions, term: rule.rhs.clone() },
        ));
    }
    let positions = find_all_subterms(&rule.lhs, &rule.rhs)?;
    if positions.is_empty() { return None; }
    if positions.contains(&Vec::<i64>::new()) { return None; } // proper subterm required
    Some(CtxtStRule::new(
        rule.lhs.clone(),
        StRhs { positions, term: rule.rhs.clone() },
    ))
}

/// `isSubtermConvergentCtxtRule`: RHS is constant or appears as a subterm
/// of LHS.
pub fn is_subterm_convergent(rule: &CtxtStRule) -> bool {
    let rhs = &rule.rhs.term;
    if frees(rhs).is_empty() { return true; }
    !find_subterm(&rule.lhs, rhs).is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{msg_var, pair};

    #[test]
    fn find_subterm_finds_all_occurrences() {
        let needle = msg_var("x", 0);
        let inner = pair(needle.clone(), msg_var("y", 0));
        let outer = pair(needle.clone(), inner);
        let positions = find_subterm(&outer, &needle);
        assert_eq!(positions.len(), 2);
    }

    #[test]
    fn rrule_with_constant_rhs() {
        use crate::builtin::true_const;
        use crate::lterm::Name;
        use crate::vterm::Lit;
        let lhs = pair(msg_var("x", 0), msg_var("y", 0));
        let rhs: LNTerm = true_const::<Lit<Name, _>>();
        let rule = RRule::new(lhs, rhs);
        let ctxt = rrule_to_ctxt_st_rule(&rule).unwrap();
        assert!(!ctxt.rhs.positions.is_empty());
    }
}
