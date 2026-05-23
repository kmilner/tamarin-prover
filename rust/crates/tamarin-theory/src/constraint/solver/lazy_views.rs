//! HS-faithful lazy state views — Phase 2 of the Disj-monad rewrite.
//!
//! ## Background
//!
//! HS's `Reduction` monad reads from `sNodes`, `sEdges`, etc. via
//! `gets`/`getM`.  These return the map *as currently stored* without
//! auto-applying the eq-store substitution.  HS applies the eq-store
//! substitution at three points:
//!   1. When passing terms to Maude for AC unification — Maude
//!      substitutes during the unif.
//!   2. When the caller explicitly invokes `apply substEqStore x` or
//!      `applyEqStore`.
//!   3. At post-processing time (e.g. `simplifySystem` calls
//!      `substSystem` between CR-rule passes).
//!
//! Rust currently calls `subst_system_once` eagerly after almost every
//! state-mutating operation, rewriting the contents of `sys.nodes`,
//! `sys.edges`, etc. in place.  This collapses HS's "raw vs. subst'd"
//! distinction — *every* read returns post-subst data.
//!
//! Per Phase 1 catalog (255 read sites surveyed), the simplify-pass
//! uniqueness rules (DG4, N5↓, N5_u) read `getM sNodes` raw in HS but
//! receive post-subst nodes in Rust.  This is the smoking gun for the
//! 2x chain_extend count gap on TLS.
//!
//! ## What these helpers do
//!
//! These pure helpers offer an explicit, two-flavoured API for every
//! state field a consumer needs:
//!
//! - `*_raw` — returns the data **as currently stored** in `sys`.  In
//!   today's Rust this is post-subst (because `subst_system_once`
//!   already ran); once Phase 2c removes that eager pass, it will be
//!   genuinely raw.
//! - `*_subst` — applies the **current** `sys.eq_store.subst` to the
//!   raw data on read.  HS-faithful for paths that expect the eq-store
//!   subst to be visible (post-`solveTermEqs` consumers).
//!
//! Migration sequence (incremental):
//! 1. **Phase 2a (this commit)** — Add helpers.  Behavior-identical:
//!    `*_raw` returns post-subst because `sys.nodes` is post-subst.
//! 2. **Phase 2b** — Migrate Phase 1's flagged consumers (simplify
//!    uniqueness passes etc.) to call `*_raw` instead of accessing
//!    `sys.nodes` directly.  Still behavior-identical.
//! 3. **Phase 2c** — Disable `subst_system_once`'s rule-fact rewriting.
//!    `*_raw` now genuinely returns raw data, `*_subst` does the
//!    substitution work the eager pass used to do.  Verdicts change;
//!    test + iterate.
//!
//! Skipping the migration step (2b) and going straight to 2c is what
//! the `TAM_RS_NO_NODE_FACT_SUBST=1` research flag does today — it
//! breaks TLS because consumers expect post-subst.  These helpers are
//! the bridge.
//!
//! ## API surface
//!
//! Functions take `&System` and `&Subst` so they're callable from
//! anywhere holding a reference.  Methods on `Reduction` are also
//! provided for the common ergonomic case (`self.node_conc_fact_raw(c)`).

use crate::constraint::constraints::{NodeConc, NodeId, NodePrem};
use crate::constraint::system::System;
use crate::fact::LNFact;
use crate::rule::RuleACInst;
use tamarin_term::lterm::{HasFrees, LNTerm, LVar, Name};
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

/// `gets $ M.lookup i sNodes` — raw rule lookup, no subst applied.
///
/// HS-faithful read of `sNodes`.  Mirrors HS `Theory.Constraint.System.nodeRule`:
/// ```haskell
/// nodeRule i = M.findWithDefault (error ...) i . get sNodes
/// ```
/// HS does NOT auto-apply the eq-store substitution; whatever was last
/// written to sNodes is what comes back.
///
/// **Today** this returns whatever's currently in `sys.nodes`, which
/// includes any subst eagerly applied by `subst_system_once`.  Once
/// Phase 2c lands, this will return truly raw data.
pub fn node_rule_raw<'a>(sys: &'a System, i: &NodeId) -> Option<&'a RuleACInst> {
    sys.nodes.iter().find(|(id, _)| id == i).map(|(_, r)| r)
}

/// Like [`node_rule_raw`] but applies the **current** eq-store
/// substitution lazily.  HS-equivalent: read sNodes then explicitly
/// `apply substEqStore` to each fact (rare in HS code; usually Maude
/// does this implicitly during unification).
///
/// Use this when the caller would otherwise have called
/// `subst_system()` before reading — switching to this helper defers
/// the subst to read-time, which is HS-faithful and lets us drop the
/// eager pass.
pub fn node_rule_subst(sys: &System, i: &NodeId) -> Option<RuleACInst> {
    node_rule_raw(sys, i).map(|r| subst_rule(r, &sys.eq_store.subst))
}

/// `gets $ nodeConcFact c` — raw conclusion fact at chain conc `c`.
/// HS-faithful: returns whatever's stored in `sNodes ! c.0`, indexed
/// by `c.1`.  No subst applied.
pub fn node_conc_fact_raw<'a>(sys: &'a System, c: &NodeConc) -> Option<&'a LNFact> {
    node_rule_raw(sys, &c.0).and_then(|r| r.conclusions.get(c.1.0))
}

/// Like [`node_conc_fact_raw`] but with lazy eq-store subst applied.
/// HS-equivalent: `apply substEqStore <$> nodeConcFact c`.
pub fn node_conc_fact_subst(sys: &System, c: &NodeConc) -> Option<LNFact> {
    node_conc_fact_raw(sys, c).map(|fa| subst_fact(fa, &sys.eq_store.subst))
}

/// `gets $ nodePremFact p` — raw premise fact.
pub fn node_prem_fact_raw<'a>(sys: &'a System, p: &NodePrem) -> Option<&'a LNFact> {
    node_rule_raw(sys, &p.0).and_then(|r| r.premises.get(p.1.0))
}

/// Like [`node_prem_fact_raw`] but with lazy eq-store subst applied.
pub fn node_prem_fact_subst(sys: &System, p: &NodePrem) -> Option<LNFact> {
    node_prem_fact_raw(sys, p).map(|fa| subst_fact(fa, &sys.eq_store.subst))
}

// -- Internal helpers --------------------------------------------------

/// Apply a subst to a single fact's terms.  Mirrors the
/// `apply_to_fact` closure inside `subst_system_once`.
fn subst_fact(fa: &LNFact, subst: &Subst<Name, LVar>) -> LNFact {
    LNFact {
        tag: fa.tag.clone(),
        annotations: fa.annotations.clone(),
        terms: fa.terms.iter().map(|t| apply_vterm(subst, t.clone())).collect(),
    }
}

/// Apply a subst to a rule's facts (premises, conclusions, actions)
/// plus its new_vars.  Mirrors the inner block of `subst_system_once`.
fn subst_rule(rule: &RuleACInst, subst: &Subst<Name, LVar>) -> RuleACInst {
    let map_var = |v: LVar| -> LVar {
        let id_term: LNTerm = Term::Lit(Lit::Var(v.clone()));
        match apply_vterm(subst, id_term) {
            Term::Lit(Lit::Var(w)) => w,
            _ => v,
        }
    };
    let new_rule = rule.clone().map_free(&mut |v| map_var(v));
    crate::rule::Rule {
        info: new_rule.info,
        premises: new_rule.premises.iter().map(|f| subst_fact(f, subst)).collect(),
        conclusions: new_rule.conclusions.iter().map(|f| subst_fact(f, subst)).collect(),
        actions: new_rule.actions.iter().map(|f| subst_fact(f, subst)).collect(),
        new_vars: new_rule.new_vars.iter()
            .map(|t| apply_vterm(subst, t.clone()))
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::system::System;
    use crate::rule::{ConcIdx, PremIdx};
    use crate::fact::{kd_fact, ku_fact};
    use crate::rule::{IntrRuleACInfo, Rule, RuleInfo};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    fn mk_lvar(name: &str, idx: u64, sort: LSort) -> LVar {
        LVar::new(name.to_string(), sort, idx)
    }

    fn mk_msg_var(name: &str, idx: u64) -> LNTerm {
        Term::Lit(Lit::Var(mk_lvar(name, idx, LSort::Msg)))
    }

    fn mk_destr_rule() -> RuleACInst {
        // A minimal destructor-like rule with one KD prem and one KU prem.
        Rule::new(
            RuleInfo::Intr(IntrRuleACInfo::DestrRule(
                b"_0_sdec".to_vec(),
                -1,
                true,
                false,
            )),
            vec![kd_fact(mk_msg_var("m", 1)), ku_fact(mk_msg_var("k", 2))],
            vec![kd_fact(mk_msg_var("out", 3))],
            vec![],
        )
    }

    #[test]
    fn node_rule_raw_returns_stored_rule() {
        let mut sys = System::default();
        let i = mk_lvar("i", 0, LSort::Node);
        let rule = mk_destr_rule();
        sys.add_node(i.clone(), rule.clone());
        assert_eq!(node_rule_raw(&sys, &i), Some(&rule));
    }

    #[test]
    fn node_rule_raw_misses_unknown_node() {
        let sys = System::default();
        let i = mk_lvar("i", 0, LSort::Node);
        assert_eq!(node_rule_raw(&sys, &i), None);
    }

    #[test]
    fn node_conc_fact_raw_returns_indexed_conclusion() {
        let mut sys = System::default();
        let i = mk_lvar("i", 0, LSort::Node);
        let rule = mk_destr_rule();
        sys.add_node(i.clone(), rule);
        let c = (i, ConcIdx(0));
        let fa = node_conc_fact_raw(&sys, &c).expect("conc fact");
        assert_eq!(fa.terms[0], mk_msg_var("out", 3));
    }

    #[test]
    fn node_prem_fact_raw_returns_indexed_premise() {
        let mut sys = System::default();
        let i = mk_lvar("i", 0, LSort::Node);
        let rule = mk_destr_rule();
        sys.add_node(i.clone(), rule);
        let p = (i, PremIdx(1));
        let fa = node_prem_fact_raw(&sys, &p).expect("prem fact");
        assert_eq!(fa.terms[0], mk_msg_var("k", 2));
    }

    #[test]
    fn node_rule_subst_with_empty_subst_equals_raw() {
        let mut sys = System::default();
        let i = mk_lvar("i", 0, LSort::Node);
        let rule = mk_destr_rule();
        sys.add_node(i.clone(), rule.clone());
        let subst_view = node_rule_subst(&sys, &i).expect("rule");
        assert_eq!(&subst_view, &rule);
    }

    #[test]
    fn node_rule_subst_rewrites_vars() {
        // Bind `m:Msg.1 → ~n:Fresh.10`.  After subst the rule's KD prem
        // should reference ~n:Fresh.10 instead of m:Msg.1.
        let mut sys = System::default();
        let i = mk_lvar("i", 0, LSort::Node);
        let rule = mk_destr_rule();
        sys.add_node(i.clone(), rule);
        let m1 = mk_lvar("m", 1, LSort::Msg);
        let n10 = Term::Lit(Lit::Var(mk_lvar("n", 10, LSort::Fresh)));
        sys.eq_store.subst = Subst::from_list(vec![(m1, n10.clone())]);
        let r = node_rule_subst(&sys, &i).expect("rule");
        assert_eq!(r.premises[0].terms[0], n10);
        // The KU prem (k:Msg.2) shouldn't change.
        assert_eq!(r.premises[1].terms[0], mk_msg_var("k", 2));
    }

    #[test]
    fn node_conc_fact_subst_applies_subst_to_term() {
        let mut sys = System::default();
        let i = mk_lvar("i", 0, LSort::Node);
        let rule = mk_destr_rule();
        sys.add_node(i.clone(), rule);
        let out3 = mk_lvar("out", 3, LSort::Msg);
        let bound = mk_msg_var("bound", 100);
        sys.eq_store.subst = Subst::from_list(vec![(out3, bound.clone())]);
        let c = (i, ConcIdx(0));
        let fa = node_conc_fact_subst(&sys, &c).expect("conc fact");
        assert_eq!(fa.terms[0], bound);
    }
}
