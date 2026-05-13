//! Port of `Theory.Constraint.Solver.ProofMethod`.
//!
//! `ProofMethod` is the small-step interface to the constraint
//! solver. The high-level loop in Haskell is:
//!
//! ```text
//! exec(method, sys) -> Map<CaseName, System>
//!     - Sorry / Finished / Invalidated → trivial
//!     - Simplify  → simplify the system once
//!     - SolveGoal → reduce a specific open goal, possibly producing
//!                   multiple cases
//!     - Induction → split into base/step cases
//! ```
//!
//! The Rust port currently implements the trivial cases and stubs
//! the non-trivial ones with `unimplemented!()`-equivalent results
//! (returns `None` / empty map). The shape is in place so the rest
//! can grow incrementally.

use std::collections::BTreeMap;

use crate::constraint::constraints::Goal;
use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::contradictions::{contradictions, Contradiction};
use crate::constraint::system::System;

/// Each case in a proof tree gets a unique name.
pub type CaseName = String;

/// Outcome of a finished proof method.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Result {
    /// A dependency graph was found that satisfies the system.
    Solved,
    /// A contradiction could be derived.
    Contradictory(Option<Contradiction>),
    /// The proof can't be finished — typically because of reducible
    /// operators in subterms or a solution after weakening.
    Unfinishable,
}

/// One small-step transformation of a sequent.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofMethod {
    Sorry(Option<String>),
    Simplify,
    SolveGoal(Goal),
    Induction,
    Finished(Result),
    Invalidated,
}

/// `isFinished`: returns the appropriate `Result` if the system is in
/// a terminal state — solved, contradictory, or unfinishable.
pub fn is_finished(ctx: &ProofContext, sys: &System) -> Option<Result> {
    if is_initial_system(sys) { return None; }
    let cs = contradictions(ctx, sys);
    if let Some(c) = cs.into_iter().next() {
        // Convert spurious Cyclic / FormulasFalse arising from
        // Fresh-consumer conflation to Unfinishable.  Fresh values
        // are linear (can be consumed by exactly one node), so two
        // distinct non-AC-unifiable nodes sharing the same Fresh
        // value is impossible — the branch IS contradictory.  BUT:
        // when this state arises via our graft pipeline (instead of
        // via legitimate search), other valid branches (the actual
        // attack trace) may be missed, and rolling up to all-
        // Contradictory wrongly yields Verified for an all-traces
        // lemma OR wrongly Falsified for an exists-trace lemma.
        // Returning Unfinishable preserves soundness — the parent
        // rolls up as Sorry-equivalent.
        //
        // FormulasFalse on a Fresh-conflated system typically comes
        // from `subst_system`'s shape-mismatch fast-path pushing
        // gfalse (Reduction.hs:213): two rule instances collapse to
        // one node id but their fact lists disagree.  Same Maude-
        // witness conflation root cause as Cyclic + Fresh-consumer.
        use crate::constraint::solver::contradictions::Contradiction;
        // Cyclic / FormulasFalse arising from Fresh-consumer
        // conflation: Unfinishable, not Contradictory.
        let is_conflation_grade = matches!(c,
            Contradiction::Cyclic | Contradiction::FormulasFalse);
        if is_conflation_grade && has_fresh_consumer_conflation_at(ctx, sys) {
            return Some(Result::Unfinishable);
        }
        // Duplicate-protocol-instance pattern: when the system has
        // multiple instances of the same Standalone proto rule (e.g.
        // two `responder` nodes), and a contradiction surfaces in the
        // eq-store, the root cause is almost always our
        // graft-pipeline's missing `conjoinSystem`/`setNodes`
        // collision semantics (Haskell merges these instances
        // cleanly via `solveRuleEqs`; our pipeline collapses them
        // through `enforce_edge_uniqueness` → eq-store
        // over-constraint → `IncompatibleEqs`/`Cyclic`).  Converting
        // such contradictions to `Unfinishable` keeps the verdict
        // sound (Sorry/Unfinishable is incomparable, never
        // wrong-Falsified) — at the cost of leaving lemmas that
        // depend on the duplicate-instance graft pattern as Sorry
        // rather than Verified.  Without the conversion,
        // `CR.spthy::executable` wrong-falsifies (ours=falsified,
        // tamarin=verified) under DFS chain-closure.
        //
        // See `project_rust_ku_fresh_responder_gap.md`.
        let is_eq_contradiction = matches!(c,
            Contradiction::IncompatibleEqs);
        if is_eq_contradiction && has_duplicate_proto_instances(sys) {
            return Some(Result::Unfinishable);
        }
        // FormulasFalse from `subst_system` shape-mismatch: Maude-
        // witness conflation collapsing distinct rule instances onto
        // the same node id.  Tagged by `subst_system` directly so we
        // don't need to recover the pattern from sys structure.
        if matches!(c, Contradiction::FormulasFalse)
            && sys.shape_mismatch_conflation
        {
            return Some(Result::Unfinishable);
        }
        return Some(Result::Contradictory(Some(c)));
    }
    if std::env::var("TAM_DBG_IMPL").is_ok() {
        let has_i_1 = sys.nodes.iter().any(|(_, r)|
            matches!(&r.info, crate::rule::RuleInfo::Proto(p)
                if matches!(&p.name, crate::rule::ProtoRuleName::Stand(s) if s == "I_1")));
        let has_r_1 = sys.nodes.iter().any(|(_, r)|
            matches!(&r.info, crate::rule::RuleInfo::Proto(p)
                if matches!(&p.name, crate::rule::ProtoRuleName::Stand(s) if s == "R_1")));
        if has_i_1 && has_r_1 {
            let has_bot = sys.formulas.iter()
                .any(|f| matches!(f, crate::guarded::Guarded::Disj(v) if v.is_empty()));
            eprintln!("[is_finished] HAS I_1+R_1: formulas.len={} has_bot={} nodes={}",
                sys.formulas.len(), has_bot, sys.nodes.len());
        }
    }
    // A system with all goals already marked solved is also "no
    // remaining open goals" — Haskell's `openGoals` filter does the
    // same thing. Formulas remain in `sFormulas` as sentinels (e.g.
    // a Disj whose case-split goal has been chosen still lives on),
    // so we don't require an empty `formulas` list — only that no
    // formula is `gfalse` (which would be a contradiction).
    let no_open_goals = sys.goals.iter().all(|(_, st)| st.solved);
    let bot = crate::guarded::gfalse();
    let no_false_formula = !sys.formulas.contains(&bot);
    let sub_finished = finished_subterms(sys);
    if no_open_goals && no_false_formula && sub_finished { Some(Result::Solved) }
    else if no_open_goals && no_false_formula && !sub_finished { Some(Result::Unfinishable) }
    else { None }
}

/// Returns true if `sys` has two or more nodes whose rules are
/// instances of the same Standalone protocol rule.  This pattern
/// arises when a source-case graft creates a duplicate protocol-rule
/// instance — Haskell merges these via `conjoinSystem`'s setNodes
/// collision semantics; our pipeline does not, so the merge cascade
/// through `enforce_fresh_node_uniqueness` + `enforce_edge_uniqueness`
/// can over-constrain the eq-store.
fn has_duplicate_proto_instances(sys: &System) -> bool {
    use std::collections::BTreeSet;
    let mut seen: BTreeSet<String> = BTreeSet::new();
    for (_, rule) in &sys.nodes {
        if let crate::rule::RuleInfo::Proto(p) = &rule.info {
            if let crate::rule::ProtoRuleName::Stand(s) = &p.name {
                if !seen.insert(s.clone()) {
                    return true;
                }
            }
        }
    }
    false
}

/// Returns true if `sys` has two distinct non-AC-unifiable nodes that
/// both consume the same Fresh value as their `Fr(~x)` premise.  See
/// `reduction::has_fresh_consumer_conflation`; this is the proof-method
/// layer's wrapper that uses the proof context to access Maude.
fn has_fresh_consumer_conflation_at(ctx: &ProofContext, sys: &System) -> bool {
    use crate::fact::FactTag;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let subst = sys.eq_store.subst.clone();
    let mut consumers: Vec<(crate::constraint::constraints::NodeId, LVar)> = Vec::new();
    for (id, rule) in &sys.nodes {
        for prem in &rule.premises {
            if !matches!(prem.tag, FactTag::Fresh) { continue; }
            let t = match prem.terms.first() { Some(t) => t, None => continue };
            let t_norm = tamarin_term::subst::apply_vterm(&subst, t.clone());
            if let Term::Lit(Lit::Var(v)) = t_norm {
                if v.sort == LSort::Fresh {
                    consumers.push((id.clone(), v));
                }
            }
        }
    }
    for i in 0..consumers.len() {
        for j in (i + 1)..consumers.len() {
            if consumers[i].1 != consumers[j].1 { continue; }
            if consumers[i].0 == consumers[j].0 { continue; }
            let ri = sys.nodes.iter().find(|(n, _)| n == &consumers[i].0).map(|(_, r)| r);
            let rj = sys.nodes.iter().find(|(n, _)| n == &consumers[j].0).map(|(_, r)| r);
            let (Some(ri), Some(rj)) = (ri, rj) else { continue };
            match crate::rule::unifiable_rule_ac_insts(&ctx.maude, ri, rj) {
                Ok(true) => continue,
                Ok(false) => return true,
                Err(_) => continue,
            }
        }
    }
    false
}

/// Approximation of Haskell's `isInitialSystem`:
///   `null sSolvedFormulas && not (bot ∈ sFormulas)`
///
/// We add the structural-emptiness checks too, since our `System`
/// carries more state than Haskell's at this stage. The crucial
/// property is the `not bot in formulas` clause — a system whose
/// open formulas contain ⊥ is *contradictory*, not initial.
fn is_initial_system(sys: &System) -> bool {
    let bot = crate::guarded::gfalse();
    sys.nodes.is_empty()
        && sys.edges.is_empty()
        && sys.less_atoms.is_empty()
        && sys.solved_formulas.is_empty()
        && sys.goals.is_empty()
        && !sys.formulas.contains(&bot)
}

/// True if every subterm constraint has been resolved (or no subterm
/// constraints exist). Mirrors Haskell's `finishedSubterms` modulo
/// the propagation step we haven't ported.
fn finished_subterms(sys: &System) -> bool {
    sys.subterm_store.subterms.iter().all(|s| s.propagated)
}

/// Execute a proof method against `sys`, returning the resulting
/// case map. `Sorry` / `Finished` produce empty cases; `Simplify`
/// runs `simplify_system` and returns one case; `SolveGoal(g)`
/// dispatches via `solve_*_goal` and converts `GoalCases` to a case
/// map. `Induction` is left as a stub.
pub fn exec_proof_method(
    ctx: &ProofContext,
    method: &ProofMethod,
    sys: &System,
) -> Option<BTreeMap<CaseName, System>> {
    use crate::constraint::solver::reduction::{ChangeIndicator, GoalCases, Reduction};
    use crate::constraint::solver::simplify::simplify_system;

    match method {
        ProofMethod::Sorry(_) | ProofMethod::Finished(_) => Some(BTreeMap::new()),
        ProofMethod::Invalidated => None,
        ProofMethod::Simplify => {
            let mut r = Reduction::new(ctx, sys.clone());
            r.changed = ChangeIndicator::Unchanged;
            simplify_system(&mut r);
            // Match Haskell's guard: if `Simplify` produced an
            // identical system, it failed — return None so the
            // search picks something else (or marks Sorry).
            if r.sys == *sys { return None; }
            let mut out = BTreeMap::new();
            out.insert("".to_string(), r.sys);
            Some(out)
        }
        ProofMethod::SolveGoal(g) => {
            let mut r = Reduction::new(ctx, sys.clone());
            let outcome = crate::constraint::solver::goals::dispatch_solve_goal(&mut r, g);
            // Run simplify after every goal-solving step — mirrors
            // Haskell's `m <* simplifySystem` pattern in `process`.
            let simplify = |sys: System| -> System {
                let mut r = Reduction::new(ctx, sys);
                simplify_system(&mut r);
                r.sys
            };
            match outcome {
                GoalCases::Linear => {
                    let mut out = BTreeMap::new();
                    out.insert("".to_string(), simplify(r.sys));
                    Some(out)
                }
                GoalCases::LinearNamed(name) => {
                    let mut out = BTreeMap::new();
                    out.insert(name, simplify(r.sys));
                    Some(out)
                }
                GoalCases::Cases(cases) => {
                    let mut out = BTreeMap::new();
                    // De-duplicate identical case names by appending
                    // `_case_1`/`_case_2`/... — mirrors Haskell's
                    // `groupSortOn casName` printing convention
                    // (e.g. `R_1_case_1`, `R_1_case_2` for two
                    // distinct unifications against rule `R_1`).
                    use std::collections::HashMap;
                    let mut counts: HashMap<String, usize> = HashMap::new();
                    for (name, _) in &cases {
                        *counts.entry(name.clone()).or_default() += 1;
                    }
                    let mut seen: HashMap<String, usize> = HashMap::new();
                    for (name, sys) in cases.into_iter() {
                        let total = counts[&name];
                        let key = if total > 1 {
                            let n = seen.entry(name.clone()).or_default();
                            *n += 1;
                            format!("{}_case_{}", name, *n)
                        } else {
                            name
                        };
                        out.insert(key, simplify(sys));
                    }
                    Some(out)
                }
                GoalCases::Contradictory => Some(BTreeMap::new()),
            }
        }
        ProofMethod::Induction => {
            use crate::constraint::solver::reduction::Reduction;
            use crate::constraint::solver::simplify::simplify_system;
            // Take the first formula and try `ginduct`.
            let fm = match sys.formulas.first() {
                Some(f) => f.clone(),
                None => return None,
            };
            let (base, step) = match crate::guarded::ginduct(&fm) {
                Ok(p) => p,
                Err(_) => return None,
            };
            // Build each case, then immediately simplify — mirrors
            // Haskell's `process . induction` which threads
            // `simplifySystem` through the resulting reduction.
            // Mirror Haskell's exec for Induction: REMOVE formulas[0]
            // (the original lemma formula) and route the new base /
            // step through `insertFormula`'s structural decomposition.
            // `Conj([])` (= gtrue) is marked solved by insertFormula's
            // GConj arm, which lands it in `solved_formulas` and makes
            // `isInitialSystem` return false on the empty-trace child.
            // Without this routing, our direct `formulas[0] = base;`
            // replacement leaves both formulas and solved_formulas
            // empty, so the child looks like a fresh initial system
            // and search refuses to mark it Solved.
            let mut base_sys = sys.clone();
            base_sys.formulas.remove(0);
            let mut br = Reduction::new(ctx, base_sys);
            br.insert_formula_decompose(base);
            simplify_system(&mut br);

            let mut step_sys = sys.clone();
            step_sys.formulas.remove(0);
            let mut sr = Reduction::new(ctx, step_sys);
            sr.insert_formula_decompose(step);
            simplify_system(&mut sr);

            let mut out = BTreeMap::new();
            out.insert("empty_trace".to_string(), br.sys);
            out.insert("non_empty_trace".to_string(), sr.sys);
            Some(out)
        }
    }
}

/// `checkAndExecProofMethod`: structurally validates the method
/// against `sys` before delegating to `exec_proof_method`. Mirrors
/// Haskell's pre-conditions:
///
/// - `Finished r` → `is_finished` must return a result with the same
///   reason kind.
/// - `Induction` → only valid on a fresh system with a single formula.
/// - `SolveGoal g` → `g` must be in `sys.goals`.
/// - `Simplify` / `Sorry` → always valid.
pub fn check_and_exec_proof_method(
    ctx: &ProofContext,
    method: &ProofMethod,
    sys: &System,
) -> Option<BTreeMap<CaseName, System>> {
    match method {
        ProofMethod::Finished(r) => {
            let actual = is_finished(ctx, sys)?;
            if !same_kind(r, &actual) { return None; }
        }
        ProofMethod::Induction => {
            if !is_initial_system(sys) { return None; }
            if sys.solved_formulas.len() != 0 { return None; }
            if sys.formulas.len() != 1 { return None; }
        }
        ProofMethod::SolveGoal(g) => {
            if !sys.goals.iter().any(|(existing, _)| existing == g) { return None; }
        }
        ProofMethod::Simplify | ProofMethod::Sorry(_) | ProofMethod::Invalidated => {}
    }
    exec_proof_method(ctx, method, sys)
}

fn same_kind(a: &Result, b: &Result) -> bool {
    match (a, b) {
        (Result::Solved, Result::Solved) => true,
        (Result::Unfinishable, Result::Unfinishable) => true,
        (Result::Contradictory(_), Result::Contradictory(_)) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_sig::pair_maude_sig;

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        let candidates = [
            "/home/linuxbrew/.linuxbrew/bin/maude",
            "/usr/local/bin/maude",
            "maude",
        ];
        for c in &candidates {
            if std::path::Path::new(c).exists() { return Some((*c).to_string()); }
        }
        None
    }

    fn ctx() -> Option<ProofContext> {
        let path = maude_path()?;
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).ok()?;
        Some(ProofContext::new(h, Vec::new()))
    }

    #[test]
    fn empty_system_is_not_finished() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let s = System::empty();
        assert!(is_finished(&ctx, &s).is_none(), "initial system shouldn't be finished");
    }

    #[test]
    fn solved_when_no_goals_and_subterms_done() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut s = System::empty();
        // Force the system out of its initial state by adding a node
        // (so is_initial_system returns false).
        let nid = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
        // Use the Fresh built-in rule shape — but for the test all we
        // need is that nodes/edges/less is non-empty.
        // We push an empty-rule-instance directly via the type's
        // constructor.
        use crate::rule::{
            IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes,
            RuleInfo, RuleACInst, Rule,
        };
        let info: RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo> =
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Test".into()),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            });
        let rule: RuleACInst = Rule::new(info, Vec::new(), Vec::new(), Vec::new());
        s.add_node(nid, rule);
        match is_finished(&ctx, &s) {
            Some(Result::Solved) => {}
            r => panic!("expected Solved, got {:?}", r),
        }
    }

    #[test]
    fn exec_sorry_is_empty_cases() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let s = System::empty();
        let cases = exec_proof_method(&ctx, &ProofMethod::Sorry(None), &s).unwrap();
        assert!(cases.is_empty());
    }

    #[test]
    fn induction_on_open_formula_returns_none() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let s = System::empty();
        // No formula → ginduct can't run.
        let r = exec_proof_method(&ctx, &ProofMethod::Induction, &s);
        assert!(r.is_none());
    }

    #[test]
    fn induction_creates_two_cases() {
        let ctx = match ctx() { Some(c) => c, None => return };
        // Build a closed action-bearing formula:
        //   Ex k #i. Setup(k) @ #i
        // tracked as a guarded GGuarded::Ex with a single Action guard.
        use tamarin_parser::ast::{Atom, Fact, SortHint, Term, VarSpec};
        let mkvar = |n: &str, sort: SortHint| Term::Var(VarSpec {
            name: n.to_string(), idx: 0, sort, typ: None,
        });
        let action_atom = Atom::Action(
            Fact {
                persistent: false,
                annotations: Vec::new(),
                name: "Setup".into(),
                args: vec![mkvar("k", SortHint::Msg)],
            },
            mkvar("i", SortHint::Node),
        );
        let body = crate::guarded::Guarded::Conj(Vec::new());
        let fm = crate::guarded::Guarded::GGuarded {
            qua: crate::guarded::Quant::Ex,
            vars: vec![
                VarSpec { name: "k".into(), idx: 0, sort: SortHint::Msg, typ: None },
                VarSpec { name: "i".into(), idx: 0, sort: SortHint::Node, typ: None },
            ],
            guards: vec![action_atom],
            body: Box::new(body),
        };
        let mut s = System::empty();
        s.formulas.push(fm);
        let r = exec_proof_method(&ctx, &ProofMethod::Induction, &s).expect("induction");
        // Two case names: empty_trace and non_empty_trace.
        assert_eq!(r.len(), 2);
        assert!(r.contains_key("empty_trace"));
        assert!(r.contains_key("non_empty_trace"));
    }

    #[test]
    fn check_solve_goal_rejects_unknown() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let s = System::empty();
        // Goal not in sys.goals → check should fail.
        let v = tamarin_term::lterm::LVar::new("k", tamarin_term::lterm::LSort::Msg, 0);
        let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        let g = Goal::Action(v, f);
        let r = check_and_exec_proof_method(&ctx, &ProofMethod::SolveGoal(g), &s);
        assert!(r.is_none());
    }
}
