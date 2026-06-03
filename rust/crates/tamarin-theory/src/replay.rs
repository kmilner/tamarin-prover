//! Skeleton-replay prover — port of HS `replaceSorryProver`
//! (lib/theory/src/Theory/Proof.hs:644-652).
//!
//! HS's `--prove` flag wires `replaceSorryProver $ runAutoProver`
//! (TheoryLoader.hs:606) so the auto-prover runs **only at `by sorry`
//! leaves of the user-written skeleton**, not from scratch.  This
//! preserves the case-decomposition structure the user wrote in the
//! `.spthy` file even when the auto-prover would have picked a
//! different (still-sound) decomposition.
//!
//! ## HS reference (Theory/Proof.hs:644-652)
//!
//! ```haskell
//! -- | Replace all annotated sorry steps using the given prover.
//! replaceSorryProver :: Prover -> Prover
//! replaceSorryProver prover0 = Prover prover
//!   where
//!     prover ctxt d _ = return . replace
//!       where
//!         replace prf@(LNode (ProofStep (Sorry _) (Just se)) _) =
//!             fromMaybe prf $ runProver prover0 ctxt d se prf
//!         replace (LNode ps cases) =
//!             LNode ps $ M.map replace cases
//! ```
//!
//! HS recurses through the static skeleton tree; at each Sorry leaf
//! that carries a `Just se` annotation (System state), the auto-prover
//! `prover0` is invoked.  Non-sorry nodes have their `ProofMethod`
//! executed via `oneStepProver` (Proof.hs:583-587) which calls
//! `execProofMethod ctxt method se`, then recurses into the
//! resulting case-map.
//!
//! ## Replay strategy in this port
//!
//! We diverge slightly from HS's structure: HS first annotates the
//! parsed skeleton with `(Just System)` at each node via
//! `unprovenLookAhead`, then replaces Sorrys.  We do it in one pass —
//! at every non-Sorry node we exec the proof method, get the case
//! list, and recurse into each.  At Sorry leaves and at unmatched-case
//! children we fall through to [`run_proof_search`].
//!
//! This matches HS's end result for any skeleton whose
//! `exec_proof_method`-produced case names match the skeleton's
//! child names — which is the normal case, since HS produced those
//! names in the first place.  When names diverge (e.g. a case the
//! user's skeleton has but our prover's `exec_proof_method` doesn't
//! produce, or vice versa), we conservatively fall back to the
//! auto-prover at that subtree.

use std::collections::BTreeMap;

use tamarin_parser::ast::{GoalSpec, ParsedMethod, ParsedProofTree};

use crate::constraint::constraints::Goal;
use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::proof_method::{
    exec_proof_method, is_finished, ProofMethod, Result as MethodResult,
};
use crate::constraint::solver::search::{run_proof_search, NodeStatus, ProofNode};
use crate::constraint::system::System;
use crate::fact::{fact_tag_name, FactTag, Multiplicity};

/// Drive a single lemma's skeleton.  Equivalent of HS
/// `runProver (replaceSorryProver (runAutoProver autoProver)) ctxt 0
///  initial sysOnTree` (Proof.hs:644-652).
///
/// `max_steps` is plumbed through to `run_proof_search` for the
/// fall-through auto-prover invocations.
pub fn replace_sorry_prove(
    ctx: &ProofContext,
    initial: System,
    skeleton: &ParsedProofTree,
    max_steps: usize,
) -> ProofNode {
    replay_node(ctx, initial, skeleton, max_steps)
}

/// Replay one node of the skeleton against `sys`.
fn replay_node(
    ctx: &ProofContext,
    sys: System,
    node: &ParsedProofTree,
    max_steps: usize,
) -> ProofNode {
    // ---- Leaf cases first (HS `replace prf@(... Sorry ...)`). ----
    // `by sorry` leaf → invoke the auto-prover on `sys`.  HS:
    //   replace prf@(LNode (ProofStep (Sorry _) (Just se)) _) =
    //       fromMaybe prf $ runProver prover0 ctxt d se prf
    if matches!(node.method, ParsedMethod::Sorry) && node.cases.is_empty() {
        return run_proof_search(ctx, sys, max_steps);
    }

    // `by contradiction` leaf → emit a Finished(Contradictory) node if
    // a contradiction can actually be derived; else fall back to the
    // auto-prover (HS would have left a `Sorry` here at proof-display
    // time, but at proof-replay time HS runs `oneStepProver
    // (Finished (Contradictory Nothing))` which fails if no
    // contradiction exists — and `replaceSorryProver` falls through
    // to the original Sorry).  We diverge slightly: rather than emit
    // a useless Sorry, we re-run the auto-prover to give the user a
    // best-effort proof.  This is acceptable because:
    //   (a) `by contradiction` in the .spthy file means the user
    //       believed the system is contradictory at this point;
    //   (b) if our prover agrees, we emit the same Finished node;
    //   (c) if our prover doesn't (a faithfulness divergence
    //       elsewhere), the auto-prover will find a valid proof or
    //       Sorry — neither lies about the result.
    if matches!(node.method, ParsedMethod::Contradiction) && node.cases.is_empty() {
        if let Some(MethodResult::Contradictory(c)) = is_finished(ctx, &sys) {
            return ProofNode {
                method: ProofMethod::Finished(MethodResult::Contradictory(c)),
                sys,
                children: BTreeMap::new(),
                status: NodeStatus::Contradictory,
            };
        }
        // HS `oneStepProver (Finished (Contradictory Nothing))` would
        // fail here, leaving the original Sorry.  We surface that as
        // a `Sorry("contradiction expected but none found")` Sorry —
        // letting the user notice the divergence.
        return ProofNode {
            method: ProofMethod::Sorry(Some(
                "contradiction expected but none found".into(),
            )),
            sys,
            children: BTreeMap::new(),
            status: NodeStatus::Sorry,
        };
    }

    // `SOLVED` leaf (HS Proof.hs:102-103) → emit Finished(Solved) if
    // the system actually has no open goals; else mismatch + Sorry.
    if matches!(node.method, ParsedMethod::SolvedLeaf) && node.cases.is_empty() {
        if let Some(MethodResult::Solved) = is_finished(ctx, &sys) {
            return ProofNode {
                method: ProofMethod::Finished(MethodResult::Solved),
                sys,
                children: BTreeMap::new(),
                status: NodeStatus::Solved,
            };
        }
        // HS doesn't ship `SOLVED` annotations on unproven skeletons —
        // they appear only after a proof completes.  If the runtime
        // disagrees, the lemma has diverged elsewhere; report Sorry.
        return ProofNode {
            method: ProofMethod::Sorry(Some(
                "SOLVED leaf but runtime not solved".into(),
            )),
            sys,
            children: BTreeMap::new(),
            status: NodeStatus::Sorry,
        };
    }

    // `UNFINISHABLE` leaf — emit Finished(Unfinishable) if runtime
    // agrees, else Sorry.
    if matches!(node.method, ParsedMethod::Unfinishable) && node.cases.is_empty() {
        if let Some(MethodResult::Unfinishable) = is_finished(ctx, &sys) {
            return ProofNode {
                method: ProofMethod::Finished(MethodResult::Unfinishable),
                sys,
                children: BTreeMap::new(),
                status: NodeStatus::Unfinishable,
            };
        }
        return ProofNode {
            method: ProofMethod::Sorry(Some(
                "UNFINISHABLE leaf but runtime disagrees".into(),
            )),
            sys,
            children: BTreeMap::new(),
            status: NodeStatus::Sorry,
        };
    }

    // ---- Non-leaf nodes: pick a method, exec it, recurse. ----
    // HS `oneStepProver`:
    //   cases <- execProofMethod ctxt method se
    //   return $ LNode (ProofStep method (Just se))
    //                  (M.map (unprovenLookAhead ctxt) cases)
    // then `replaceSorryProver` recurses on the children — but in
    // HS's setup the skeleton's children take precedence (they're
    // already there from the parse), and `unprovenLookAhead` produces
    // a Sorry that gets replaced by the auto-prover.
    let (method, cases) = match exec_method_for(&node.method, &sys, ctx, &node.cases) {
        Some(p) => p,
        None => {
            // Couldn't resolve OR the method didn't apply.  Fall back
            // to the auto-prover.  Honest faithfulness divergence.
            return run_proof_search(ctx, sys, max_steps);
        }
    };

    // Match the skeleton's child case-names against the cases
    // exec_proof_method produced.  If `cases` is empty (e.g.
    // contradictory closure), this is a leaf-equivalent.
    if cases.is_empty() {
        // Empty case-map after exec means contradictory closure —
        // mirror the regular search-path handling at search.rs:478-481.
        return ProofNode {
            method,
            sys,
            children: BTreeMap::new(),
            status: NodeStatus::Contradictory,
        };
    }

    // Build a map from case name → System for fast lookup.
    let produced: BTreeMap<String, System> =
        cases.into_iter().collect();

    let mut children: BTreeMap<String, ProofNode> = BTreeMap::new();
    let mut any_solved = false;
    let mut any_contra = false;
    let mut any_unfin = false;
    let mut any_sorry = false;

    // Walk the skeleton's child cases in source order.
    for (skel_name, sub_tree) in &node.cases {
        // Find the matching runtime case.  Two common shapes:
        //   - Skel case is "" (no name; from Simplify or single-case
        //     SolveGoal) → matches the single produced case.
        //   - Skel case has a name → matches by exact name.
        let runtime_name_opt: Option<String> = if skel_name.is_empty() {
            // Skeleton has an unnamed single-child block (Simplify
            // produces a "" case).
            if produced.len() == 1 {
                Some(produced.keys().next().unwrap().clone())
            } else {
                None
            }
        } else if produced.contains_key(skel_name) {
            Some(skel_name.clone())
        } else {
            None
        };
        let child_sys = match &runtime_name_opt {
            Some(n) => produced.get(n).cloned().unwrap(),
            None => {
                // No matching runtime case — the skeleton drifted from
                // the actual decomposition.  Fall back to auto-prover
                // for this subtree, but use a synthetic "skeleton
                // mismatch" Sorry leaf seeded with the parent system
                // so the user gets a visible signal.  Honest
                // divergence reporting; not a paper-over.
                let placeholder = ProofNode {
                    method: ProofMethod::Sorry(Some(format!(
                        "skeleton case `{}` not produced at replay",
                        skel_name
                    ))),
                    sys: sys.clone(),
                    children: BTreeMap::new(),
                    status: NodeStatus::Sorry,
                };
                children.insert(skel_name.clone(), placeholder);
                any_sorry = true;
                continue;
            }
        };
        let child_node = replay_node(ctx, child_sys, sub_tree, max_steps);
        match child_node.status {
            NodeStatus::Solved => any_solved = true,
            NodeStatus::Contradictory => any_contra = true,
            NodeStatus::Unfinishable => any_unfin = true,
            NodeStatus::Sorry => any_sorry = true,
            NodeStatus::Open => {}
        }
        // Use the actual runtime name (matches what HS' produced map
        // shows when rendering).
        let key = runtime_name_opt.unwrap_or_else(|| skel_name.clone());
        children.insert(key, child_node);
    }

    // For runtime cases NOT covered by the skeleton (e.g. skeleton was
    // stale and a new case appeared), invoke the auto-prover on each.
    // HS's `replaceSorryProver` doesn't have this branch because HS
    // parses the skeleton AFTER having built the tree-with-systems —
    // they always match by construction.  In our port the skeleton is
    // parsed from text BEFORE the runtime systems exist, so drift is
    // possible.  Honest fallback.
    let already_covered: std::collections::BTreeSet<String> =
        children.keys().cloned().collect();
    for (rt_name, rt_sys) in produced.into_iter() {
        if already_covered.contains(&rt_name) { continue; }
        // Also skip if the skeleton consumed this case via "".
        if node.cases.iter().any(|(s, _)| s.is_empty())
            && children.len() == 1
            && already_covered.iter().next().map(|s| s.as_str()) == Some(rt_name.as_str())
        {
            continue;
        }
        let auto = run_proof_search(ctx, rt_sys, max_steps);
        match auto.status {
            NodeStatus::Solved => any_solved = true,
            NodeStatus::Contradictory => any_contra = true,
            NodeStatus::Unfinishable => any_unfin = true,
            NodeStatus::Sorry => any_sorry = true,
            NodeStatus::Open => {}
        }
        children.insert(rt_name, auto);
    }

    let status = if any_solved {
        NodeStatus::Solved
    } else if any_sorry {
        NodeStatus::Sorry
    } else if any_unfin {
        NodeStatus::Unfinishable
    } else if any_contra {
        NodeStatus::Contradictory
    } else {
        NodeStatus::Sorry
    };

    ProofNode { method, sys, children, status }
}

/// Resolve a parsed method against `sys` and produce a (method, cases)
/// pair if possible.  For `SolveGoal(GoalSpec::Raw(_))` (a `solve(...)`
/// in the skeleton whose inner formula we couldn't structurally parse,
/// e.g. a disjunction `(a) ∥ (b)` or a subterm `a ⊏ b`), we iterate
/// over the candidate ProofMethods in heuristic-ranked order (same
/// list `expand` in search.rs uses) and pick the first one whose
/// resulting case-set is compatible with the skeleton's child case
/// names.  This is the closest we can come to HS's behavior without a
/// full formula→Goal parser: HS parses the formula directly into a
/// Goal, but if our auto-prover would have picked the same goal in
/// that state, the case-decomposition matches.
fn exec_method_for(
    parsed: &ParsedMethod,
    sys: &System,
    ctx: &ProofContext,
    skel_children: &[(String, ParsedProofTree)],
) -> Option<(ProofMethod, Vec<(String, System)>)> {
    let dbg = std::env::var("TAM_DBG_REPLAY").is_ok();
    // Fast path: parsed method resolves directly.
    if let Some(method) = resolve_method(parsed, sys) {
        if let Some(cases) = exec_proof_method(ctx, &method, sys) {
            if dbg {
                let names: Vec<&str> = cases.iter().map(|(n, _)| n.as_str()).collect();
                eprintln!("[replay] direct {:?} → {} cases: {:?}",
                    method_kind(&method), cases.len(), names);
            }
            return Some((method, sort_cases(cases)));
        }
        if dbg { eprintln!("[replay] direct {:?} → exec returned None",
            method_kind(&method)); }
        return None;
    }
    // Slow path: SolveGoal(GoalSpec::Raw(_)) — iterate candidates and
    // pick the first SolveGoal whose case-set has at least one name in
    // common with the skeleton's child names.  This is HS-faithful in
    // spirit: HS parses the formula inside `solve(...)` directly to a
    // Goal value via `goal` (Theory/Text/Parser/Proof.hs:39-72) and
    // would always find the goal in `sys.goals`; we can't do that for
    // disjunction / subterm / split goals yet (see GoalSpec::Raw
    // doc-comment), so we approximate by trusting the heuristic
    // ranking — for the patterns we hit in the target lemmas, the
    // top-ranked goal IS the one HS parsed.
    if !matches!(parsed, ParsedMethod::SolveGoal(GoalSpec::Raw(_))) {
        return None;
    }
    let skel_names: Vec<&str> = skel_children.iter().map(|(s, _)| s.as_str()).collect();
    if dbg {
        let raw = match parsed {
            ParsedMethod::SolveGoal(GoalSpec::Raw(r)) =>
                r.chars().take(120).collect::<String>(),
            _ => String::new(),
        };
        eprintln!("[replay] raw-solve skel_names={:?} (raw text: {:?})", skel_names, raw);
    }
    let candidates = crate::constraint::solver::search::candidate_methods(sys, ctx);
    let mut tried = 0usize;
    // Cap candidate iteration to avoid pathological case-enumeration
    // explosion (each `exec_proof_method` for a SolveGoal can be
    // expensive — Maude calls, system clones, simplify loops).  64
    // candidates is generous; HS's first-match-wins ranking typically
    // hits at the top.
    const MAX_CANDIDATES: usize = 32;
    for m in candidates {
        if !matches!(m, ProofMethod::SolveGoal(_)) { continue; }
        tried += 1;
        if tried > MAX_CANDIDATES { break; }
        if let Some(cases) = exec_proof_method(ctx, &m, sys) {
            if dbg && tried <= 8 {
                let names: Vec<&str> = cases.iter().map(|(n, _)| n.as_str()).collect();
                eprintln!("[replay]   candidate#{} {:?} → {} cases {:?}",
                    tried, method_kind(&m), cases.len(), names);
            }
            if cases_compatible(&cases, &skel_names) {
                if dbg {
                    eprintln!("[replay]   MATCH at candidate#{}", tried);
                }
                return Some((m, sort_cases(cases)));
            }
        }
    }
    if dbg { eprintln!("[replay] raw-solve: no candidate matched"); }
    None
}

fn method_kind(m: &ProofMethod) -> String {
    match m {
        ProofMethod::Simplify => "Simplify".into(),
        ProofMethod::Induction => "Induction".into(),
        ProofMethod::Sorry(_) => "Sorry".into(),
        ProofMethod::Finished(_) => "Finished".into(),
        ProofMethod::Invalidated => "Invalidated".into(),
        ProofMethod::SolveGoal(g) => format!("SolveGoal({})", goal_kind(g)),
    }
}

fn goal_kind(g: &Goal) -> String {
    match g {
        Goal::Action(_, f) => format!("Action({})", fact_tag_name(&f.tag)),
        Goal::Premise(np, f) => format!("Premise(prem={},{})", (np.1).0, fact_tag_name(&f.tag)),
        Goal::Chain(_, _) => "Chain".into(),
        Goal::Split(_) => "Split".into(),
        Goal::Disj(_) => "Disj".into(),
        Goal::Subterm(_) => "Subterm".into(),
    }
}

/// Match the produced case-name set against the skeleton's child case
/// names.
///
/// HS's `checkProof` (Proof.hs:455-469) uses `mergeMapsWith
/// unhandledCase noSystemPrf (go (d+1))` — it tolerates BOTH (a) cases
/// the skeleton has but runtime doesn't produce (preserved as
/// `noSystemPrf` — Sorry-style placeholders), and (b) cases the
/// runtime produces but the skeleton doesn't have (handled by
/// `unhandledCase = prover d` — auto-prover).
///
/// But that only applies AFTER the right candidate goal is picked.
/// When choosing among ranked goal candidates for a `GoalSpec::Raw`
/// goal whose formula we couldn't structurally parse, we need a
/// STRICT match (every skel name in produced) to ensure we pick the
/// correct goal — not just a same-name-prefix candidate.  Otherwise
/// we'd accept an unrelated goal that happens to share a case name
/// (e.g. `case_1`), leading to deeper-tree drift.
fn cases_compatible(produced: &[(String, System)], skel: &[&str]) -> bool {
    if skel.is_empty() { return false; }
    if skel.len() == 1 && skel[0].is_empty() {
        return produced.len() == 1;
    }
    let prod_names: std::collections::BTreeSet<&str> =
        produced.iter().map(|(n, _)| n.as_str()).collect();
    skel.iter().all(|s| prod_names.contains(s))
}

fn sort_cases(mut cases: Vec<(String, System)>) -> Vec<(String, System)> {
    // Mirror search.rs:507-508: cases are visited in alphabetical
    // order so name-based skeleton matching is deterministic.
    cases.sort_by(|a, b| a.0.cmp(&b.0));
    cases
}

/// Resolve a parsed method to a runtime [`ProofMethod`] against `sys`.
///
/// For `SolveGoal`, this involves matching the parsed [`GoalSpec`]
/// against an actual [`Goal`] in `sys.goals`.  See `match_goal`.
fn resolve_method(parsed: &ParsedMethod, sys: &System) -> Option<ProofMethod> {
    match parsed {
        ParsedMethod::Sorry => Some(ProofMethod::Sorry(None)),
        ParsedMethod::Simplify => Some(ProofMethod::Simplify),
        ParsedMethod::Induction => Some(ProofMethod::Induction),
        ParsedMethod::Contradiction => {
            // Handled inline as a leaf above.  If we reach here it's
            // because the skeleton has a `by contradiction` step
            // followed by `case` blocks — malformed.  Fall back.
            None
        }
        ParsedMethod::SolveGoal(spec) => {
            let g = match_goal(spec, sys)?;
            Some(ProofMethod::SolveGoal(g))
        }
        ParsedMethod::SolvedLeaf
        | ParsedMethod::Unfinishable
        | ParsedMethod::Invalidated
        | ParsedMethod::Other(_) => None,
    }
}

/// Find a [`Goal`] in `sys.goals` that matches the parsed [`GoalSpec`].
///
/// The skeleton's `solve(...)` text identifies a goal by fact NAME and
/// optionally a premise INDEX.  At replay time variable indices and
/// substitutions may differ from the skeleton's static text, so we
/// match structurally (fact name + arity + premise idx) rather than
/// by deep term equality.
///
/// HS does goal lookup via the parsed `Goal` directly (see
/// `Theory.Text.Parser.Proof.goal` Proof.hs:39-72), but HS's parsed
/// goal carries proper LVar identities populated by the parser's name
/// table; our skeleton parser captures only surface text, hence the
/// structural-match approach.
///
/// Returns `None` if no goal matches (or multiple ambiguous matches
/// exist with no way to disambiguate); the caller falls back to the
/// auto-prover.
fn match_goal(spec: &GoalSpec, sys: &System) -> Option<Goal> {
    match spec {
        GoalSpec::Action { fact, .. } => {
            // Open Action goals whose fact name matches.  Skip KU
            // (auto-handled) for non-KU goal specs — the skeleton's
            // `solve(...)` always names protocol facts, never `KU(...)`.
            let want_name = &fact.name;
            let want_arity = fact.args.len();
            let want_persistent = fact.persistent;
            let mut matches: Vec<&Goal> = sys
                .goals
                .iter()
                .filter(|(_, st)| !st.solved)
                .filter_map(|(g, _)| match g {
                    Goal::Action(_, fa) => {
                        if name_matches(&fa.tag, want_name)
                            && fa.terms.len() == want_arity
                            && tag_persistent(&fa.tag) == want_persistent
                            && !matches!(fa.tag, FactTag::Ku)
                        {
                            Some(g)
                        } else { None }
                    }
                    _ => None,
                })
                .collect();
            if matches.len() == 1 {
                return Some(matches.remove(0).clone());
            }
            // Ambiguous → pick the first in source order to mirror HS's
            // goalNrRanking-style ordering.  HS would have unique
            // by-index; if our matches are ambiguous, the skeleton's
            // original goal must be one of them and creation order is
            // the closest proxy.
            if !matches.is_empty() {
                return Some(matches[0].clone());
            }
            None
        }
        GoalSpec::Premise { fact, prem_idx, .. } => {
            let want_name = &fact.name;
            let want_arity = fact.args.len();
            let want_persistent = fact.persistent;
            let mut matches: Vec<&Goal> = sys
                .goals
                .iter()
                .filter(|(_, st)| !st.solved)
                .filter_map(|(g, _)| match g {
                    Goal::Premise(np, fa) => {
                        if name_matches(&fa.tag, want_name)
                            && fa.terms.len() == want_arity
                            && tag_persistent(&fa.tag) == want_persistent
                            && (np.1).0 == *prem_idx
                        {
                            Some(g)
                        } else { None }
                    }
                    _ => None,
                })
                .collect();
            if matches.len() == 1 {
                return Some(matches.remove(0).clone());
            }
            if !matches.is_empty() {
                return Some(matches[0].clone());
            }
            None
        }
        GoalSpec::Raw(_) => None,
    }
}

fn name_matches(tag: &FactTag, want: &str) -> bool {
    fact_tag_name(tag) == want
}

fn tag_persistent(tag: &FactTag) -> bool {
    matches!(tag, FactTag::Proto(Multiplicity::Persistent, _, _))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::system::System;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_parser::ast::{Fact as PFact, ParsedMethod, ParsedProofTree};

    fn maude() -> Option<MaudeHandle> {
        let path = std::env::var("MAUDE_PATH").ok().or_else(|| {
            for c in ["/home/linuxbrew/.linuxbrew/bin/maude", "/usr/local/bin/maude", "maude"] {
                if std::path::Path::new(c).exists() { return Some(c.to_string()); }
            }
            None
        })?;
        MaudeHandle::start(&path, pair_maude_sig()).ok()
    }

    /// A Sorry-only skeleton on an empty system should be a degenerate
    /// replay → equivalent to running the auto-prover directly.
    #[test]
    fn sorry_leaf_runs_auto_prover() {
        let h = match maude() { Some(m) => m, None => return };
        let ctx = ProofContext::new(h, Vec::new());
        let sys = System::empty();
        // Skeleton = `by sorry`.
        let skel = ParsedProofTree {
            method: ParsedMethod::Sorry,
            cases: Vec::new(),
        };
        let _ = replace_sorry_prove(&ctx, sys, &skel, 50);
        // Just must terminate; status indeterminate on empty system.
    }

    /// A `by contradiction` leaf on a system with no contradictions
    /// must NOT silently emit Finished(Contradictory) — it should emit
    /// a Sorry with reason.
    #[test]
    fn contradiction_leaf_without_contradiction_is_sorry() {
        let h = match maude() { Some(m) => m, None => return };
        let ctx = ProofContext::new(h, Vec::new());
        let mut sys = System::empty();
        // Force out of initial state so is_finished can run.
        sys.solved_formulas.push(crate::guarded::gtrue());
        let skel = ParsedProofTree {
            method: ParsedMethod::Contradiction,
            cases: Vec::new(),
        };
        let result = replace_sorry_prove(&ctx, sys, &skel, 50);
        // No goals, no contradictions → is_finished returns Solved.
        // contradiction-leaf with non-contradictory runtime → Sorry.
        assert_eq!(result.status, NodeStatus::Sorry);
    }

    /// Match an Action goal by fact name + arity.  Uses an empty-args
    /// fact for simplicity (matches by tag name + arity 0).
    #[test]
    fn match_action_goal_by_name_arity() {
        use crate::fact::{Fact, FactTag, Multiplicity};
        let i = LVar::new("t", LSort::Node, 0);
        let tag = FactTag::Proto(Multiplicity::Linear, "Setup".into(), 0);
        let fact = Fact::new(tag, Vec::new());
        let goal = Goal::Action(i.clone(), fact);
        let mut sys = System::empty();
        sys.goals.push((goal.clone(), Default::default()));
        let spec = GoalSpec::Action {
            fact: PFact {
                persistent: false,
                name: "Setup".into(),
                args: Vec::new(),
                annotations: Vec::new(),
            },
            time_var: "t".into(),
        };
        let matched = match_goal(&spec, &sys).expect("should match");
        assert!(matches!(matched, Goal::Action(_, _)));
    }

    /// match_goal returns None when no goal matches the fact name.
    #[test]
    fn no_match_returns_none() {
        use crate::fact::{Fact, FactTag, Multiplicity};
        let i = LVar::new("t", LSort::Node, 0);
        let tag = FactTag::Proto(Multiplicity::Linear, "Setup".into(), 0);
        let fact = Fact::new(tag, Vec::new());
        let goal = Goal::Action(i, fact);
        let mut sys = System::empty();
        sys.goals.push((goal, Default::default()));
        let spec = GoalSpec::Action {
            fact: PFact {
                persistent: false,
                name: "WrongName".into(),
                args: Vec::new(),
                annotations: Vec::new(),
            },
            time_var: "t".into(),
        };
        assert!(match_goal(&spec, &sys).is_none());
    }
}
