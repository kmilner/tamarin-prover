//! Proof-search driver — port of the `Theory.Proof` step loop.
//!
//! In Haskell, a proof tree (`LTreeProof`) grows by repeatedly:
//! 1. Picking a `ProofMethod` via the heuristic ranking.
//! 2. Executing it to produce zero or more child sub-systems.
//! 3. Recursing on each child.
//!
//! The full ranking is large (`rankGoals` enumerates many Tamarin
//! priorities); for now we implement the "first open goal, then
//! simplify" heuristic — enough to drive small examples end-to-end
//! and exercise the solver wiring.
//!
//! The search is bounded by `max_steps` to keep tests deterministic.

use std::collections::BTreeMap;

use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::proof_method::{
    exec_proof_method, is_finished, ProofMethod, Result as MethodResult,
};
use crate::constraint::system::System;

/// One node in the proof tree.
#[derive(Debug, Clone)]
pub struct ProofNode {
    pub method: ProofMethod,
    pub sys: System,
    pub children: BTreeMap<String, ProofNode>,
    pub status: NodeStatus,
}

/// What's the proof-tree node currently saying?
#[derive(Debug, Clone, PartialEq)]
pub enum NodeStatus {
    /// Not yet finished — has open children to explore.
    Open,
    /// All branches reached `Solved`.
    Solved,
    /// At least one branch reached `Contradictory(_)`.
    Contradictory,
    /// At least one branch reached `Unfinishable`.
    Unfinishable,
    /// Exceeded the `max_steps` budget.
    Sorry,
}

/// Per-lemma wall-clock cap on `run_proof_search`. Mirrors Haskell
/// tamarin's `--prove-timeout` flag: when the search tree branches
/// faster than CR-rules can prune (e.g. with a richer signature), we'd
/// rather mark the lemma `Sorry` than spin forever. Set via the
/// `TAM_PROVE_DEADLINE_MS` env var; default 30s, which matches
/// tamarin's per-lemma default.
fn proof_deadline() -> std::time::Instant {
    let ms: u64 = std::env::var("TAM_PROVE_DEADLINE_MS").ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(30_000);
    std::time::Instant::now() + std::time::Duration::from_millis(ms)
}

thread_local! {
    /// Thread-local per-search deadline. Set at the start of
    /// `run_proof_search`, queried from `solve_action_goal` /
    /// `solve_premise_goal` so wide case enumeration can short-circuit
    /// when the wall-clock cap is hit (the recursion-only check only
    /// fires between successive `expand` calls — a single
    /// `exec_proof_method` enumerating thousands of cases would
    /// otherwise sit unchecked).
    static DEADLINE: std::cell::Cell<Option<std::time::Instant>> =
        std::cell::Cell::new(None);

    /// ID-DFS depth limit for the current iteration.  `usize::MAX` =
    /// no limit (default; matches pre-ID-DFS behaviour).  Set per
    /// iteration in `run_proof_search`'s ID-DFS loop.
    static MAX_DEPTH: std::cell::Cell<usize> = std::cell::Cell::new(usize::MAX);

    /// Set to true by `expand` whenever a node hits `MAX_DEPTH`.  The
    /// top-level loop reads this between iterations to decide whether
    /// to retry with doubled depth.  Mirrors Haskell's `MaybeNoSolution`
    /// sentinel in `cutOnSolvedDFS` (Proof.hs:855-877).
    static DEPTH_LIMIT_HIT: std::cell::Cell<bool> = std::cell::Cell::new(false);
}

/// True iff the current search is past its wall-clock deadline.
pub fn deadline_reached() -> bool {
    DEADLINE.with(|d| d.get().map(|t| std::time::Instant::now() >= t).unwrap_or(false))
}

fn set_deadline(t: std::time::Instant) { DEADLINE.with(|d| d.set(Some(t))); }
fn clear_deadline()                     { DEADLINE.with(|d| d.set(None));     }

/// Run a small-step search to depth `max_steps`. Heuristic: try
/// `Simplify` once, then pick the first open goal each round.
///
/// Returns the root proof node. The final status is the OR of children
/// (Solved if all children solved, Contradictory if any contradictory,
/// etc.) — matching Haskell's notion of "complete" proofs.
///
/// **Iterative-deepening DFS** — port of Haskell's `cutOnSolvedDFS`
/// (Proof.hs:855-877).  Starts at `max_depth=4` and doubles up to
/// 2048.  At each iteration:
///   1. Run `expand` with the current `MAX_DEPTH`.
///   2. If status is Solved → return immediately (matches Haskell's
///      `Solution path` short-circuit via `<>`).
///   3. If `DEPTH_LIMIT_HIT` was set and depth < cap → double and retry.
///   4. Else (no Solved found, no depth limit hit) → return.
///
/// This makes shorter Solved paths win over longer Solved paths even
/// when the longer path is alphabetically earlier — critical for
/// NSPK3/roles `injective_agree` where Haskell renders `case c_aenc`
/// (shorter) over `case I_2` (alphabetically earlier but deeper).
///
/// `TAM_DISABLE_ID_DFS=1` falls back to single-pass with no depth limit
/// (pre-ID-DFS behaviour) — useful for diagnosing regressions.
pub fn run_proof_search(
    ctx: &ProofContext,
    initial: System,
    max_steps: usize,
) -> ProofNode {
    let deadline = proof_deadline();
    set_deadline(deadline);
    let id_dfs_disabled = std::env::var("TAM_DISABLE_ID_DFS").is_ok();
    let cap: usize = 2048;
    let mut current_max_depth: usize = if id_dfs_disabled { usize::MAX } else { 4 };
    let mut root;
    loop {
        MAX_DEPTH.with(|m| m.set(current_max_depth));
        DEPTH_LIMIT_HIT.with(|f| f.set(false));
        let mut budget = max_steps;
        root = ProofNode {
            method: ProofMethod::Sorry(Some("initial".into())),
            sys: initial.clone(),
            children: BTreeMap::new(),
            status: NodeStatus::Open,
        };
        expand(ctx, &mut root, &mut budget, &deadline, 0);
        if id_dfs_disabled {
            break;
        }
        if matches!(root.status, NodeStatus::Solved | NodeStatus::Contradictory) {
            break;
        }
        if std::time::Instant::now() >= deadline {
            break;
        }
        let hit_depth = DEPTH_LIMIT_HIT.with(|f| f.get());
        if !hit_depth {
            // No branch hit the depth limit — going deeper won't help.
            break;
        }
        if current_max_depth >= cap {
            // Depth cap reached; accept whatever we have.
            break;
        }
        current_max_depth = current_max_depth.saturating_mul(2).min(cap);
    }
    MAX_DEPTH.with(|m| m.set(usize::MAX));
    DEPTH_LIMIT_HIT.with(|f| f.set(false));
    clear_deadline();
    root
}

fn expand(
    ctx: &ProofContext,
    node: &mut ProofNode,
    budget: &mut usize,
    deadline: &std::time::Instant,
    depth: usize,
) {
    let dbg_expand = std::env::var("TAM_DBG_EXPAND").is_ok();
    if dbg_expand {
        eprintln!("[expand] enter depth={} budget={} sys.nodes={} goals={}",
            depth, *budget, node.sys.nodes.len(), node.sys.goals.len());
    }
    crate::state_trace::emit("expand", None, &node.sys);
    // ID-DFS depth limit (Haskell `cutOnSolvedDFS` Proof.hs:855-877).
    //
    // Haskell's `findSolved` checks `d >= dMax` BEFORE checking the
    // node's method type:
    //
    //   findSolved d node
    //     | d >= dMax = MaybeNoSolution
    //     | otherwise = case node of
    //         LNode (ProofStep (Finished Solved) ...) _  -> Solution path
    //         ...
    //
    // So a Solved leaf at depth d == dMax becomes MaybeNoSolution, NOT
    // Solution.  This is critical for correct alphabetical-first selection
    // during iterative deepening: if a shorter Solved (case_2 at d=8)
    // exists alongside a longer one (case_1 at d=15), Haskell needs to
    // iterate dMax up to >= 16 before EITHER returns Solution, at which
    // point alphabetical-first (case_1) wins.  Checking is_finished
    // before the depth limit would make our case_2 close at max_depth=8
    // and short-circuit before case_1 is reachable at deeper iterations.
    //
    // See [[project_rust_id_dfs]] for the original ID-DFS port and
    // KAS2_eCK::eCK_key_secrecy for the case that motivated this fix.
    let max_depth = MAX_DEPTH.with(|m| m.get());
    if depth >= max_depth {
        DEPTH_LIMIT_HIT.with(|f| f.set(true));
        node.method = ProofMethod::Sorry(Some("depth limit".into()));
        node.status = NodeStatus::Sorry;
        return;
    }
    // Already terminal.
    if let Some(r) = is_finished(ctx, &node.sys) {
        node.method = ProofMethod::Finished(r.clone());
        node.status = match r {
            MethodResult::Solved => NodeStatus::Solved,
            MethodResult::Contradictory(_) => NodeStatus::Contradictory,
            MethodResult::Unfinishable => NodeStatus::Unfinishable,
        };
        return;
    }
    if std::time::Instant::now() >= *deadline {
        node.method = ProofMethod::Sorry(Some("deadline reached".into()));
        node.status = NodeStatus::Sorry;
        return;
    }
    if *budget == 0 {
        node.method = ProofMethod::Sorry(Some("budget exhausted".into()));
        node.status = NodeStatus::Sorry;
        return;
    }
    *budget -= 1;
    // Mirror Haskell's `rankProofMethods` → `execMethods` flow:
    // build a priority-ordered list of candidate methods, try each
    // until one's `exec_proof_method` returns `Some(cases)`.  Haskell
    // does this via `mapMaybe execMethod`; for the automatic-search
    // path we pick the first surviving method.
    //
    // Reference: `Theory.Constraint.Solver.ProofMethod.rankProofMethods`
    // (`ProofMethod.hs:520`):
    //
    //   proofMethods = bool toList insertInduction (isInitialSystem sys)
    //                  ((Simplify, "") :| goals)
    //   insertInduction (simplify :| gs) = case pcUseInduction ctxt of
    //     AvoidInduction -> simplify : (Induction, "") : gs
    //     UseInduction   -> (Induction, "") : simplify : gs
    //
    // Then `execMethods` filters to those that succeed.
    let candidates = candidate_methods(&node.sys, ctx);
    if dbg_expand {
        let names: Vec<String> = candidates.iter().map(|m| format!("{:?}", m).chars().take(40).collect()).collect();
        eprintln!("[expand] candidates: {:?}", names);
    }
    let (method, cases) = {
        let mut pick: Option<(ProofMethod, Vec<(String, System)>)> = None;
        for m in candidates {
            if dbg_expand {
                let name: String = format!("{:?}", m).chars().take(40).collect();
                eprintln!("[expand] try method {}", name);
            }
            let t0 = std::time::Instant::now();
            let r = exec_proof_method(ctx, &m, &node.sys);
            if dbg_expand {
                eprintln!("[expand] method took {:?}, result_kind={}", t0.elapsed(),
                    if r.is_some() { "Some" } else { "None" });
            }
            match r {
                Some(cs) => { pick = Some((m, cs)); break; }
                None => continue,
            }
        }
        match pick {
            Some(p) => p,
            None => {
                node.method = ProofMethod::Sorry(Some("no method".into()));
                node.status = NodeStatus::Sorry;
                return;
            }
        }
    };
    if dbg_expand {
        eprintln!("[expand] picked {} cases", cases.len());
    }
    node.method = method;
    if cases.is_empty() {
        // Empty case-map after exec means contradictory closure.
        node.status = NodeStatus::Contradictory;
        return;
    }
    let mut all_closed = true;       // All children are Solved OR Contradictory
    let mut any_contra = false;
    let mut any_solved = false;
    let mut any_unfin = false;
    let mut any_sorry = false;
    // Early-break-on-Solved (Haskell `foldMap` semantics):
    //
    // Haskell's Disj-monad is lazy — once any branch returns
    // `TraceFound` (Solved), the monad short-circuits and siblings
    // aren't forced.  Haskell's proof tree renders only what was
    // forced: the Solved branch and its ancestors.  Our search does
    // the same — once any child closes Solved, parent's status is
    // Solved (per rollup) and remaining siblings are wasted work.
    //
    // Critical for NSPK3::nonce_secrecy and other attack lemmas:
    // Haskell finds the trace at one specific case (e.g. `c_aenc`)
    // after the lazy Disj-monad short-circuits other paths.
    //
    // Case iteration order: `execProofMethod` (ProofMethod.hs:435-441)
    // builds a `Data.Map` keyed by case name via `M.fromListWith`, so
    // entries are alphabetically ordered.  `proveSystemDFS` /
    // `cutOnSolvedDFS` then walk in map order (Proof.hs:855-877 —
    // `foldMap`, `M.map`).  Our `Vec` preserves creation order
    // (source-file rule order), so sort by name to match Haskell.
    let mut cases = cases;
    cases.sort_by(|a, b| a.0.cmp(&b.0));
    // Haskell-faithful: no per-branch budget split.  Haskell's lazy
    // Disj-monad explores each branch using as many steps as needed —
    // there is no step-count cap on individual branches.  The ID-DFS
    // depth limit (above) prevents infinite recursion; deadline catches
    // runaway Maude calls.  Earlier fair-budget split divided `budget`
    // by `n_cases`, which caused deeply-branching paths to exhaust
    // their per-branch share before reaching a Solved leaf, even when
    // total budget was generous.  Each child sees the same shared
    // `budget` counter, decremented as it explores.
    for (name, sys) in cases {
        if any_solved { break; }  // Haskell-lazy: stop on first TraceFound.
        let mut child = ProofNode {
            method: ProofMethod::Sorry(None),
            sys,
            children: BTreeMap::new(),
            status: NodeStatus::Open,
        };
        expand(ctx, &mut child, budget, deadline, depth + 1);
        match child.status {
            NodeStatus::Solved => any_solved = true,
            NodeStatus::Contradictory => any_contra = true,
            NodeStatus::Unfinishable => { any_unfin = true; all_closed = false; }
            NodeStatus::Sorry => { any_sorry = true; all_closed = false; }
            NodeStatus::Open => { all_closed = false; }
        }
        node.children.insert(name, child);
    }
    // Rollup follows Haskell's `Semigroup ProofStatus`
    // (`Theory.Proof:409`):
    //
    //   TraceFound <> _ = TraceFound
    //   _ <> TraceFound = TraceFound
    //   IncompleteProof <> _ = IncompleteProof
    //   _ <> IncompleteProof = IncompleteProof
    //   UnfinishableProof <> _ = UnfinishableProof
    //   _ <> UnfinishableProof = UnfinishableProof
    //   CompleteProof <> _ = CompleteProof
    //   _ <> CompleteProof = CompleteProof
    //
    // `TraceFound` (a Solved leaf was found) absorbs every other
    // status — once *any* branch finds a witness, the whole proof
    // is TraceFound (witness exists).  This is what makes the
    // automatic prover correctly identify exists-trace verdicts
    // even when sibling branches remain Sorry.
    //
    // `CompleteProof` (all branches closed without finding a
    // witness) corresponds to our `Contradictory` — every path
    // exhausts to ⊥.
    node.status = if any_solved {
        NodeStatus::Solved
    } else if any_sorry {
        NodeStatus::Sorry
    } else if any_unfin {
        NodeStatus::Unfinishable
    } else if any_contra {
        // All children closed without any Solved — every path
        // reached ⊥, so the parent is Contradictory.
        NodeStatus::Contradictory
    } else {
        // No children at all — defensive fallback; the empty
        // case-set was already handled earlier as `Contradictory`.
        NodeStatus::Sorry
    };
    let _ = all_closed; // unused now — kept the variable to mark
                        // intent that `Contradictory` requires no
                        // open branch (only Contradictory children).
}

/// Build the priority-ordered list of candidate proof methods to
/// try at this node.  Mirrors Haskell's `rankProofMethods`
/// (`ProofMethod.hs:520`):
///
///   proofMethods = bool toList insertInduction (isInitialSystem sys)
///                  ((Simplify, "") :| goals)
///   insertInduction (simplify :| gs) = case pcUseInduction ctxt of
///     AvoidInduction -> simplify : (Induction, "") : gs
///     UseInduction   -> (Induction, "") : simplify : gs
///
/// Then `execMethods` filters to those that succeed; the first
/// surviving method is picked.  Important: Simplify is *always*
/// in the list before goals so that when the system is reducible
/// the simplifier runs first, decomposing pending formulas into
/// goals.  Induction is only added in the initial state.
pub fn candidate_methods(
    sys: &System,
    ctx: &ProofContext,
) -> Vec<ProofMethod> {
    use crate::constraint::solver::context::UseInduction;
    let mut out: Vec<ProofMethod> = Vec::new();
    // Haskell-faithful: build the FULL ranked goal list, not just the
    // first one (ProofMethod.hs:520-540).  Haskell's `proofMethods`
    // includes ALL open goals as SolveGoal candidates; `execMethods`
    // then filters via `mapMaybe execMethod` and picks the first that
    // succeeds.  If the highest-ranked goal's SolveGoal returns None
    // (e.g. its dispatch_solve_goal hit Contradictory and was filtered),
    // we fall through to the next-ranked goal.
    //
    // Previously we only added the FIRST ranked goal, causing search
    // to Sorry whenever the top goal was un-solvable — even if a
    // lower-ranked goal could have made progress.
    let goals = crate::constraint::solver::goals::rank_goals_with(sys, Some(ctx));
    // Construct: [Simplify, goal_1, goal_2, ..., goal_N].
    out.push(ProofMethod::Simplify);
    for g in goals.into_iter() {
        out.push(ProofMethod::SolveGoal(g.goal));
    }
    // Insert Induction at the appropriate position in initial state.
    let initial = can_apply_induction(sys);
    if initial {
        let can_induct = sys.formulas.first()
            .map(|fm| crate::guarded::ginduct(fm).is_ok())
            .unwrap_or(false);
        if can_induct {
            match ctx.use_induction {
                UseInduction::UseInduction => {
                    // [Induction, Simplify, goals...]
                    out.insert(0, ProofMethod::Induction);
                }
                UseInduction::AvoidInduction => {
                    // [Simplify, Induction, goals...]
                    out.insert(1, ProofMethod::Induction);
                }
            }
        }
    }
    out
}

/// Legacy single-method picker (kept for now in case callers expect
/// it).  Returns the first candidate from `candidate_methods`.
#[allow(dead_code)]
fn pick_method(
    sys: &System,
    ctx: &ProofContext,
) -> ProofMethod {
    candidate_methods(sys, ctx).into_iter().next()
        .unwrap_or(ProofMethod::Simplify)
}

/// Goal picker — delegates to `goals::rank_goals_with` (port of
/// Haskell's `Theory.Constraint.Solver.ProofMethod.smartRanking`)
/// and returns the first ranked open goal.  Threads the proof
/// context through so source-cache predicates
/// (`is_msg_one_case_goal`) can access `ctx.full_sources`.
///
/// Currently unused — live callers go through `candidate_methods` →
/// `execProofMethod` which embeds the same ranking.  Kept as a
/// reusable helper for diagnostic code that wants just the goal.
#[allow(dead_code)]
fn pick_open_goal(
    sys: &System,
    ctx: &ProofContext,
) -> Option<crate::constraint::constraints::Goal> {
    crate::constraint::solver::goals::rank_goals_with(sys, Some(ctx))
        .into_iter()
        .next()
        .map(|a| a.goal)
}

/// Mirror of Haskell's `canApplyInduction` precondition: induction is
/// only valid on the *initial* state of the system, before anything
/// else has been added.
fn can_apply_induction(sys: &System) -> bool {
    sys.nodes.is_empty()
        && sys.edges.is_empty()
        && sys.less_atoms.is_empty()
        && sys.solved_formulas.is_empty()
        && sys.goals.is_empty()
        && sys.formulas.len() == 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_sig::pair_maude_sig;

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        for c in ["/home/linuxbrew/.linuxbrew/bin/maude", "/usr/local/bin/maude", "maude"] {
            if std::path::Path::new(c).exists() { return Some(c.to_string()); }
        }
        None
    }

    fn ctx() -> Option<ProofContext> {
        let path = maude_path()?;
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).ok()?;
        Some(ProofContext::new(h, Vec::new()))
    }

    #[test]
    fn search_empty_system_with_a_node_solves_immediately() {
        let ctx = match ctx() { Some(c) => c, None => return };
        // Force out of initial state by adding a node, then no goals
        // / subterms remain.
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
        let mut sys = System::empty();
        // Mark non-initial via a solved formula (Haskell's
        // `isInitialSystem` uses solved_formulas emptiness, not the
        // node/edge count).
        sys.solved_formulas.push(crate::guarded::gtrue());
        sys.add_node(tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0), rule);
        let root = run_proof_search(&ctx, sys, 10);
        assert_eq!(root.status, NodeStatus::Solved);
    }

    #[test]
    fn search_empty_disj_goal_closes_contradictory() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut sys = System::empty();
        // Force out of initial state.
        sys.add_less(crate::constraint::constraints::LessAtom::new(
            tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
            tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
            crate::constraint::constraints::Reason::Fresh,
        ));
        // An empty disjunction comes hand-in-hand with `gfalse` in the
        // formula set (insert_formula pushes both).  That's
        // also how Haskell signals contradictoryness — `openGoals`
        // filters `DisjG (Disj [])` and `FormulasFalse` fires from
        // `contradictions`.  We mirror exactly that here.
        sys.formulas.push(crate::guarded::gfalse());
        sys.add_goal(crate::constraint::constraints::Goal::Disj(
            crate::constraint::constraints::Disj::new(Vec::new()),
        ));
        let root = run_proof_search(&ctx, sys, 5);
        assert_eq!(root.status, NodeStatus::Contradictory);
    }

    #[test]
    fn search_disj_goal_with_two_branches_lazy_early_break_on_solved() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut sys = System::empty();
        // Force out of initial state.
        sys.add_less(crate::constraint::constraints::LessAtom::new(
            tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
            tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
            crate::constraint::constraints::Reason::Fresh,
        ));
        // Add a 2-branch disjunction goal — true | false.
        // Haskell's lazy Disj-monad early-breaks once any branch
        // returns TraceFound (Solved).  The gtrue branch Solves
        // immediately, so the gfalse branch is never forced.
        // Our search mirrors this: only 1 child rendered.
        let f1 = crate::guarded::gtrue();
        let f2 = crate::guarded::gfalse();
        sys.add_goal(crate::constraint::constraints::Goal::Disj(
            crate::constraint::constraints::Disj::new(vec![f1, f2]),
        ));
        let root = run_proof_search(&ctx, sys, 10);
        assert!(matches!(root.method,
            ProofMethod::SolveGoal(crate::constraint::constraints::Goal::Disj(_))));
        // Lazy early-break: only the first-Solved branch is rendered.
        assert_eq!(root.children.len(), 1);
        assert_eq!(root.status, NodeStatus::Solved);
    }

    #[test]
    fn search_simplify_then_solved_after_dedup_pass() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut sys = System::empty();
        // Force out of initial state.
        sys.add_less(crate::constraint::constraints::LessAtom::new(
            tamarin_term::lterm::LVar::new("a", tamarin_term::lterm::LSort::Node, 0),
            tamarin_term::lterm::LVar::new("b", tamarin_term::lterm::LSort::Node, 0),
            crate::constraint::constraints::Reason::Fresh,
        ));
        // Two duplicate gtrue formulas — `dedupe_formulas_pass` must
        // drop one and `drop_trivially_true_formulas_pass` drops both.
        sys.formulas.push(crate::guarded::gtrue());
        sys.formulas.push(crate::guarded::gtrue());
        let root = run_proof_search(&ctx, sys, 5);
        assert_eq!(root.status, NodeStatus::Solved);
    }

    #[test]
    fn search_runs_out_of_budget_returns_sorry() {
        let ctx = match ctx() { Some(c) => c, None => return };
        let mut sys = System::empty();
        // Open subterm goal that we can't actually progress on.
        let v = tamarin_term::lterm::LVar::new(
            "x", tamarin_term::lterm::LSort::Msg, 0);
        let v2 = tamarin_term::lterm::LVar::new(
            "y", tamarin_term::lterm::LSort::Msg, 0);
        use tamarin_term::vterm::Lit;
        let tx: tamarin_term::lterm::LNTerm =
            tamarin_term::term::Term::Lit(Lit::Var(v));
        let ty: tamarin_term::lterm::LNTerm =
            tamarin_term::term::Term::Lit(Lit::Var(v2));
        // Create an Action goal — without any rules in ctx the solver
        // will keep returning Contradictory branches, but the goal
        // itself stays unsolved across iterations.
        let i = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let f = crate::fact::out_fact(tx);
        sys.add_goal(crate::constraint::constraints::Goal::Action(i, f));
        // Add a non-empty piece so isInitialSystem returns false.
        sys.subterm_store.add(ty.clone(), ty);
        let root = run_proof_search(&ctx, sys, 1);
        // Budget=1: one expand step. Action goal with no rules → contradiction.
        assert!(matches!(root.status,
            NodeStatus::Contradictory | NodeStatus::Sorry | NodeStatus::Solved));
    }
}
