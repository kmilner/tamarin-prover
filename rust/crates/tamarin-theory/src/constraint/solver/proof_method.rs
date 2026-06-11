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
    /// Display-only: `solve( <raw_inner> )`.  Used for HS-faithful
    /// unannotated subtree display (replay.rs `parsed_to_unannotated`)
    /// where we have the original skeleton text but no live Goal object.
    /// HS `noSystemPrf` (Proof.hs:469) carries the original ProofMethod
    /// verbatim; RS uses raw inner text as the closest equivalent.
    RawSolve(String),
}

/// `isFinished`: returns the appropriate `Result` if the system is in
/// a terminal state — solved, contradictory, or unfinishable.
pub fn is_finished(ctx: &ProofContext, sys: &System) -> Option<Result> {
    if is_initial_system(sys) { return None; }
    let cs = contradictions(ctx, sys);
    if let Some(c) = cs.into_iter().next() {
        // Mirror Haskell `contradictorySystem`: any contradiction
        // closes the branch.  Previous Cyclic/FormulasFalse→Unfinishable
        // routing for conflation patterns has been removed — it was
        // not Haskell-faithful.  See `project_rust_search_completeness_gaps.md`
        // for the underlying search-completeness bugs that those
        // workarounds were masking.
        let _ = ctx;
        // Haskell's `isFinished` (ProofMethod.hs:505) does not gate
        // Contradictory on incomplete-source consumption.  Source's
        // `incomplete` flag only affects diagnostic warnings, not
        // search verdict.  Removed the Unfinishable downgrade to match.
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
    // Mirror Haskell `isFinished`:
    //   | null ogs && stFinished     = Just Solved
    //   | null ogs && not stFinished = Just Unfinishable
    //   | otherwise                  = Nothing
    // where `ogs = openGoals sys` — the FILTERED list (with the
    // auto-solve KU heuristic applied), not just the unsolved-status
    // count.  Our `open_goals` does the same filtering, so we should
    // check IT for emptiness rather than the status flags.
    // Direct port of Haskell `isFinished` (ProofMethod.hs:505):
    //   | null ogs && stFinished     = Just Solved
    //   | null ogs && not stFinished = Just Unfinishable
    //   | otherwise                  = Nothing
    // (gfalse is caught as a FormulasFalse contradiction above, so we
    // don't need an explicit `no_false_formula` guard here.)
    use crate::constraint::solver::goals::open_goals;
    let no_open_goals = open_goals(sys).is_empty();
    let sub_finished = finished_subterms(ctx, sys);
    if no_open_goals && sub_finished {
        if std::env::var("TAM_RS_DBG_SOLVED_GOALS").as_deref() == Ok("1") {
            use crate::constraint::constraints::Goal;
            eprintln!("[SOLVED_GOALS] all open_goals empty. Showing all goal statuses:");
            for (g, st) in &sys.goals {
                let kind = match g {
                    Goal::Action(_, fa) => format!("Action({:?})", fa.tag),
                    Goal::Premise(_, fa) => format!("Premise({:?})", fa.tag),
                    Goal::Chain(_, _) => "Chain".to_string(),
                    Goal::Split(_) => "Split".to_string(),
                    Goal::Disj(_) => "Disj".to_string(),
                    Goal::Subterm(_) => "Subterm".to_string(),
                };
                let term_dump = match g {
                    Goal::Action(i, fa) | Goal::Premise((i, _), fa) =>
                        format!("@{}.{} {}", i.name, i.idx,
                            fa.terms.iter().map(|t| format!("{:?}", t).chars().take(60).collect::<String>())
                                .collect::<Vec<_>>().join(",")),
                    _ => String::new(),
                };
                eprintln!("[SOLVED_GOALS]   solved={} {} {}", st.solved, kind, term_dump);
            }
        }
        if std::env::var("TAM_DBG_SOLVED_DUMP").is_ok() {
            let path = crate::constraint::solver::trace::case_path_string();
            eprintln!("[SOLVED_DUMP] path={} nodes={} actions=?, formulas={}, solved_formulas={}, lemmas={}, edges={}, eq_store_n={}",
                path, sys.nodes.len(),
                sys.formulas.len(), sys.solved_formulas.len(),
                sys.lemmas.len(), sys.edges.len(),
                sys.eq_store.subst.to_list().len());
            eprintln!("[SOLVED_DUMP]   nodes:");
            for (id, r) in &sys.nodes {
                let acts: Vec<String> = r.actions.iter()
                    .map(|a| format!("{:?}({:?})", a.tag,
                        a.terms.iter().map(|t| format!("{:?}", t).chars().take(80).collect::<String>())
                            .collect::<Vec<_>>()))
                    .collect();
                eprintln!("[SOLVED_DUMP]     {}.{} {} acts={:?}",
                    id.name, id.idx,
                    crate::constraint::solver::reduction::rule_case_name(r),
                    acts);
            }
            eprintln!("[SOLVED_DUMP]   formulas (open):");
            for (i, f) in sys.formulas.iter().enumerate() {
                eprintln!("[SOLVED_DUMP]     [{}] {}", i, format!("{:?}", f).chars().take(300).collect::<String>());
            }
            eprintln!("[SOLVED_DUMP]   solved_formulas:");
            for (i, f) in sys.solved_formulas.iter().enumerate() {
                eprintln!("[SOLVED_DUMP]     [{}] {}", i, format!("{:?}", f).chars().take(300).collect::<String>());
            }
            eprintln!("[SOLVED_DUMP]   lemmas:");
            for (i, f) in sys.lemmas.iter().enumerate() {
                eprintln!("[SOLVED_DUMP]     [{}] {}", i, format!("{:?}", f).chars().take(300).collect::<String>());
            }
            eprintln!("[SOLVED_DUMP]   eq_store bindings:");
            for (v, t) in sys.eq_store.subst.to_list().iter() {
                eprintln!("[SOLVED_DUMP]     {}.{}({:?}) → {}",
                    v.name, v.idx, v.sort,
                    format!("{:?}", t).chars().take(150).collect::<String>());
            }
            eprintln!("[SOLVED_DUMP]   edges:");
            for e in &sys.edges {
                let src_rule = sys.nodes.iter()
                    .find(|(id, _)| id == &e.src.0)
                    .map(|(_, r)| crate::constraint::solver::reduction::rule_case_name(r))
                    .unwrap_or_else(|| "?".to_string());
                let tgt_rule = sys.nodes.iter()
                    .find(|(id, _)| id == &e.tgt.0)
                    .map(|(_, r)| crate::constraint::solver::reduction::rule_case_name(r))
                    .unwrap_or_else(|| "?".to_string());
                eprintln!("[SOLVED_DUMP]     ({}.{}/{},conc{}) → ({}.{}/{},prem{})",
                    e.src.0.name, e.src.0.idx, src_rule, e.src.1.0,
                    e.tgt.0.name, e.tgt.0.idx, tgt_rule, e.tgt.1.0);
            }
            eprintln!("[SOLVED_DUMP]   node-premises by node:");
            for (id, r) in &sys.nodes {
                let prems: Vec<String> = r.premises.iter()
                    .map(|f| format!("{:?}", f.tag))
                    .collect();
                let concs: Vec<String> = r.conclusions.iter()
                    .map(|f| format!("{:?}", f.tag))
                    .collect();
                eprintln!("[SOLVED_DUMP]     {}.{} ({}) prems={:?} concs={:?}",
                    id.name, id.idx,
                    crate::constraint::solver::reduction::rule_case_name(r),
                    prems, concs);
            }
        }
        // Haskell's `isFinished` (ProofMethod.hs:505) doesn't gate
        // Solved on `incomplete` source consumption — `Source.incomplete`
        // is diagnostic-only there.  Match that.
        Some(Result::Solved)
    }
    else if no_open_goals && !sub_finished { Some(Result::Unfinishable) }
    else { None }
}

/// Approximation of Haskell's `isInitialSystem`:
///   `null sSolvedFormulas && not (bot ∈ sFormulas)`
///
/// We add the structural-emptiness checks too, since our `System`
/// carries more state than Haskell's at this stage. The crucial
/// property is the `not bot in formulas` clause — a system whose
/// open formulas contain ⊥ is *contradictory*, not initial.
/// Direct port of Haskell `isInitialSystem`:
///   isInitialSystem sys = null (get sSolvedFormulas sys) && not (member bot (get sFormulas sys))
/// (`System.hs:828`).  Just two conditions: no solved formulas yet,
/// and no gfalse in the formula set.  We were checking many more
/// (empty nodes/edges/less/goals) which made us mark systems as
/// non-initial too early — that caused `is_finished` to short-circuit
/// to Solved/Unfinishable when Haskell would still return `None` and
/// continue searching.
fn is_initial_system(sys: &System) -> bool {
    let bot = crate::guarded::gfalse();
    sys.solved_formulas.is_empty() && !sys.formulas.contains(&bot)
}

/// Direct port of Haskell `finishedSubterms`
/// (`Theory.Tools.SubtermStore:130`):
///   hasReducibleOperatorsOnTop reducible sst =
///     all (topIsNotReducible . snd) allSubterms
///     where allSubterms = posSubterms ∪ negSubterms ∪ solvedSubterms
///           topIsNotReducible (FApp f _) = f ∉ reducible
///           topIsNotReducible _          = True
///
/// True iff every subterm's RHS has a top-level function symbol that
/// is NOT in the reducible set.  If any subterm's RHS has a reducible
/// top symbol, the proof cannot finish (further rewriting could
/// reduce it).
fn finished_subterms(ctx: &ProofContext, sys: &System) -> bool {
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::term::Term;
    let msig = ctx.maude.maude_sig();
    let top_is_not_reducible = |t: &tamarin_term::lterm::LNTerm| -> bool {
        match t {
            Term::App(f, _) => !msig.reducible_fun_syms.iter().any(|r| match (r, f) {
                (FunSym::NoEq(rs), FunSym::NoEq(fs)) => rs.name == fs.name,
                (FunSym::Ac(ra), FunSym::Ac(fa)) =>
                    std::mem::discriminant(ra) == std::mem::discriminant(fa),
                (FunSym::C(rc), FunSym::C(fc)) =>
                    std::mem::discriminant(rc) == std::mem::discriminant(fc),
                _ => false,
            }),
            // Variables and constants are never reducible at the top.
            _ => true,
        }
    };
    // HS `hasReducibleOperatorsOnTop` walks posSubterms ∪ negSubterms ∪
    // solvedSubterms (SubtermStore.hs:131-133).
    sys.subterm_store.subterms.iter().all(|s| top_is_not_reducible(&s.big))
        && sys.subterm_store.solved_subterms.iter().all(|s| top_is_not_reducible(&s.big))
        && sys.subterm_store.neg_subterms.iter().all(|(_, big)| top_is_not_reducible(big))
}

/// Execute a proof method against `sys`, returning the resulting
/// case list IN INSERTION ORDER. `Sorry` / `Finished` produce empty
/// cases; `Simplify` runs `simplify_system` and returns one case;
/// `SolveGoal(g)` dispatches via `solve_*_goal` and converts
/// `GoalCases` to a case list. `Induction` is left as a stub.
///
/// **Order matters**: Haskell's `disjunctionOfList` and the
/// downstream `runReduction` preserve the order of rules /
/// destructors as iterated in `joinAllRules` / saturate output.
/// Returning `Vec` (not `BTreeMap`) preserves that order so the
/// search explores cases in Haskell's same order, allowing the
/// `case c_aenc`-style trace-found paths to be reached without
/// being starved by alphabetically-earlier siblings.
pub fn exec_proof_method(
    ctx: &ProofContext,
    method: &ProofMethod,
    sys: &System,
) -> Option<Vec<(CaseName, System)>> {
    use crate::constraint::solver::reduction::{ChangeIndicator, GoalCases, Reduction};
    use crate::constraint::solver::simplify::simplify_system;

    // Deadline short-circuit (entry-guard).  Without this, a single
    // `exec_proof_method` invocation that internally enumerates many
    // Maude unifiers / source-case branches (e.g. bilinear-pairing
    // examples with large variant tables) can run for many seconds
    // before any caller checks the deadline.  Returning `None` signals
    // "no method applicable" — the caller in `expand_inner` then walks
    // the rest of the candidate list, all of which also return `None`,
    // and the node becomes `Sorry: no method`.  The next call up the
    // recursion checks the deadline at the top of `expand_inner` (line
    // 441 in search.rs) and bails to `Sorry: deadline reached`.
    // Combined, this bounds the post-deadline runtime to O(depth) rather
    // than O(remaining-work-in-current-method).
    if crate::constraint::solver::search::deadline_reached() {
        return None;
    }

    // HS-faithful per-step Maude counter reset (ProofMethod.hs:443):
    //   `runReduction (m <* simplifySystem) ctxt sys (avoid sys)`
    // The FreshT counter starts at `avoid sys + 1` for EVERY proof step.
    // Without this, Rust's Maude counter advances monotonically across all
    // proof steps — so witness idxs grow to hundreds where HS stays in
    // the ~20-30 range.  Beyond cosmetics, the unbounded growth surfaces
    // SubstVFresh same-target collisions: when a variant's lifted witness
    // gets a target idx that collides with another raw entry's target,
    // the collision pattern encodes an unintended unification that
    // cascades downstream (KAS_key_secrecy: `~ltkA.0` and `~ltkA.349`
    // both → `~ltkA.425` after lifting forces $R=$I via setNodes merge).
    //
    // Opt-out via `TAM_RS_PER_STEP_RESET_LEGACY=1`.
    if std::env::var("TAM_RS_PER_STEP_RESET_LEGACY").is_err() {
        let avoid = crate::constraint::solver::reduction::bounds_max(sys);
        ctx.maude.reset_counter_to(avoid.saturating_add(1));
    }

    match method {
        ProofMethod::Sorry(_) | ProofMethod::Finished(_) => Some(Vec::new()),
        ProofMethod::Invalidated | ProofMethod::RawSolve(_) => None,
        ProofMethod::Simplify => {
            // HS-faithful: `simplifySystem` (Simplify.hs:65-67) emits
            // its `traceExecM "simplifySystem"` ONCE per call; its
            // internal `go`-loop runs CR-rules to a fixpoint without
            // re-tracing.  We mirror that by tracing here (the logical
            // invocation site) and leaving `simplify_system` un-traced,
            // so the outer fixpoint loop below doesn't duplicate the
            // line.
            crate::constraint::solver::trace::trace_exec("simplifySystem");
            // HS-faithful simplify-time fan-out.  When
            // `solveUniqueActions` calls `solveGoal (ActionG i fa)`,
            // the `Reduction = StateT System (FreshT (DisjT ...))`
            // monad lets `disjunctionOfList` (over source-cases /
            // variants / Maude unifiers) fan out the entire enclosing
            // `simplifySystem` into N branches — one per fan-out case.
            // Each branch continues independently through the rest of
            // the simplify loop and post-loop, and surfaces here as a
            // sibling `Simplify` case.  HS's `process` then renders
            // them as `case 1`/`case 2`/... via `distinguish n`.
            //
            // Without fan-out, RS collapses 7 HS siblings to 1 on
            // Yubikey's `no_replay` (and 50 → 1 on
            // `slightly_weaker_invariant`), because `solve_action_goal`'s
            // Cases outcome was discarded.
            //
            // Kill switch: `TAM_RS_DISABLE_SIMPLIFY_FANOUT=1` reverts
            // to the in-place behaviour.
            let case_systems: Vec<System> =
                if std::env::var("TAM_RS_DISABLE_SIMPLIFY_FANOUT").is_ok() {
                    let mut r = Reduction::new(ctx, sys.clone());
                    r.changed = ChangeIndicator::Unchanged;
                    simplify_system(&mut r);
                    vec![r.sys]
                } else {
                    crate::constraint::solver::simplify::simplify_system_with_fanout(ctx, sys.clone())
                };
            // HS-faithful `cleanup` (ProofMethod.hs:453-454): EVERY
            // proof method's cases pass through `map (fmap cleanup .
            // fst)` (ProofMethod.hs:442), and `Simplify` goes through
            // `process` (ProofMethod.hs:405-406) — so its output is
            // ALSO cleaned.
            let cleanup = |s: &System| -> System {
                let mut s2 = s.clone();
                if std::env::var("TAM_DISABLE_RENAME_PRECISE").is_err() {
                    crate::constraint::solver::rename_precise::rename_precise_system(
                        &mut s2);
                }
                s2.eq_store.subst =
                    tamarin_term::subst::Subst::from_list(Vec::new());
                s2
            };
            // HS-faithful filter: cases whose eq_store is false were
            // mzero'd by `contradictoryIf` during simplify; they don't
            // show up in HS's surviving Disj.  (Other contradiction
            // reasons surface as explicit Finished(Contradictory) leaves.)
            let cleaned: Vec<System> = case_systems.into_iter()
                .filter(|s| !s.eq_store.is_false())
                .map(|s| cleanup(&s))
                .collect();
            if cleaned.is_empty() { return None; }
            let cleaned_input = cleanup(sys);
            if cleaned.len() == 1 {
                // Single-case path: HS's `Simplify` arm (ProofMethod.hs:419-424)
                // checks whether the simplified system equals the cleaned
                // input — if so, the method "failed" and we return None.
                // Multi-case fan-out trivially can't satisfy that condition.
                if cleaned[0] == cleaned_input { return None; }
                return Some(vec![("".to_string(), cleaned.into_iter().next().unwrap())]);
            }
            // HS-faithful naming: `distinguish n` (ProofMethod.hs:527-532)
            // with empty case name renders as `show i` ("1", "2", "3", ...)
            // with NO `_case_` prefix and NO zero-padding (the `pad`
            // call only runs in the else branch when the prefix is
            // non-empty).
            //
            // Inner duplicate detection: HS's `M.fromListWith (error
            // "case names not unique")` plus `uniqueListBy` dedups
            // exact-name duplicates structurally; for our empty-name
            // case all siblings get unique numeric names so no real
            // dedup is needed.
            let out: Vec<(String, System)> = cleaned.into_iter()
                .enumerate()
                .map(|(i, s)| ((i + 1).to_string(), s))
                .collect();
            Some(out)
        }
        ProofMethod::SolveGoal(g) => {
            let dbg_solve = std::env::var("TAM_DBG_SOLVE").is_ok();
            let t_dispatch = std::time::Instant::now();
            // State snapshot BEFORE dispatch — paired with HS's
            // `[STATE]` line in `Theory.Constraint.Solver.ProofMethod.solve`.
            // Emits the canonical open-goal / node set so we can see what
            // ranking decision was available at this proof step.  Reusable
            // for any future HS-vs-Rust step-by-step lockstep diff: set
            // `TAM_RS_TRACE_STATE=1` + `TAM_HS_TRACE_STATE=1` on both
            // sides, run the same theory, diff the outputs.
            crate::constraint::solver::trace::trace_state(sys);
            crate::constraint::solver::trace::trace_pick(g);
            // TAM_RS_DBG_PICK_NR=1 (mirrors HS TAM_HS_DBG_PICK_NR):
            // dump the picked goal's gsNr and the entire open-goal queue with
            // their gsNrs. Lets HS↔RS comparison align picks by gsNr ordering.
            if std::env::var("TAM_RS_DBG_PICK_NR").is_ok() {
                use crate::constraint::constraints::Goal;
                let pick_nr = sys.goals.iter()
                    .find(|(eg, _)| eg == g)
                    .map(|(_, st)| st.nr.to_string())
                    .unwrap_or_else(|| "?".to_string());
                let pick_kind = match g {
                    Goal::Action(_, fa) => format!("Action {:?}", fa),
                    Goal::Premise(_, fa) => format!("Premise {:?}", fa),
                    Goal::Chain(_, _) => "Chain".to_string(),
                    Goal::Split(_) => "Split".to_string(),
                    Goal::Disj(_) => "Disj".to_string(),
                    Goal::Subterm(_) => "Subterm".to_string(),
                };
                let all_open: Vec<String> = sys.goals.iter()
                    .filter(|(_, st)| !st.solved)
                    .map(|(eg, st)| {
                        let k = match eg {
                            Goal::Action(_, fa) => format!("Action({:?})", fa.tag),
                            Goal::Premise(_, fa) => format!("Premise({:?})", fa.tag),
                            Goal::Chain(_, _) => "Chain".to_string(),
                            Goal::Split(_) => "Split".to_string(),
                            Goal::Disj(_) => "Disj".to_string(),
                            Goal::Subterm(_) => "Subterm".to_string(),
                        };
                        format!("#{}:{}/lb={}", st.nr, k, st.looping)
                    })
                    .collect();
                let cpstr = crate::constraint::solver::trace::case_path_string();
                eprintln!("[RS_PICK_NR] path={} #{}:{}", cpstr, pick_nr, pick_kind);
                eprintln!("[RS_OPEN_NRS] path={} {}", cpstr, all_open.join(" ; "));
            }
            let mut r = Reduction::new(ctx, sys.clone());
            let outcome = crate::constraint::solver::goals::dispatch_solve_goal(&mut r, g);
            if dbg_solve {
                let truncate_at: usize = std::env::var("TAM_DBG_SOLVE_TRUNC")
                    .ok().and_then(|v| v.parse().ok()).unwrap_or(60);
                let name: String = format!("{:?}", g).chars().take(truncate_at).collect();
                let kind = match &outcome {
                    crate::constraint::solver::reduction::GoalCases::Linear => "Linear".to_string(),
                    crate::constraint::solver::reduction::GoalCases::LinearNamed(n) => format!("LinearNamed({})", n),
                    crate::constraint::solver::reduction::GoalCases::Cases(cs) => {
                        let names: Vec<&str> = cs.iter().map(|(n, _)| n.as_str()).collect();
                        format!("Cases({})=[{}]", cs.len(), names.join(","))
                    },
                    crate::constraint::solver::reduction::GoalCases::Contradictory => "Contradictory".to_string(),
                };
                eprintln!("[solve] dispatch {} → {} in {:?}", name, kind, t_dispatch.elapsed());
                if std::env::var("TAM_DBG_SOLVE_NODES").is_ok() {
                    // Dump sys.nodes (rule names per node) so we can
                    // see which rules are grafted when the goal is
                    // dispatched.
                    let mut node_list: Vec<String> = sys.nodes.iter()
                        .map(|(id, rule)| format!("{}#{}={}",
                            id.name, id.idx,
                            crate::constraint::solver::reduction::rule_case_name(rule)))
                        .collect();
                    node_list.sort();
                    eprintln!("[solve] nodes: [{}]", node_list.join(", "));
                }
            }
            // Run simplify after every goal-solving step — mirrors
            // Haskell's `m <* simplifySystem` pattern in `process`
            // (ProofMethod.hs:299-308).  Filter out cases that simplify
            // to a contradictory system — Haskell's Disj-monad does the
            // same via `mzero` on `contradictoryIf`, so contradictory
            // cases never make it into the children map.  This keeps
            // our proof tree the same shape as Haskell's: when every
            // case fires a contradiction, the SolveGoal node has 0
            // children (rendered as a leaf "by solve(...)" in Haskell
            // / "by contradiction /* closed */" in our normalised diff).
            //
            // Returns `Vec<System>` to surface simplify-time fan-out: when
            // `simplifySystem` internally fans out (via
            // `solveUniqueActions → solveAction → solveFactEqs SplitNow`
            // or any `insertFormula → insertAtom EqE → solveTermEqs
            // SplitNow` whose Maude AC unification returns multiple
            // arms), the DisjT-monad in HS's `runReduction` replicates
            // the case once per arm.  Our `simplify_system_with_fanout`
            // mirrors that, returning N systems.  Each is then cleaned
            // (renamePrecise + clear subst) per HS's `cleanup`.
            //
            // Kill switch: `TAM_RS_DISABLE_SIMPLIFY_FANOUT=1` falls back
            // to the in-place behaviour (returns a single-element vec).
            let simplify = |sys: System| -> Vec<System> {
                if dbg_solve {
                    eprintln!("[solve] simplify start (nodes={} goals={})",
                        sys.nodes.len(), sys.goals.len());
                }
                let t0 = std::time::Instant::now();
                let raw_systems: Vec<System> =
                    if std::env::var("TAM_RS_DISABLE_SIMPLIFY_FANOUT").is_ok() {
                        let mut r = Reduction::new(ctx, sys);
                        simplify_system(&mut r);
                        vec![r.sys]
                    } else {
                        crate::constraint::solver::simplify::simplify_system_with_fanout(ctx, sys)
                    };
                if dbg_solve {
                    eprintln!("[solve] simplify done {:?} (n_systems={})",
                        t0.elapsed(), raw_systems.len());
                }
                // Cleanup each surviving system per HS
                // `cleanup` (ProofMethod.hs:443-444):
                //   cleanup s = L.set sSubst emptySubst
                //                       (renamePrecise s)
                let mut out: Vec<System> = Vec::with_capacity(raw_systems.len());
                for mut s in raw_systems {
                    if std::env::var("TAM_DISABLE_RENAME_PRECISE").is_err() {
                        crate::constraint::solver::rename_precise::rename_precise_system(
                            &mut s);
                    }
                    if !s.eq_store.is_false() {
                        s.invalidate_max_var_idx_cache();
                        s.eq_store.subst =
                            tamarin_term::subst::Subst::from_list(Vec::new());
                    }
                    out.push(s);
                }
                out
            };
            // Filter cases the same way Haskell's `runReduction` does:
            // when a CR-rule called `contradictoryIf` during simplify
            // (e.g. solveFactEqs / solveRuleEqs / solveSubstEqs hitting
            // an incompatible unification, or Maude returning the empty
            // unifier set on a sort/tag mismatch), the Disj entry for
            // that case becomes `mzero` and disappears.  In our port
            // these failures surface as `Contradiction::IncompatibleEqs`
            // (eq_store.is_false / sort-conflation / edge-tag mismatch).
            // We mirror Haskell by pruning only those cases.
            //
            // Cases with *other* contradictions (FormulasFalse, Cyclic,
            // NodeAfterLast, …) survive `runReduction` in Haskell and
            // are picked up by the next iteration's contradictions
            // check as explicit `Finished(Contradictory(_))` leaves.
            // Do *not* filter those here, or the proof tree loses
            // siblings whose contradiction reason Haskell renders.
            // Filter cases where the eq_store has been marked false.
            // This is the most-direct Haskell-faithful proxy for `mzero`
            // from `contradictoryIf` during simplify (the eq-store flips
            // to false when solveSubstEqs/solveTermEqs/solveFactEqs hit
            // an incompatible unification, or when Maude returns the
            // empty unifier set).  Other `Contradiction`-list signals
            // (sort-conflation, edge-fact-tag mismatch, Cyclic, …) are
            // post-simplify detections in our port — Haskell either
            // catches them earlier (before the case is even built) or
            // leaves them as explicit `Finished(Contradictory(_))`
            // leaves.  Mirror the latter shape by *not* filtering them.
            let dbg_filter = std::env::var("TAM_DBG_FILTER").is_ok();
            let dbg_filter_compact = std::env::var("TAM_DBG_FILTER_COMPACT").is_ok();
            let keep = |sys: &System, name: &str| -> bool {
                let r = !sys.eq_store.is_false();
                if dbg_filter {
                    let cs = crate::constraint::solver::contradictions::contradictions(ctx, sys);
                    eprintln!("[filter] goal={:?} case={:?} eqf={} contradictions={:?} keep={}",
                        g, name, sys.eq_store.is_false(), cs, r);
                }
                if dbg_filter_compact {
                    let cs = crate::constraint::solver::contradictions::contradictions(ctx, sys);
                    let cpath = crate::constraint::solver::trace::case_path_string();
                    let goal_short = match g {
                        crate::constraint::constraints::Goal::Action(i, fa) =>
                            format!("Action(#{}.{}, {:?}/{}args)", i.name, i.idx, fa.tag, fa.terms.len()),
                        crate::constraint::constraints::Goal::Premise((i, p), fa) =>
                            format!("Premise(#{}.{}@{}, {:?}/{}args)", i.name, i.idx, p.0, fa.tag, fa.terms.len()),
                        crate::constraint::constraints::Goal::Chain(_,_) => "Chain".to_string(),
                        crate::constraint::constraints::Goal::Split(_) => "Split".to_string(),
                        crate::constraint::constraints::Goal::Disj(_) => "Disj".to_string(),
                        crate::constraint::constraints::Goal::Subterm(_) => "Subterm".to_string(),
                    };
                    eprintln!("[filtercomp] path={} goal={} case={} contras={:?} keep={}",
                        cpath, goal_short, name, cs, r);
                }
                let op = if r { "case_keep" } else { "case_drop" };
                crate::state_trace::emit_case(op, name, Some(&g), sys);
                r
            };
            match outcome {
                GoalCases::Linear => {
                    let systems = simplify(r.sys);
                    let mut out = Vec::new();
                    for s in systems {
                        if keep(&s, "") { out.push(("".to_string(), s)); }
                    }
                    Some(out)
                }
                GoalCases::LinearNamed(name) => {
                    let systems = simplify(r.sys);
                    let mut out = Vec::new();
                    for s in systems {
                        if keep(&s, &name) { out.push((name.clone(), s)); }
                    }
                    Some(out)
                }
                GoalCases::Cases(cases) => {
                    // De-duplicate identical case names by appending
                    // `_case_1`/`_case_2`/... — mirrors Haskell's
                    // `groupSortOn casName` printing convention
                    // (e.g. `R_1_case_1`, `R_1_case_2` for two
                    // distinct unifications against rule `R_1`).
                    //
                    // The dedup must run on the *kept* cases only.  If
                    // we count before `keep` and one of two `Create`
                    // cases gets dropped (e.g. eq_store false after
                    // simplify), we end up with a lone `Create_case_1`
                    // where Haskell shows a bare `Create` — a pure
                    // naming divergence with no proof-shape difference.
                    // So: simplify + keep first, then dedup the
                    // survivors.
                    //
                    // **Order preservation**: Vec<(name, sys)> output
                    // preserves the order from `dispatch_solve_goal`,
                    // which matches Haskell's `disjunctionOfList`
                    // iteration order (rule order in `joinAllRules`).
                    use std::collections::HashMap;
                    // simplify can fan out per case — flat-map.
                    // For debugging (TAM_DBG_FILTER_COMPACT), tag the case
                    // path with the sibling name + index so traces map back
                    // to the specific source-case being simplified.
                    let trace_cases = std::env::var("TAM_DBG_TRACE_CASES").is_ok();
                    let dbg_kr = std::env::var("TAM_RS_DBG_KEPT_RAW").is_ok();
                    let mut kr_pre_counts: std::collections::HashMap<String, (usize, usize, usize)>
                        = std::collections::HashMap::new();
                    let kept_raw: Vec<(String, System)> = cases.into_iter()
                        .enumerate()
                        .flat_map(|(idx, (name, sys))| {
                            if trace_cases {
                                crate::constraint::solver::trace::case_path_push(
                                    &format!("cand_{}_{}", idx, name));
                            }
                            let systems = simplify(sys);
                            let n_pre_keep = systems.len();
                            let out: Vec<(String, System)> = systems.into_iter()
                                .filter(|s| keep(s, &name))
                                .map(|s| (name.clone(), s))
                                .collect();
                            let n_post_keep = out.len();
                            if dbg_kr {
                                let entry = kr_pre_counts.entry(name.clone()).or_insert((0,0,0));
                                entry.0 += 1; // incoming cases
                                entry.1 += n_pre_keep; // post-simplify
                                entry.2 += n_post_keep; // post-keep
                            }
                            if trace_cases {
                                crate::constraint::solver::trace::case_path_pop();
                            }
                            out
                        })
                        .collect();
                    if dbg_kr {
                        let cpath = crate::constraint::solver::trace::case_path_string();
                        let goal_short = match g {
                            crate::constraint::constraints::Goal::Action(_, fa) =>
                                format!("Action({:?})", fa.tag),
                            crate::constraint::constraints::Goal::Premise(_, fa) =>
                                format!("Premise({:?})", fa.tag),
                            _ => format!("{:?}", g),
                        };
                        eprintln!("[KEPT_RAW] path={} goal={} counts={:?}",
                            cpath, goal_short, kr_pre_counts);
                    }
                    // Dedup cases that share BOTH a name and canonical
                    // system (post-simplify + rename_precise).  Haskell's
                    // `someRuleACInst` encodes rule variants as a SplitG
                    // disjunction on the eq-store, so `solveAction`
                    // returns ONE case per rule with variants threaded
                    // through SplitG; our legacy expansion enumerates
                    // each variant as a separate `RuleACInst`.  When
                    // multiple variants converge to the same post-
                    // simplify canonical system, drop the duplicates —
                    // that's the structural-match win for NSPK3/NSLPK3/
                    // roles `case R_1` (vs our prior `case R_1_case_1`).
                    let kept: Vec<(String, System)> = {
                        // Dedup by (case_name, exact-system) — catches
                        // cases where two distinct rule unifications
                        // produce structurally-identical post-simplify
                        // systems.  Safety guard for actually-isomorphic
                        // cases; the proper Haskell-parity dedup is the
                        // SplitG-variants path (now always on).
                        let dbg_dedup = std::env::var("TAM_RS_DBG_NAMESYS_DEDUP").is_ok();
                        let mut seen_systems: Vec<(String, System)> = Vec::new();
                        let mut dup_count = 0usize;
                        let mut dup_names: Vec<String> = Vec::new();
                        for (name, s) in kept_raw {
                            let dup = seen_systems.iter().any(|(prev_name, prev_sys)|
                                prev_name == &name && prev_sys == &s);
                            if !dup {
                                seen_systems.push((name, s));
                            } else {
                                dup_count += 1;
                                if dbg_dedup { dup_names.push(name); }
                            }
                        }
                        if dbg_dedup && dup_count > 0 {
                            eprintln!("[NAMESYS_DEDUP] dropped={} names={:?} kept={}",
                                dup_count, dup_names, seen_systems.len());
                        }
                        // HS-faithful `removeRedundantCases ctxt [] snd`
                        // (ProofMethod.hs:455).  Gated on BP/MSet per HS
                        // short-circuit.  Empty stable_vars (HS passes `[]`).
                        // No-op outside BP/MSet by `remove_redundant_cases`'s
                        // own guard.
                        let msig = ctx.maude.maude_sig();
                        let empty_stable: std::collections::BTreeSet<tamarin_term::lterm::LVar>
                            = std::collections::BTreeSet::new();
                        crate::constraint::solver::sources::remove_redundant_cases(
                            msig.enable_bp,
                            msig.enable_mset,
                            &empty_stable,
                            |c| &c.1,
                            seen_systems,
                        )
                    };
                    let mut counts: HashMap<String, usize> = HashMap::new();
                    for (name, _) in &kept {
                        *counts.entry(name.clone()).or_default() += 1;
                    }
                    let mut seen: HashMap<String, usize> = HashMap::new();
                    let mut out = Vec::new();
                    for (name, s) in kept.into_iter() {
                        let total = counts[&name];
                        let key = if total > 1 {
                            let n = seen.entry(name.clone()).or_default();
                            *n += 1;
                            // HS-faithful zero-padding: ProofMethod.hs:485-490
                            //   distinguish n =
                            //     [ (\(x,y) -> (... x ++ "_case_" ++ pad (show i), y))
                            //     | i <- [(1::Int)..] ]
                            //     where l      = length (show n)
                            //           pad cs = replicate (l - length cs) '0' ++ cs
                            // For total<10 width=1 (no padding); total>=10 width=2 ("01"..);
                            // total>=100 width=3, etc.
                            let width = total.to_string().len();
                            format!("{}_case_{:0width$}", name, *n, width = width)
                        } else {
                            name
                        };
                        out.push((key, s));
                    }
                    Some(out)
                }
                GoalCases::Contradictory => Some(Vec::new()),
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
            // HS-faithful: mirror Haskell's `induction` (ProofMethod.hs:521-525):
            //   induction (baseCase, stepCase) = do
            //     (caseName, caseFormula) <- disjunctionOfList
            //         [("empty_trace", baseCase), ("non_empty_trace", stepCase)]
            //     L.setM sFormulas (S.singleton caseFormula)
            //     return caseName
            // HS uses `setM` — direct field write into `sFormulas`, NOT
            // `insertFormula`.  Calling `insertFormula` here would route
            // through HS's GDisj arm (Reduction.hs:529-543) which adds the
            // empty DisjG goal to `sGoals`; HS's `reduceFormulas`
            // (Simplify.hs:426-433) filters by `reducibleFormula`
            // (Reduction.hs:589-597) which returns False for `GDisj _`, so
            // an `empty_trace` formula `Disj([])` (gfalse) stays in
            // `sFormulas` untouched and never produces a DisjG goal —
            // `FormulasFalse` contradiction picks it up directly.
            // Before this fix, RS called `insert_formula(base)` which for
            // `Disj([])` (empty_trace's base case) inserted an empty
            // DisjG goal at gsNr=0, shifting every subsequent gsNr in
            // every sibling branch and producing a divergent goal
            // sequence vs HS at the very first insertGoal call.
            let mut base_sys = sys.clone();
            base_sys.invalidate_max_var_idx_cache();
            base_sys.formulas.clear();
            base_sys.formulas.push(base);
            let mut br = Reduction::new(ctx, base_sys);
            simplify_system(&mut br);

            let mut step_sys = sys.clone();
            step_sys.invalidate_max_var_idx_cache();
            step_sys.formulas.clear();
            step_sys.formulas.push(step);
            let mut sr = Reduction::new(ctx, step_sys);
            simplify_system(&mut sr);

            // HS-faithful `cleanup` (ProofMethod.hs:453-468): induction is
            //   `Induction -> process . induction <$> getInductionCases sys`
            // (ProofMethod.hs:428), and `process`/`processLabeled` apply
            //   `map (fmap cleanup . fst)` (ProofMethod.hs:456) where
            //   cleanup s = L.set sSubst emptySubst
            //                 (Precise.evalFresh (renamePrecise s) nothingUsed)
            // So EVERY surviving induction case is renamePrecise'd with an
            // empty per-name Precise fresh supply, then has its substitution
            // cleared.  Without this, the IH disjunction's free vars (opened
            // from the `Ex` IH via global-counter freshLVar during simplify)
            // keep their high `.N` indices (e.g. `last(#z.7)`) instead of the
            // canonical per-name idx-0 form (`last(#z)`) HS renders.
            let cleanup = |s: &mut System| {
                if std::env::var("TAM_DISABLE_RENAME_PRECISE").is_err() {
                    crate::constraint::solver::rename_precise::rename_precise_system(s);
                }
                s.invalidate_max_var_idx_cache();
                s.eq_store.subst =
                    tamarin_term::subst::Subst::from_list(Vec::new());
            };
            cleanup(&mut br.sys);
            cleanup(&mut sr.sys);

            Some(vec![
                ("empty_trace".to_string(), br.sys),
                ("non_empty_trace".to_string(), sr.sys),
            ])
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
) -> Option<Vec<(CaseName, System)>> {
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
        ProofMethod::RawSolve(_) => return None,
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
        // Force the system out of its initial state by recording a
        // solved formula (Haskell `isInitialSystem` checks
        // `solved_formulas.is_empty() && no_gfalse`; setting one to
        // gtrue makes the system non-initial).
        s.solved_formulas.push(crate::guarded::gtrue());
        // Add a placeholder node too so the structure is non-trivial.
        let nid = tamarin_term::lterm::LVar::new("i", tamarin_term::lterm::LSort::Node, 0);
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
        // Build with close_guarded so the binder's `k` and `i` are
        // properly substituted to `Bound` in the guard atom.
        let fm = crate::guarded::close_guarded(
            crate::guarded::Quant::Ex,
            vec![
                VarSpec { name: "k".into(), idx: 0, sort: SortHint::Msg, typ: None },
                VarSpec { name: "i".into(), idx: 0, sort: SortHint::Node, typ: None },
            ],
            vec![action_atom],
            body,
        );
        let mut s = System::empty();
        s.formulas.push(fm);
        let r = exec_proof_method(&ctx, &ProofMethod::Induction, &s).expect("induction");
        // Two case names: empty_trace and non_empty_trace.
        assert_eq!(r.len(), 2);
        assert!(r.iter().any(|(n, _)| n == "empty_trace"));
        assert!(r.iter().any(|(n, _)| n == "non_empty_trace"));
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
