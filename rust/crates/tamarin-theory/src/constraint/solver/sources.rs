//! Skeleton port of `Theory.Constraint.Solver.Sources`.
//!
//! Sources represent the big-step proofs computing the possible
//! sources of a fact in a constraint system. The full Haskell module
//! handles:
//!
//! - Precomputing source distinctions for every protocol rule's
//!   premises (`precomputeSources`).
//! - Refining sources with source-assumption lemmas
//!   (`refineWithSourceAsms`).
//! - Solving a goal by application of a precomputed source
//!   (`solveWithSource`).
//! - Removing redundant cases (`removeRedundantCases`).
//!
//! The Rust port currently exposes the public data shapes and the
//! `IntegerParameters` config. The actual source-precomputation logic
//! depends on the full reduction loop and AC unification, which we'll
//! wire in incrementally.

use crate::constraint::system::System;

// =============================================================================
// Precompute-mode marker
// =============================================================================
//
// `solve_premise_goal` reads this flag to decide between full
// `exploit_prems` (precompute) and `exploit_prems_supplier_only`
// (runtime).  Set from `precompute_full_sources` for the duration of
// the precomputation; cleared on exit.  Mirrors how Haskell's
// `precomputeSources` runs the reducer in a fixed mode that records
// every dangling premise, then `saturateSources` resolves them.

thread_local! {
    static IN_PRECOMPUTE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub fn in_precompute_mode() -> bool {
    IN_PRECOMPUTE.with(|c| c.get())
}

fn set_precompute_mode(v: bool) {
    IN_PRECOMPUTE.with(|c| c.set(v));
}

/// Solver-tuning parameters mirroring Haskell's `IntegerParameters`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerParameters {
    /// Maximum number of open destruction chains a single proof may
    /// carry before bailing.
    pub open_chains_limit: i64,
    /// Maximum saturation iterations during source refinement.
    pub saturation_limit: i64,
    /// Whether to log each saturation step (debug aid).
    pub show_saturation_steps: bool,
}

impl Default for IntegerParameters {
    fn default() -> Self {
        // Defaults match Haskell's `defaultIntegerParameters`.
        IntegerParameters {
            open_chains_limit: 10,
            saturation_limit: 5,
            show_saturation_steps: false,
        }
    }
}

/// Number of unsolved-chain constraints in the system. Mirrors
/// `unsolvedChainConstraints`.
pub fn unsolved_chain_constraints(sys: &System) -> usize {
    use crate::constraint::constraints::Goal;
    sys.goals.iter()
        .filter(|(g, status)| !status.solved && matches!(g, Goal::Chain(_, _)))
        .count()
}

/// `Source` — one precomputed case distinction. The Haskell version
/// is `Source { _cdGoal :: Goal, _cdCases :: Disj (M.Map CaseName System) }`.
/// We carry the open shape until the reduction port can populate it.
#[derive(Debug, Clone, PartialEq)]
pub struct Source {
    pub goal: crate::constraint::constraints::Goal,
    pub cases: Vec<(String, System)>,
    /// `true` iff case enumeration was truncated by the per-source cap
    /// (`TAM_MAX_CLOSURES_PER_SOURCE`).  Search must not return
    /// `Verified` for any proof tree that consumed an incomplete
    /// source — the dropped cases could contain attack witnesses.
    /// Used to prevent wrong-VERIFIED on user-equation files where the
    /// destructor-chain explosion forces truncation.
    pub incomplete: bool,
}

impl Source {
    pub fn new(goal: crate::constraint::constraints::Goal) -> Self {
        Source { goal, cases: Vec::new(), incomplete: false }
    }
}

/// `precomputeSources` (lite). For each non-K conclusion fact across
/// the proof context's rules, count how many rules produce it. A
/// "unique-source" fact (exactly one producer) yields a `Source` with
/// the producing rule pre-attached. The solver can use these to cut
/// short the candidate enumeration in `solve_premise_goal`.
///
/// The full Haskell version runs the reduction loop on each rule's
/// premises to compute every reachable case-distinction. We currently
/// only emit the structural one-rule-one-source mapping, which is
/// enough to recover most leaf-rule premises (Fr/In/KU/Out producers).
pub fn precompute_sources(
    _params: &IntegerParameters,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<UniqueSource> {
    use std::collections::BTreeMap;
    let mut counts: BTreeMap<crate::fact::FactTag, u32> = BTreeMap::new();
    for o in &ctx.rules {
        for c in &o.rule.conclusions {
            *counts.entry(c.tag.clone()).or_insert(0) += 1;
        }
    }
    let mut out = Vec::new();
    for o in &ctx.rules {
        for c in &o.rule.conclusions {
            if counts.get(&c.tag).copied() == Some(1) {
                out.push(UniqueSource {
                    fact_tag: c.tag.clone(),
                    rule_name: o.name().to_string(),
                });
            }
        }
    }
    // Dedup.
    out.sort_by(|a, b| a.fact_tag.cmp(&b.fact_tag));
    out.dedup_by(|a, b| a.fact_tag == b.fact_tag);
    out
}

/// One precomputed source: a fact tag whose only producer is the
/// named rule. Lets `solve_premise_goal` short-circuit instead of
/// enumerating all candidates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UniqueSource {
    pub fact_tag: crate::fact::FactTag,
    pub rule_name: String,
}

/// `precomputeSources` (full).  Direct port of Haskell's
/// `Theory.Constraint.Solver.Sources.precomputeSources`, restricted
/// to *initial* sources (no saturation pass — we run one level of
/// case enumeration and rely on subsequent runtime expansion to
/// resolve any dangling subgoals).
///
/// For each non-special protocol-fact tag, build an abstract premise
/// goal `PremiseG (i, 0) (Fact tag (t1..tk))`, run `solve_premise_goal`
/// once on a fresh empty system, and collect the resulting cases.
/// The result is one `Source` per tag, with the goal as key and the
/// per-rule cases as the disjunction.
///
/// At runtime, `solve_premise_goal` consults this cache before
/// enumerating rules: the precomputed cases let the search graft a
/// pre-instantiated subsystem rather than re-deriving it every time.
pub fn precompute_full_sources(
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{Reduction, GoalCases};
    use crate::fact::{Fact, FactTag, fact_tag_arity};
    use crate::rule::PremIdx;

    use std::collections::BTreeSet;
    let mut tags: BTreeSet<FactTag> = BTreeSet::new();
    for o in &ctx.rules {
        for fa in o.rule.premises.iter().chain(o.rule.conclusions.iter()) {
            if matches!(&fa.tag, FactTag::Proto(_, _, _)) {
                tags.insert(fa.tag.clone());
            }
        }
    }

    set_precompute_mode(true);
    let mut out: Vec<Source> = Vec::new();
    // -----------------------------------------------------------------
    // protoGoals — PremiseG for each proto-fact tag seen in the rules.
    // Mirrors Haskell's protoGoals branch of `precomputeSources`.
    // -----------------------------------------------------------------
    for tag in tags {
        let arity = fact_tag_arity(&tag);
        let goal_node = tamarin_term::lterm::LVar::new(
            "i", tamarin_term::lterm::LSort::Node, 0);
        let terms: Vec<tamarin_term::lterm::LNTerm> = (0..arity)
            .map(|i| tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
                tamarin_term::lterm::LVar::new(
                    "t", tamarin_term::lterm::LSort::Msg, (i + 1) as u64))))
            .collect();
        let abstract_fact = Fact::new(tag.clone(), terms);
        let goal = Goal::Premise(
            (goal_node.clone(), PremIdx(0)), abstract_fact.clone());

        // Haskell-faithful: inject the theory's restrictions into each
        // case-system before saturate.  Mirrors `initialSource ctxt
        // restrictions goal` (Sources.hs:102):
        //   se0 = insertLemmas restrictions $ emptySystem RawSource ...
        // Restrictions then fire on rule actions during saturate, so
        // e.g. `True_is_true` on Responder's `IsTrue(z)` action forces
        // z=true and drops cases whose variant subst doesn't satisfy
        // that constraint.
        let mut sys = System::empty();
        sys.insert_lemmas(ctx.restrictions.clone());
        let mut red = Reduction::new(ctx, sys);
        red.insert_goal(goal.clone());
        // Haskell-faithful: mark the goal as solved BEFORE invoking the
        // solver.  Mirrors `solveGoal` (Goals.hs:201-213):
        //   solveGoal goal = do
        //       -- mark before solving, as representation might change
        //       -- due to unification
        //       markGoalAsSolved "directly" goal
        //       ...
        // Without this, `solve_fact_eqs` running inside `solve_premise_goal`
        // can rewrite the goal's fact terms (e.g. Check0's repeated-arg
        // `Loop(loopId, kOrig, kOrig)` unification rewrites the abstract
        // `Loop(t1, t2, t3)` to `Loop(t1, t2, t2)`), after which a post-
        // solve mark using the original goal misses the (now substituted)
        // entry in the map.  The unmarked goal then triggers spurious
        // re-graft in `saturate_sources_inner_with_options`, adding a
        // duplicate producing-rule instance (task #222).
        red.mark_goal_as_solved(&goal);
        let outcome = red.solve_premise_goal(
            &(goal_node.clone(), PremIdx(0)),
            &abstract_fact);
        // Propagate eq-store substitution into nodes/edges/goals for
        // each case before saving — without this, the case stores its
        // rules' original vars (e.g., `x_1`) while the abstract terms
        // (`t_1`) live only in the eq-store.  Saturation needs the
        // unified form so its substitution can rewrite the rule vars
        // to match the outer case's premise term.
        // Mirror Haskell's `refineSource` (Sources.hs:118-124):
        //   newCases = map (modify sSubst (restrict stableVars)) cases
        // After applying the eq-store via substSystem, drop any
        // bindings whose KEY is not in `frees (cdGoal th)`.  This
        // prevents the rule-internal var → abstract-var bindings
        // from chaining at runtime when applySource adds a new
        // abstract-var binding.
        let stable_vars = stable_vars_for_goal(&goal);
        // Haskell `initialSource` runs `runReduction (instantiate)` whose
        // `Disj` monad mzeros out any case whose embedded `contradictoryIf`
        // fires inside `solveGoal` / `simplifySystem`.  Mirror that by
        // running `simplify_system` then dropping cases that turn
        // contradictory.  Without this, destructor-chain branches whose
        // `Secret(I,R,x:Msg)` (or similar) is incompatible with a pre-
        // existing fresh-binding survive precompute and produce stray
        // `_case_2` siblings at runtime (Bug 2 from agent ab16c432c4c2).
        let normalize_and_keep = |sys: System, _case_name: &str| -> Option<System> {
            let mut r = Reduction::new(ctx, sys);
            r.sys.insert_lemmas(ctx.restrictions.clone());
            r.subst_system();
            crate::constraint::solver::simplify::simplify_system(&mut r);
            if r.sys.eq_store.is_false() { return None; }
            if !crate::constraint::solver::contradictions::contradictions(ctx, &r.sys)
                .is_empty()
            { return None; }
            let mut s = r.sys;
            restrict_eq_store_to_stable_vars(&mut s, &stable_vars);
            Some(s)
        };
        let cases: Vec<(String, System)> = match outcome {
            GoalCases::Linear => normalize_and_keep(red.sys, "only")
                .map(|s| vec![("only".into(), s)]).unwrap_or_default(),
            GoalCases::LinearNamed(name) => {
                let name_cloned = name.clone();
                normalize_and_keep(red.sys, &name_cloned)
                    .map(|s| vec![(name, s)]).unwrap_or_default()
            }
            GoalCases::Cases(systems) => systems.into_iter()
                .filter_map(|(name, s)| {
                    let n = name.clone();
                    normalize_and_keep(s, &n).map(|s| (name, s))
                })
                .collect(),
            GoalCases::Contradictory => Vec::new(),
        };
        if cases.is_empty() { continue; }
        out.push(Source { goal, cases, incomplete: false });
    }

    // -----------------------------------------------------------------
    // msgGoals — ActionG for KU(t) over each non-trivial function
    // symbol head + a Fresh-sorted variable.  Mirrors Haskell's
    // `msgGoals = someKUGoal <$> absMsgFacts`.
    //
    // The cases produced by `solve_action_goal` for an abstract
    // `KU(t)` give the full enumeration of how the adversary derives
    // a term of that shape — including the recursive saturate-driven
    // chain.  At runtime, `solve_with_source_cases_action` (added
    // below) matches a live KU goal against these.
    // -----------------------------------------------------------------
    let goal_node = tamarin_term::lterm::LVar::new(
        "i", tamarin_term::lterm::LSort::Node, 0);
    let mut ku_patterns: Vec<tamarin_term::lterm::LNTerm> = Vec::new();
    // Fresh-sorted singleton: KU(t:Fresh).  This is the pattern that
    // gates the chain for protocol-fresh values like ~ni, ~nr, ~ltk.
    ku_patterns.push(tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
        tamarin_term::lterm::LVar::new(
            "t", tamarin_term::lterm::LSort::Fresh, 1))));
    // Per-function-symbol applications.  Use Msg-sorted arg vars.
    // Mirrors Haskell `absMsgFacts`: only Constructor-flavoured
    // irreducible symbols of arity ≥ 1, excluding implicit DH/pair
    // symbols.
    let msig = ctx.maude.maude_sig();
    for sym in &msig.irreducible_fun_syms {
        if let tamarin_term::function_symbols::FunSym::NoEq(noeq) = sym {
            // Private nullary symbols still need a source case (the
            // intruder learns them only via protocol rules that
            // output them).  Public nullary symbols are auto-solved
            // by `is_nullary_public_function`, but including them
            // here is harmless: their source case enumeration will
            // typically be empty (no protocol rule outputs them in
            // a useful way) and `cases.is_empty()` skips the entry.
            if noeq.constructability
                != tamarin_term::function_symbols::Constructability::Constructor
            { continue; }
            // Skip implicit function symbols (pair/fst/snd/inv/one) —
            // these have their own structural handling in the solver.
            let name = String::from_utf8_lossy(&noeq.name);
            if matches!(name.as_ref(),
                "pair" | "fst" | "snd" | "inv" | "1") { continue; }
            let args: Vec<tamarin_term::lterm::LNTerm> = (0..noeq.arity)
                .map(|i| tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
                    tamarin_term::lterm::LVar::new(
                        "t", tamarin_term::lterm::LSort::Msg, (i + 1) as u64))))
                .collect();
            ku_patterns.push(tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::NoEq(noeq.clone()),
                args));
        }
    }
    for pat in ku_patterns {
        let ku_fact = crate::fact::ku_fact(pat.clone());
        let goal = Goal::Action(goal_node.clone(), ku_fact.clone());
        // Haskell-faithful: inject restrictions (see protoGoals branch).
        let mut sys = System::empty();
        sys.insert_lemmas(ctx.restrictions.clone());
        let mut red = Reduction::new(ctx, sys);
        red.insert_goal(goal.clone());
        // Haskell-faithful mark-before-solve (Goals.hs:201-213).  See
        // proto-goals branch above for full justification.
        red.mark_goal_as_solved(&goal);
        let outcome = red.solve_action_goal(&goal_node, &ku_fact);
        // Haskell `refineSource` restrict (Sources.hs:118-124).
        let stable_vars = stable_vars_for_goal(&goal);
        // Haskell `initialSource` runs `runReduction (instantiate)` whose
        // `Disj` monad mzeros out any case whose embedded `contradictoryIf`
        // fires inside `solveGoal` / `simplifySystem`.  Mirror that by
        // running `simplify_system` then dropping cases that turn
        // contradictory.  Without this, destructor-chain branches whose
        // `Secret(I,R,x:Msg)` (or similar) is incompatible with a pre-
        // existing fresh-binding survive precompute and produce stray
        // `_case_2` siblings at runtime (Bug 2 from agent ab16c432c4c2).
        let normalize_and_keep = |sys: System, _case_name: &str| -> Option<System> {
            let mut r = Reduction::new(ctx, sys);
            // Re-inject restrictions (see proto branch above).
            r.sys.insert_lemmas(ctx.restrictions.clone());
            r.subst_system();
            crate::constraint::solver::simplify::simplify_system(&mut r);
            if r.sys.eq_store.is_false() { return None; }
            if !crate::constraint::solver::contradictions::contradictions(ctx, &r.sys)
                .is_empty()
            { return None; }
            let mut s = r.sys;
            restrict_eq_store_to_stable_vars(&mut s, &stable_vars);
            Some(s)
        };
        let cases: Vec<(String, System)> = match outcome {
            GoalCases::Linear => normalize_and_keep(red.sys, "only")
                .map(|s| vec![("only".into(), s)]).unwrap_or_default(),
            GoalCases::LinearNamed(name) => {
                let n2 = name.clone();
                normalize_and_keep(red.sys, &n2)
                    .map(|s| vec![(name, s)]).unwrap_or_default()
            }
            GoalCases::Cases(systems) => systems.into_iter()
                .filter_map(|(name, s)| {
                    let n2 = name.clone();
                    normalize_and_keep(s, &n2).map(|s| (name, s))
                })
                .collect(),
            GoalCases::Contradictory => Vec::new(),
        };
        if cases.is_empty() { continue; }
        out.push(Source { goal, cases, incomplete: false });
    }

    set_precompute_mode(false);
    out
}

/// `saturateSources` (lite). Direct port of Haskell's
/// `Theory.Constraint.Solver.Sources.saturateSources`, restricted to
/// the *expansion* loop: each iteration walks every case of every
/// source, finds the first open protocol-fact premise goal, and
/// expands it by grafting each matching source's cases.  Stops after
/// `limit` iterations or when no case changes.
///
/// After saturation, cases that still carry open protocol-fact
/// premises are dropped — they represent un-folded recursive chains
/// that exceed the saturation budget.  Self-contained cases (no
/// dangling premises) survive and are safe to graft at runtime.
///
/// Note: only protocol-fact premise goals are expanded.  KU/KD/Action
/// goals are left for runtime to handle.
pub fn saturate_sources(
    sources: Vec<Source>,
    limit: usize,
) -> Vec<Source> {
    saturate_sources_inner(sources, limit, None)
}

/// Lightweight saturator that uses the Maude ctx ONLY for intruder-
/// chain folding (Out / KD premise resolution), not for Proto-premise
/// alignment.  At context init we want the Maude-backed chain fold
/// (so `case coerce` / `case irecv` collapse into `case <protocol>`)
/// while keeping the lightweight order-sorted aligner for Proto
/// premises (the Maude alignment there over-merges cases).
pub fn saturate_sources_with_chain_fold(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    saturate_sources_inner_with_options(
        sources, limit, /* maude_align */ None, /* fold_ctx */ Some(ctx))
}

/// Maude-backed variant of [`saturate_sources`].  Mirrors Haskell's
/// `saturateSources` by running each saturation step's graft through
/// Maude AC-unification, so order-sorted narrowing (Pub/Fresh ⊂ Msg)
/// applies correctly at precompute time — not just at runtime.
pub fn saturate_sources_maude(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    saturate_sources_inner(sources, limit, Some(ctx))
}

/// Helper: `true` iff `sys` has an unsolved `Chain(c, p)` whose
/// start term has a fixed non-Msg sort (Fresh/Pub/Nat) and whose
/// end term is App-headed.  Such a chain can never close: no
/// destructor rule maps a Fresh/Pub/Nat-sorted value to a function
/// application of a different head, and direct unification
/// (Fresh ⊆ Msg vs senc-shape) fails.
///
/// Mirrors the **shape-level** impossibility that Haskell catches
/// via its lazy `Disj`-monad backtracking inside `refineSource` —
/// Haskell's `solveAllSafeGoals` extends the chain via destructors
/// and `mzero`s when no extension is viable.  Our saturate keeps
/// the chain open, so we need an explicit drop here.
fn case_has_impossible_open_chain(
    sys: &crate::constraint::system::System,
) -> bool {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    for (g, st) in &sys.goals {
        if st.solved { continue; }
        let Goal::Chain(c, p) = g else { continue; };
        let c_rule = sys.nodes.iter().find(|(id, _)| id == &c.0).map(|(_, r)| r);
        let p_rule = sys.nodes.iter().find(|(id, _)| id == &p.0).map(|(_, r)| r);
        let (Some(c_rule), Some(p_rule)) = (c_rule, p_rule) else { continue };
        let Some(conc_fact) = c_rule.conclusions.get(c.1.0) else { continue };
        let Some(prem_fact) = p_rule.premises.get(p.1.0) else { continue };
        if !matches!(conc_fact.tag, FactTag::Kd) { continue; }
        if !matches!(prem_fact.tag, FactTag::Kd) { continue; }
        let Some(t_start) = conc_fact.terms.first() else { continue };
        let Some(t_end) = prem_fact.terms.first() else { continue };

        // Determine t_start's "fixed sort" — Fresh/Pub/Nat (Var) or
        // Fresh constant (Lit::Con).  Msg vars don't have a fixed
        // sort.  App-headed terms are excluded (they can extend
        // via destructors of matching head).
        let t_start_fixed_sort: Option<LSort> = match t_start {
            Term::Lit(Lit::Var(v)) if !matches!(v.sort, LSort::Msg) => Some(v.sort),
            Term::Lit(Lit::Con(n)) => Some(match n.tag {
                NameTag::Pub => LSort::Pub,
                NameTag::Fresh => LSort::Fresh,
                NameTag::Nat => LSort::Nat,
                NameTag::Node => LSort::Node,
            }),
            _ => None,
        };
        let Some(_start_sort) = t_start_fixed_sort else { continue };

        // t_end must be App-headed with a different "shape" — i.e.
        // a non-trivial function application that can't accept a
        // Fresh/Pub/Nat-sorted value as its own root.  We use the
        // simplest check: t_end is an App.
        let t_end_is_app = matches!(t_end, Term::App(_, _));
        if !t_end_is_app { continue; }

        // The chain shape is incompatible.  No destructor maps
        // Fresh/Pub/Nat to an App-headed term of arbitrary shape
        // (destructors are head-specific: d_fst extracts pair
        // components, d_sdec extracts senc plaintexts, etc., all
        // requiring the input to already be App-headed of the
        // matching constructor).
        return true;
    }
    false
}

/// **Drop contradictory cases** — Haskell-faithful final filter.
///
/// After `saturateSources`, walk each source's cases and drop any
/// whose system has a `contradictions()` non-empty.  Haskell's
/// `refineSource` (Sources.hs:118-133) runs each case through the
/// `Reduction` monad whose `Disj` short-circuits via `mzero` on
/// `contradictoryIf` (Sources.hs:178 in `solveAllSafeGoals`).  A
/// case whose system is contradictory after saturation never
/// appears in `cdCases`.
///
/// Our saturate keeps cases by name but doesn't check the final
/// system for contradictions — so impossible chains (e.g. an
/// `Out(k:Fresh) → Kd(senc(...))` chain where no destructor maps
/// Fresh → senc) survive into runtime as bogus cases.  This pass
/// closes the gap.
pub fn drop_contradictory_cases(
    sources: Vec<Source>,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    // TAM_DISABLE_DROP_CONTRADICTORY=1 — bypass this Rust-specific pass
    // to compare against Haskell's behaviour, which has no equivalent
    // post-saturate drop step.  Haskell relies on saturate-time
    // `contradictoryIf` inside `solveAllSafeGoals` plus runtime
    // contradiction detection during proof search.
    if std::env::var("TAM_DISABLE_DROP_CONTRADICTORY").is_ok() {
        return sources;
    }
    let dbg = std::env::var("TAM_DBG_DROP").is_ok();
    // Iterate to fixpoint mirroring Haskell's `saturateSources` loop
    // (Sources.hs:357-385).  Each iteration, cases whose `proofStep`
    // (solveAllSafeGoals with goodTh sources) returns empty Disj are
    // dropped.  As more sources reach single-case "goodTh" status,
    // accumulated constraints can drop additional cases that survived
    // earlier iterations.
    let max_iters: usize = std::env::var("TAM_DROP_ITER_CAP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(5);
    let mut current = sources;
    for iter in 0..max_iters {
        // goodTh filter: sources with ≤1 case (Haskell's
        // `goodTh th = length (getDisj (get cdCases th)) <= 1`).
        let good_ths: Vec<Source> = current.iter()
            .filter(|s| s.cases.len() <= 1)
            .cloned()
            .collect();
        if dbg {
            eprintln!("[drop iter={}] total_sources={} good_ths.len={}",
                iter, current.len(), good_ths.len());
        }
        let before_total: usize = current.iter().map(|s| s.cases.len()).sum();
        let next: Vec<Source> = current.into_iter().map(|src| {
            let goal_str = format!("{:?}", src.goal).chars().take(80).collect::<String>();
            let cases: Vec<_> = src.cases.into_iter()
                .filter(|(name, sys)| {
                    let keep = case_has_surviving_variant_with_ths(
                        ctx, sys, &good_ths);
                    if dbg {
                        eprintln!("[drop iter={}] goal={} case={} keep={}",
                            iter, goal_str, name, keep);
                    }
                    keep
                })
                .collect();
            Source { goal: src.goal, cases, incomplete: src.incomplete }
        }).collect();
        let after_total: usize = next.iter().map(|s| s.cases.len()).sum();
        current = next;
        if before_total == after_total {
            if dbg { eprintln!("[drop] fixpoint at iter={}", iter); }
            break;
        }
    }
    current
}

fn case_has_surviving_variant_with_ths(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: &crate::constraint::system::System,
    ths: &[Source],
) -> bool {
    let dbg = std::env::var("TAM_DBG_VARIANT").is_ok();
    let mut base_sys = sys.clone();
    base_sys.insert_lemmas(ctx.restrictions.clone());
    set_precompute_mode(true);
    let branch_cap: usize = std::env::var("TAM_DROP_BRANCH_CAP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(20);
    let outer_cap: i64 = std::env::var("TAM_DROP_OUTER_CAP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(40);
    let branches = run_solve_all_safe_goals_disj(
        ctx, base_sys, ths,
        /* chains_limit */ 10,
        /* outer_cap */ outer_cap,
        /* branch_cap */ branch_cap,
        String::new());
    set_precompute_mode(false);
    if dbg {
        eprintln!("[variant_with_ths] disj-monad surviving branches={} ths.len={}",
            branches.len(), ths.len());
    }
    !branches.is_empty()
}

/// Haskell-faithful contradictory-case filter via Disj-monad
/// variant enumeration.  Mirrors `refineSource`'s
/// `runReduction proofStep ctxt se fs` (Sources.hs:131): each open
/// Split goal in the case fans out into branches; each branch runs
/// simplify; branches with contradictions mzero out.  If ALL branches
/// of a Split mzero, the entire case is contradictory and dropped.
///
/// Without this, single-pick saturate commits to the first variant
/// and misses contradictions Haskell catches via full Disj-monad
/// exploration (e.g. `True_is_true` forces z=true, but Responder's
/// variant subst maps z to and(encSucc, isPair) — incompatible with
/// every variant after Maude AC reduction).
fn case_has_surviving_variant(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: &crate::constraint::system::System,
) -> bool {
    // Haskell-faithful (Sources.hs:118-133):
    //   refinement = do (names, se) <- get cdCases th
    //                   ((x, names'), se') <- fst <$>
    //                       runReduction proofStep ctxt se fs
    //                   return (...)
    // `runReduction proofStep ctxt se fs` returns `[(result, final_sys)]`
    // — the list of all Disj-monad branches that survived `proofStep`.
    // If the list is empty, the input case (this `sys`) contributes
    // NOTHING to `newCases` ⇒ the case is dropped.
    //
    // `proofStep` is `solveAllSafeGoals (filter goodTh ths) limit`.
    // Our `run_solve_all_safe_goals_disj` is exactly this — a
    // worklist-based Disj-monad explorer that drops branches on
    // mzero (contradiction).  Return value is the list of survivors.
    //
    // So the Haskell-faithful drop test is simply: run the multi-
    // branch saturate; keep the case iff the result is non-empty.
    let dbg = std::env::var("TAM_DBG_VARIANT").is_ok();
    let mut base_sys = sys.clone();
    base_sys.insert_lemmas(ctx.restrictions.clone());
    set_precompute_mode(true);
    let branch_cap: usize = std::env::var("TAM_DROP_BRANCH_CAP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(20);
    let outer_cap: i64 = std::env::var("TAM_DROP_OUTER_CAP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(40);
    // Pass goodTh-filtered sources (≤1 case) so solveAllSafeGoals can
    // source-pick on KU action goals — matches Haskell's
    // `solveAllSafeGoals (filter goodTh ths) limit` (Sources.hs:382-383).
    // Without this, KU-action source-pick at iter 1 can't fire and the
    // destructor-chain Cyclic+ForbiddenChain contradiction Haskell catches
    // is missed.
    let good_ths: Vec<Source> = ctx.full_sources.iter()
        .filter(|s| s.cases.len() <= 1)
        .cloned()
        .collect();
    let branches = run_solve_all_safe_goals_disj(
        ctx, base_sys, &good_ths,
        /* chains_limit */ 10,
        /* outer_cap */ outer_cap,
        /* branch_cap */ branch_cap,
        String::new());
    set_precompute_mode(false);
    if dbg {
        eprintln!("[variant] disj-monad surviving branches={} good_ths.len={}",
            branches.len(), good_ths.len());
    }
    !branches.is_empty()
}

/// **Source-case-level loop-breaker** (experimental, currently
/// disabled at the call site in `context.rs`) — drop precomputed
/// cases whose nodes contain an `In(_)` premise whose term-shape
/// could narrow to the SAME source's abstract head pattern.  Such
/// cases recurse infinitely at runtime: applying the case introduces
/// an In premise of the same shape as the goal that triggered the
/// apply, so runtime search re-picks the same source, etc.
///
/// **Status (2026-05-18)**: implemented per user request to mirror
/// the intent of Haskell's `saturateSources` loop-breaker machinery
/// (`filterCases` + `solveAllSafeGoals` Disj-monad backtracking
/// inside `refineSource`).  Empirically this is **NOT** Haskell-
/// faithful: Haskell *keeps* such cases and relies on runtime
/// source ordering (alphabetical via Data.Map) to try the
/// non-looping cases first.  When applied as a hard drop, this
/// pass:
///   - does not fix Pattern_matching::Responder_secrecy (still
///     wrong-falsifies via a deeper search-completeness bug),
///   - reduces corpus skeleton-match (46→43) because Haskell's
///     proof trees reference the dropped cases.
///
/// Left in tree as documented machinery.  The real fix needs to be
/// in runtime source-case selection (`solve_with_source_cases_action`
/// + `expand` case-sort), not at saturate time.
///
/// Concretely, for a Source with goal `KU(P)` (Action goal whose
/// fact is `KU(P)` for some abstract pattern `P`), and a case
/// `(name, sys)`, we walk `sys.goals` for any open `Goal::Premise(_, fa)`
/// such that:
///   - `fa.tag ∈ { In, Ku }` (the runtime-bound input-routing facts),
///   - `fa.terms[0]`'s head shape matches `P`'s head shape:
///     - if `P` is a Var of sort S, the premise's term has sort ≤ S
///       (sort-narrowing matches),
///     - if `P = f(_,_,...)`, the premise's term is `f(_,_,...)`
///       (head-symbol + arity match).
///
/// Such a case is sound to drop: the recursion has no base case in
/// this source (no rule in the case provides the matching shape
/// without going through the In/Ku premise), so any runtime trace
/// reaching the case loops indefinitely.  Dropping cannot lose
/// witnesses — any actual attack must instead use one of the
/// surviving cases.
pub fn drop_source_case_loops(sources: Vec<Source>) -> Vec<Source> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    sources.into_iter().map(|src| {
        // Only KU-action sources participate in the runtime
        // source-pick loop.  Premise sources don't (they're matched
        // structurally per fact tag, not via `solveWithSourceAction`).
        let (pat_var_sort, pat_head_arity): (
            Option<LSort>,
            Option<(tamarin_term::function_symbols::FunSym, usize)>,
        ) = match &src.goal {
            Goal::Action(_, fa) if fa.tag == FactTag::Ku && fa.terms.len() == 1 => {
                match &fa.terms[0] {
                    Term::Lit(Lit::Var(v)) => (Some(v.sort), None),
                    Term::App(f, args) => (None, Some((f.clone(), args.len()))),
                    _ => (None, None),
                }
            }
            _ => return src,
        };
        if pat_var_sort.is_none() && pat_head_arity.is_none() {
            return src;
        }

        // A case "loops" iff at runtime it would re-derive a KU/In
        // goal of the same shape as the source's own pattern.
        // Concretely: the case must contain a NODE with an In
        // premise (which becomes a KU runtime-goal via I_Send) whose
        // term-shape could unify with the source's abstract pattern.
        //
        // We only count In premises (not Ku, not the source's own
        // abstract Action goal) — In is the runtime-routed premise
        // that triggers source enumeration; the abstract Action
        // goal isn't a sub-goal.
        let case_loops = |sys: &crate::constraint::system::System| -> bool {
            for (_nid, rule) in &sys.nodes {
                for prem in &rule.premises {
                    if prem.tag != FactTag::In { continue; }
                    let Some(term) = prem.terms.first() else { continue; };
                    let term_could_match = match (&pat_var_sort, &pat_head_arity, term) {
                        // Var pattern (e.g. KU(t:Fresh)): match by sort.
                        (Some(s), _, _) => {
                            let term_sort = sort_of_lnterm(term);
                            sort_ge(*s, term_sort)
                        }
                        // App pattern + term is App: head+arity must match.
                        (None, Some((pf, pa)), Term::App(tf, targs)) => {
                            pf == tf && *pa == targs.len()
                        }
                        // App pattern + term is Var: the var could
                        // narrow at runtime to the pattern shape iff
                        // its sort is unconstrained enough (Msg).
                        (None, Some(_), Term::Lit(Lit::Var(v))) => {
                            matches!(v.sort, LSort::Msg)
                        }
                        _ => false,
                    };
                    if term_could_match { return true; }
                }
            }
            false
        };

        let cases: Vec<_> = src.cases.into_iter()
            .filter(|(_, sys)| !case_loops(sys))
            .collect();
        Source { goal: src.goal, cases, incomplete: src.incomplete }
    }).collect()
}

fn saturate_sources_inner(
    sources: Vec<Source>,
    limit: usize,
    ctx_for_maude: Option<&crate::constraint::solver::context::ProofContext>,
) -> Vec<Source> {
    saturate_sources_inner_with_options(sources, limit, ctx_for_maude, ctx_for_maude)
}

fn saturate_sources_inner_with_options(
    sources: Vec<Source>,
    limit: usize,
    maude_align: Option<&crate::constraint::solver::context::ProofContext>,
    fold_ctx: Option<&crate::constraint::solver::context::ProofContext>,
) -> Vec<Source> {
    use std::collections::BTreeSet;
    let mut current = sources;
    // Per-case `used_sources` mirroring Haskell's `filterCases` in
    // `solveAllSafeGoals` (Sources.hs:215). Tracks which source-labels
    // the case has already consumed via KU-action expansion, so the
    // SAME source isn't re-applied to a freshly-introduced KU goal in
    // its chain.  Without this, expansion grows cyclic-redundant
    // chains like `PCR_Unbind_PCR_CreateKey_PCR_Unbind_PCR_CreateKey…`
    // and the [sources] typing assumption collapses to FormulasFalse
    // because no chain depth ever reaches the type-witnessing rule.
    let mut current_used: Vec<Vec<BTreeSet<String>>> = current.iter()
        .map(|s| vec![BTreeSet::new(); s.cases.len()])
        .collect();
    let dbg = std::env::var("TAM_DBG_SAT_ITER").is_ok();
    for iter in 0..limit {
        if dbg {
            eprintln!("=== sat iter {} ({} sources) ===", iter, current.len());
            for src in &current {
                if let crate::constraint::constraints::Goal::Action(_, fa) = &src.goal {
                    if matches!(fa.tag, crate::fact::FactTag::Ku) {
                        let term = format!("{:?}", fa.terms.first()).chars().take(60).collect::<String>();
                        eprintln!("  Ku {}: {} cases", term, src.cases.len());
                        for (n, _) in &src.cases {
                            eprintln!("    {}", n);
                        }
                    }
                }
            }
        }
        // Precompute source labels for filterCases.
        let source_labels: Vec<Option<String>> = current.iter()
            .map(source_label).collect();
        let mut next: Vec<Source> = Vec::new();
        let mut next_used: Vec<Vec<BTreeSet<String>>> = Vec::new();
        let mut changed = false;
        for (src_idx, src) in current.iter().enumerate() {
            let mut new_cases: Vec<(String, System)> = Vec::new();
            let mut new_used: Vec<BTreeSet<String>> = Vec::new();
            let mut src_incomplete = src.incomplete;
            for (case_idx, (name, sys)) in src.cases.iter().enumerate() {
                let case_used = current_used.get(src_idx)
                    .and_then(|v| v.get(case_idx)).cloned()
                    .unwrap_or_default();
                // Try intruder-chain folding first: Out / KD premises
                // get grafted onto the protocol rule that produces
                // them, collapsing nested `case coerce / case irecv
                // / case <rule>` chains into a single saturated `case
                // <rule>`.  Mirrors Haskell's `solveAllSafeGoals`
                // which iterates `solveGoal` over all safe goals
                // (including intruder premises) during saturation.
                if let Some((p, fa)) = first_open_out_premise(sys) {
                    if let Some(ctx) = fold_ctx {
                        let mut sat_incomplete = false;
                        if let Some(grafted) = saturate_out_premise(
                            ctx, sys, &p, &fa, name, &mut sat_incomplete)
                        {
                            // Saturate-time variant fanout: when the
                            // chain-folded case has a small unsolved
                            // variant SplitG, fan it out into per-arm
                            // sub-cases.  Mirrors Haskell
                            // `someRuleACInst` + `solveDisjunction`
                            // resolving `RuleACConstrs` BEFORE the
                            // saturated case is stored, so destructor
                            // chains see the variant-narrowed Fresh-
                            // typed t_start (essential for
                            // `hasImpossibleChain`'s pcTrueSubterm
                            // dispatch — Contradictions.hs:258).
                            for (sub_name, sub_sys) in grafted {
                                let arms = saturate_fanout_variant_splits(
                                    ctx, sub_sys.clone(), &sub_name);
                                match arms {
                                    Some(arm_list) => {
                                        for (arm_name, arm_sys) in arm_list {
                                            new_cases.push((arm_name, arm_sys));
                                            new_used.push(case_used.clone());
                                            changed = true;
                                        }
                                    }
                                    None => {
                                        new_cases.push((sub_name, sub_sys));
                                        new_used.push(case_used.clone());
                                        changed = true;
                                    }
                                }
                            }
                            if sat_incomplete { src_incomplete = true; }
                            continue;
                        }
                    }
                }
                // Mirror Haskell's `solveAllSafeGoals` KU-action arm
                // (Sources.hs:144-215): expand open KU action goals by
                // grafting matching source-cases from the current
                // saturating list.  Task #120.
                //
                // Crucial gate: DEFER to proto-premise expansion when
                // there's an open Proto premise.  Those need to be
                // satisfied by the proto-premise graft first (e.g.
                // !AIK ← PCR_Init) or the final filter drops the
                // case. Without this gate, KU expansion intercepts
                // Alice_Init's iteration and grafts a sign-source
                // case instead, leaving !AIK open → case dropped at
                // end.
                //
                // Each case carries `case_used: BTreeSet<SourceLabel>`
                // — the set of source labels already applied to this
                // case's lineage. We pass only UNUSED sources to the
                // KU-exp helper, mirroring Haskell's `filterCases`
                // (Sources.hs:215). Sub-cases inherit `case_used ∪
                // {label(picked source)}`, so iter N+1 can't re-apply
                // a source already used at iter ≤N.  Without this,
                // the same source keeps grafting onto its own
                // freshly-introduced KU goals → cyclic redundant
                // chains, FormulasFalse wrong-falsified, and OOM.
                //
                // Off by default behind `TAM_ENABLE_KU_EXP=1`; the
                // filterCases tracking still needs more validation on
                // the full corpus before being default-on.
                // Bound KU-exp iterations to keep saturate memory
                // tractable across the corpus.  Without a cap, even
                // filterCases-bounded chains multiply cross-source ×
                // cross-case enough to OOM on large protocols.  Tamarin
                // gets away without an explicit cap because its strict
                // `goodTh` filter (≤1 case per source) keeps the
                // saturating list small; our chain-fold path produces
                // many more cases per source than tamarin.  Cap is a
                // tunable knob; default 1 covers TPM correctly per
                // filterCases analysis.
                let ku_iter_cap: usize = std::env::var("TAM_KU_EXP_MAX_ITER")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(1);
                if std::env::var("TAM_ENABLE_KU_EXP").is_ok()
                    && iter < ku_iter_cap
                    && first_open_proto_premise(sys).is_none()
                {
                    if let Some(ctx) = fold_ctx {
                        if let Some((goal_node, fa_ku)) = first_open_ku_action_goal(sys) {
                            // Filter `current` to:
                            // (a) unused-by-this-case (filterCases),
                            // (b) `goodTh` — sources with ≤1 case
                            //     (matches Haskell `saturateSources`
                            //     Sources.hs:380, the `goodTh th =
                            //     length (getDisj (get cdCases th)) <= 1`
                            //     guard inside `solver`).  Without this
                            //     filter, multi-case sources fan out
                            //     during KU-exp and OOM the corpus.
                            let filtered: Vec<Source> = current.iter()
                                .zip(source_labels.iter())
                                .filter(|(s, _)| s.cases.len() <= 1)
                                .filter(|(_, lbl)| match lbl {
                                    Some(l) if l.starts_with("KU:") =>
                                        !case_used.contains(l),
                                    _ => true,
                                })
                                .map(|(s, _)| s.clone())
                                .collect();
                            // Determine which source-label will be
                            // picked, so sub-cases can inherit it.
                            let picked_label = pick_matching_ku_source_label(
                                &filtered, &fa_ku);
                            if let (Some(picked), Some(grafted)) = (
                                picked_label,
                                saturate_ku_action_via_sources(
                                    ctx, &filtered, sys, &goal_node, &fa_ku, name),
                            ) {
                                for (sub_name, sub_sys) in grafted {
                                    let mut sub_used = case_used.clone();
                                    sub_used.insert(picked.clone());
                                    new_cases.push((sub_name, sub_sys));
                                    new_used.push(sub_used);
                                    changed = true;
                                }
                                continue;
                            }
                        }
                    }
                }
                let open = first_open_proto_premise(sys);
                match open {
                    None => {
                        new_cases.push((name.clone(), sys.clone()));
                        new_used.push(case_used.clone());
                    }
                    Some((p, fa)) => {
                        // Find a source whose recorded goal matches this
                        // tag.  If none, leave the case intact.
                        let avoid_max = system_max_idx(sys);
                        let target = current.iter().find(|s| match &s.goal {
                            crate::constraint::constraints::Goal::Premise(_, gfa)
                                => gfa.tag == fa.tag,
                            _ => false,
                        });
                        let Some(target) = target else {
                            new_cases.push((name.clone(), sys.clone()));
                            new_used.push(case_used.clone());
                            continue;
                        };
                        let abstract_orig = match &target.goal {
                            crate::constraint::constraints::Goal::Premise((n, _), _) => n.clone(),
                            _ => continue,
                        };
                        let abstract_orig_idx_pidx = match &target.goal {
                            crate::constraint::constraints::Goal::Premise((_, pi), _) => *pi,
                            _ => continue,
                        };
                        let mut any_grafted = false;
                        for (sub_name, sub_sys) in &target.cases {
                            let renamed = freshen_system(
                                sub_sys, avoid_max,
                                maude_align.map(|c| &c.maude));
                            let abstract_renamed = {
                                let mut v = abstract_orig.clone();
                                v.idx = v.idx.saturating_add(avoid_max.saturating_add(1));
                                v
                            };
                            // Find the case's producer-conclusion edge into
                            // the abstract goal.  The fact at that edge's
                            // source is the *concrete* conclusion: its term
                            // arguments (post-`subst_system` normalisation
                            // from precompute) use the rule's actual vars,
                            // which is what we need to unify with the open
                            // premise's term.  Mirrors the same logic in
                            // `solve_with_source_cases` at runtime.
                            let case_conc = renamed.edges.iter().find_map(|e| {
                                if e.tgt.0 == abstract_renamed
                                    && e.tgt.1 == abstract_orig_idx_pidx
                                {
                                    renamed.nodes.iter()
                                        .find(|(id, _)| id == &e.src.0)
                                        .and_then(|(_, ru)| ru.conclusions.get(e.src.1.0).cloned())
                                } else { None }
                            });
                            let Some(case_conc) = case_conc else {
                                // No producer-conclusion edge — case has
                                // dangling abstract goal, skip.
                                continue;
                            };
                            // Build a syntactic substitution that aligns
                            // the case's conclusion-fact term vars with
                            // the live open-premise's terms.  When BOTH
                            // sides are bare vars but with different
                            // sorts, prefer the narrower sort (so $I:Pub
                            // doesn't get rewritten to I:Msg).  This is a
                            // lightweight stand-in for Maude order-sorted
                            // unification at saturation time — without
                            // it, Pub/Fresh narrowings from the protocol's
                            // typed rules get washed out when source
                            // cases are pre-computed.
                            use tamarin_term::lterm::LSort;
                            let narrower = |a: LSort, b: LSort| -> Option<LSort> {
                                if a == b { return Some(a); }
                                match (a, b) {
                                    (LSort::Msg, LSort::Pub) | (LSort::Pub, LSort::Msg) => Some(LSort::Pub),
                                    (LSort::Msg, LSort::Fresh) | (LSort::Fresh, LSort::Msg) => Some(LSort::Fresh),
                                    (LSort::Msg, LSort::Nat) | (LSort::Nat, LSort::Msg) => Some(LSort::Nat),
                                    _ => None, // incompatible — skip
                                }
                            };
                            let mut term_subst: std::collections::BTreeMap<
                                tamarin_term::lterm::LVar,
                                tamarin_term::lterm::LNTerm,
                            > = std::collections::BTreeMap::new();
                            let mut compatible = true;
                            for (c, l) in case_conc.terms.iter().zip(fa.terms.iter()) {
                                use tamarin_term::term::Term;
                                use tamarin_term::vterm::Lit;
                                match (c, l) {
                                    (Term::Lit(Lit::Var(cv)), Term::Lit(Lit::Var(lv))) => {
                                        let Some(s) = narrower(cv.sort, lv.sort) else {
                                            compatible = false; break;
                                        };
                                        // When the live side is a Maude
                                        // witness (`~mw:Msg:N`), don't
                                        // propagate its (synthetic) name
                                        // into a new sort — that produces
                                        // sort-conflated `~mw:Fresh:N` /
                                        // `~mw:Pub:N` LVars that pollute
                                        // the source-case structure and
                                        // are the root cause of TLS's
                                        // witness-conflation class of
                                        // wrong-falsified verdicts.
                                        //
                                        // Use the case's natural-named
                                        // var (`cv`) at the narrower sort
                                        // instead — that's exactly what
                                        // Haskell's order-sorted unifier
                                        // does (it picks the named var
                                        // when one side is anonymous).
                                        //
                                        // ALSO: if lv's sort is BROADER
                                        // than the narrower result `s`,
                                        // pick cv's identity (which is at
                                        // the narrower sort already) —
                                        // synthesizing `{name: lv.name,
                                        // sort: s, idx: lv.idx}` would
                                        // create a sort-conflated LVar
                                        // (e.g. `t:Fresh:1` colliding with
                                        // stable `t:Msg:1`).  Haskell-
                                        // faithful: narrowing produces a
                                        // binding `lv → cv` (Msg→Fresh)
                                        // without synthesizing new LVars.
                                        let use_cv_name = (lv.name == "~mw" && cv.name != "~mw")
                                            || lv.sort != s;
                                        let canonical = if use_cv_name {
                                            tamarin_term::lterm::LVar {
                                                name: cv.name.clone(),
                                                sort: s,
                                                idx: cv.idx,
                                            }
                                        } else {
                                            tamarin_term::lterm::LVar {
                                                name: lv.name.clone(),
                                                sort: s,
                                                idx: lv.idx,
                                            }
                                        };
                                        let canonical_term = Term::Lit(Lit::Var(canonical));
                                        term_subst.insert(cv.clone(), canonical_term.clone());
                                        if cv != lv {
                                            term_subst.insert(lv.clone(), canonical_term);
                                        }
                                    }
                                    (Term::Lit(Lit::Var(cv)), _) => {
                                        term_subst.insert(cv.clone(), l.clone());
                                    }
                                    _ => { /* live side is not a bare var; let runtime
                                              Maude handle complex pairings */ }
                                }
                            }
                            if !compatible { continue; }
                            // Apply the subst to BOTH sides so the live
                            // outer case's vars get narrowed too — without
                            // this, the live `I:Msg` stays Msg-sorted while
                            // the case adds `I:Pub`, and the graft hands
                            // the runtime two semantically-distinct LVars
                            // for what should be the same variable.
                            let renamed = apply_lvar_subst(&renamed, &term_subst);
                            let mut live_sys = apply_lvar_subst(sys, &term_subst);
                            // Compose cross-sort term_subst entries into
                            // live_sys.eq_store.subst.  apply_lvar_subst
                            // only rewrites identity for same-sort renames
                            // (guarded since session 5 to avoid sort-
                            // conflated LVars).  Cross-sort entries like
                            // `t#1:Msg → n:Fresh:8` represent narrowing
                            // constraints that must enter eq_store as
                            // bindings — otherwise the constraint is lost
                            // and runtime applySource can't detect the
                            // contradiction.  Haskell-faithful: matching
                            // subst is composed into eq_store via
                            // `applyEqStore` (EquationStore.hs).
                            {
                                let mut cross_sort_pairs: Vec<(tamarin_term::lterm::LVar,
                                    tamarin_term::lterm::LNTerm)> = Vec::new();
                                for (k, v) in &term_subst {
                                    if let tamarin_term::term::Term::Lit(
                                        tamarin_term::vterm::Lit::Var(nv)) = v
                                    {
                                        if nv.sort == k.sort {
                                            // Same-sort: handled by apply_lvar_subst alpha-rename.
                                            continue;
                                        }
                                    }
                                    // Cross-sort or var→app: add as binding.
                                    cross_sort_pairs.push((k.clone(), v.clone()));
                                }
                                if !cross_sort_pairs.is_empty() {
                                    let added = tamarin_term::subst::Subst::from_list(cross_sort_pairs);
                                    live_sys.eq_store.subst = added.compose(&live_sys.eq_store.subst);
                                }
                            }
                            // Compute the case_conc post-subst for the
                            // Maude alignment step below.
                            let case_conc_aligned = {
                                use tamarin_term::lterm::HasFrees;
                                let mut f = case_conc.clone();
                                f = f.map_free(&mut |v| {
                                    if let Some(t) = term_subst.get(&v) {
                                        if let tamarin_term::term::Term::Lit(
                                            tamarin_term::vterm::Lit::Var(nv)) = t
                                        {
                                            nv.clone()
                                        } else { v }
                                    } else { v }
                                });
                                // Apply the term part of the subst into terms too.
                                f.terms = f.terms.into_iter()
                                    .map(|t| tamarin_term::subst::apply_vterm(
                                        &lvar_map_to_subst(&term_subst), t))
                                    .collect();
                                f
                            };
                            let fa_aligned = {
                                use tamarin_term::lterm::HasFrees;
                                let mut f = fa.clone();
                                f = f.map_free(&mut |v| {
                                    if let Some(t) = term_subst.get(&v) {
                                        if let tamarin_term::term::Term::Lit(
                                            tamarin_term::vterm::Lit::Var(nv)) = t
                                        {
                                            nv.clone()
                                        } else { v }
                                    } else { v }
                                });
                                f.terms = f.terms.into_iter()
                                    .map(|t| tamarin_term::subst::apply_vterm(
                                        &lvar_map_to_subst(&term_subst), t))
                                    .collect();
                                f
                            };
                            if let Some(grafted) = graft_case_into(
                                &live_sys, &renamed, &abstract_renamed,
                                &p.0, p.1, &fa_aligned,
                            ) {
                                // Maude alignment: if we have a Maude
                                // handle, run a proper AC-unification of
                                // case_conc with fa.  This is the
                                // Haskell-faithful step that narrows
                                // sorts and equates structurally-shared
                                // sub-terms.  Without Maude, fall back
                                // on the lightweight `term_subst` we
                                // already built above.
                                let final_sys: Option<System> = if let Some(ctx) = maude_align {
                                    maude_align_and_simplify(
                                        ctx, grafted, &case_conc_aligned, &fa_aligned)
                                } else {
                                    Some(grafted)
                                };
                                if let Some(final_sys) = final_sys {
                                    // Haskell `refineSource`'s `combine`
                                    // (Sources.hs:135-137): drop leading
                                    // "coerce" entries from the
                                    // accumulated name list, then take
                                    // the FIRST remaining entry — i.e.
                                    // subsequent step-names are IGNORED
                                    // once we have a non-coerce name.
                                    //
                                    //   combine ("coerce":ns) ns' =
                                    //     combine ns ns'
                                    //   combine (n:_) _           = [n]
                                    //   combine []    ns'         = ns'
                                    //
                                    // So if `name` already carries a
                                    // non-coerce segment (e.g. "responder"
                                    // from prior saturate_out_premise),
                                    // the proto-premise step's `sub_name`
                                    // ("Setup") doesn't extend the case
                                    // name.  Without this rule, our names
                                    // grew unbounded ("coerce_responder_
                                    // Setup", "responder_Setup_…") and
                                    // `saturated_chain_root` only stripped
                                    // the leading coerce, leaving the
                                    // proof trace mismatched against
                                    // Haskell's single-segment "responder".
                                    let combined = combine_case_names(
                                        &name, &sub_name);
                                    new_cases.push((combined, final_sys));
                                    new_used.push(case_used.clone());
                                    any_grafted = true;
                                }
                            }
                        }
                        if any_grafted { changed = true; }
                        else {
                            new_cases.push((name.clone(), sys.clone()));
                            new_used.push(case_used.clone());
                        }
                    }
                }
            }
            // Mirror Haskell's `refineSource` (Sources.hs:118-124):
            // after running the proof step on each case, restrict the
            // eq-store to `stableVars = frees (get cdGoal th)`.  Drops
            // bindings keyed on rule-internal vars introduced during
            // this saturate iteration's `solveAllSafeGoals`.
            //
            // Before restrict, run `subst_system` so any eq-store
            // bindings introduced by the saturate step's
            // `solve_premise_goal` / `saturate_out_premise` get
            // propagated into the case's nodes/edges.  Without this
            // propagation, the Coerce/IRecv premise terms in the case
            // retain abstract pattern-vars (e.g. `t:Msg:1`) while the
            // eq-store carries `t:Msg:1 → <case-body>`.  At runtime,
            // `apply_source_case_action`'s refineSubst adds
            // `t:Msg:1#shift → <live-body>`, which Maude chains
            // against the precompute binding's `<case-body>` —
            // dragging stale rule-internal vars from the case-body
            // into the live system as orphan bindings, surfaces as
            // spurious `eq_store.is_false` post-simplify, and the
            // simplify-time filter drops the case.  Mirrors Haskell:
            // `solveAllSafeGoals` calls `simplifySystem` (which calls
            // `substSystem`) on every iteration, so by the time
            // `refineSource` does `restrict`, the subst is propagated.
            let stable_vars = stable_vars_for_goal(&src.goal);
            // Haskell-faithful: solveAllSafeGoals interleaves simplifySystem
            // (which propagates eq-store bindings via substSystem) and
            // contradictoryIf checks between safe-goal solves.  Cases that
            // become contradictory mid-iter via mzero are dropped from the
            // Disj.  Mirror this by running subst_system + contradictions
            // check on every case AFTER expansion BEFORE restrict.
            //
            // Critical for KU(t:Fresh) source: Sessk_reveal's Out(k) chained
            // back to Init_2's !Sessk(_, KDF(...)) introduces binding
            // k → KDF(...).  After subst_system, irecv's KD(m_learn) becomes
            // KD(KDF(...)) — which has_impossible_chain catches as
            // incompatible with the chain-end KD(t:Fresh).  Without this
            // check, the Sessk_reveal case survives saturate and pollutes
            // the KU(t:Fresh) source with cases Haskell correctly omits.
            //
            // Aligned with: Haskell `solveAllSafeGoals` (Sources.hs:175 area)
            // calls `simplifySystem >> contradictoryIfT ... <- gets
            // contradictorySystem` on every step.
            let mut filtered_new_cases: Vec<(String, System)> = Vec::new();
            let mut filtered_new_used: Vec<BTreeSet<String>> = Vec::new();
            for ((nm, case_sys), used) in new_cases.into_iter().zip(new_used.into_iter()) {
                let keep = if let Some(ctx) = fold_ctx {
                    let mut r = crate::constraint::solver::reduction::Reduction::new(ctx, case_sys);
                    // Haskell's `solvePremise` enforces fact equality on the
                    // newly-added edge via insertEdges → solveFactEqs.  Our
                    // graft_case_into adds edges WITHOUT this unification,
                    // so the case's eq_store lacks the producer-conclusion
                    // bindings (e.g. !Sessk(~m1, k) ~ !Sessk(_, KDF(...))
                    // never produces `k → KDF(...)`).  Re-run edge fact
                    // unification here to bridge the gap.  Mirrors Haskell
                    // `solveAllSafeGoals` which calls solvePremise that
                    // calls insertEdges that calls solveFactEqs.
                    let edge_eqs: Vec<_> = r.sys.edges.iter().filter_map(|e| {
                        let conc = r.sys.nodes.iter()
                            .find(|(n, _)| n == &e.src.0)?
                            .1.conclusions.get(e.src.1.0).cloned()?;
                        let prem = r.sys.nodes.iter()
                            .find(|(n, _)| n == &e.tgt.0)?
                            .1.premises.get(e.tgt.1.0).cloned()?;
                        if conc.tag != prem.tag || conc.terms.len() != prem.terms.len() {
                            return None;
                        }
                        if conc == prem { return None; }
                        Some(tamarin_term::rewriting::Equal { lhs: conc, rhs: prem })
                    }).collect();
                    if !edge_eqs.is_empty() {
                        // Was `SplitLater`; bumped to `SplitNow` to match
                        // Haskell `insertEdges` → `solveFactEqs SplitNow`
                        // (System.hs near insertEdges).  Defers => SplitG
                        // means downstream saturate iters see open Splits
                        // rather than propagated subst — exactly the gap
                        // that forced the defensive `chain_eqs` pass in
                        // apply_source_case_premise (task #249).
                        let _ = r.solve_fact_eqs(
                            crate::constraint::solver::reduction::SplitStrategy::SplitNow,
                            &edge_eqs);
                    }
                    r.subst_system();
                    if r.sys.eq_store.is_false() {
                        None
                    } else {
                        let contras = crate::constraint::solver::contradictions::contradictions(
                            ctx, &r.sys);
                        if !contras.is_empty() { None } else { Some(r.sys) }
                    }
                } else {
                    Some(case_sys)
                };
                if let Some(s) = keep {
                    filtered_new_cases.push((nm, s));
                    filtered_new_used.push(used);
                }
            }
            let mut new_cases = filtered_new_cases;
            let new_used = filtered_new_used;
            for (_, case_sys) in new_cases.iter_mut() {
                restrict_eq_store_to_stable_vars(case_sys, &stable_vars);
            }
            next.push(Source { goal: src.goal.clone(), cases: new_cases, incomplete: src_incomplete });
            next_used.push(new_used);
        }
        // Haskell-faithful per-iter contradictory-case pruning.
        // Mirrors `solveAllSafeGoals` (Sources.hs:144-219) running
        // inside `refineSource` for each iter of `saturateSources`
        // (Sources.hs:356-385).  Each iter, Haskell's Disj monad
        // mzeros out cases whose `solveAllSafeGoals` produces no
        // surviving branches — driving sources like `KU(t:Fresh)`
        // toward `goodTh` (≤1 case) so they become applicable to
        // sub-goals in OTHER cases via `solveWithSourceAndReturn`
        // (Sources.hs:206 `asum $ map ...`).
        //
        // Without this pass, Rust's saturate accumulates chain-fold
        // variants in KU(t:Fresh) (coerce-rooted) that aren't pruned
        // until `drop_contradictory_cases` runs POST-saturate.  The
        // multi-case state blocks `goodTh` throughout saturate, so
        // the proto-grafted case-systems (e.g. chaum's `S_1` case
        // with open `KU(~x:Fresh)`) never get their KU sub-goals
        // auto-solved, and the runtime smartRanking ends up picking
        // `case c_fresh` instead of `case B_1` / `S_2` / etc.
        //
        // Cluster B fix.
        if let Some(ctx) = fold_ctx {
            // good_ths = iter-start sources with ≤1 case.  Same set
            // Haskell passes to `solveAllSafeGoals` per iter
            // (Sources.hs:383-384 `filter goodTh ths`).
            let good_ths: Vec<Source> = current.iter()
                .filter(|s| s.cases.len() <= 1)
                .cloned()
                .collect();
            for (src_idx, src) in next.iter_mut().enumerate() {
                let cases_snapshot = src.cases.clone();
                let used_snapshot: Vec<BTreeSet<String>> = next_used
                    .get(src_idx).cloned().unwrap_or_default();
                let mut kept_cases: Vec<(String, System)> = Vec::new();
                let mut kept_used: Vec<BTreeSet<String>> = Vec::new();
                for (case_idx, (name, sys)) in cases_snapshot.iter().enumerate() {
                    if case_has_surviving_variant_with_ths(ctx, sys, &good_ths) {
                        kept_cases.push((name.clone(), sys.clone()));
                        kept_used.push(used_snapshot.get(case_idx)
                            .cloned().unwrap_or_default());
                    } else {
                        // A case was dropped this iter — flag `changed`
                        // so the saturate loop continues another iter.
                        changed = true;
                    }
                }
                src.cases = kept_cases;
                if let Some(slot) = next_used.get_mut(src_idx) {
                    *slot = kept_used;
                }
            }
            // After pruning, run an auto-apply pass: for each case in
            // `next` with an open KU action goal, find a NOW-goodTh
            // source (in `next`, post-prune) that matches and graft
            // its case.  Mirrors Haskell's `solveAllSafeGoals`'s
            // `solveWithSourceAndReturn` arm (Sources.hs:206) firing
            // on `usefulGoals` (KU actions) when goodTh sources are
            // available.
            //
            // Without this, sources like `KU(t:Fresh)` that BECOME
            // goodTh after per-iter pruning aren't actually applied
            // to KU sub-goals in proto-grafted cases — runtime
            // smartRanking then sees open KU(~x:Fresh) sub-goals and
            // picks `case c_fresh` instead of the protocol rule.
            //
            // Consults `next` (post-prune state) so newly-goodTh
            // sources are visible.  Source labels are recomputed
            // since `next.cases` may have changed.
            let next_labels: Vec<Option<String>> = next.iter()
                .map(source_label).collect();
            for src_idx in 0..next.len() {
                let cases_snapshot = next[src_idx].cases.clone();
                let used_snapshot: Vec<BTreeSet<String>> = next_used
                    .get(src_idx).cloned().unwrap_or_default();
                let mut new_inner_cases: Vec<(String, System)> = Vec::new();
                let mut new_inner_used: Vec<BTreeSet<String>> = Vec::new();
                for (case_idx, (name, sys)) in cases_snapshot.iter().enumerate() {
                    let case_used = used_snapshot.get(case_idx)
                        .cloned().unwrap_or_default();
                    if first_open_proto_premise(sys).is_none() {
                        if let Some((goal_node, fa_ku)) =
                            first_open_ku_action_goal(sys)
                        {
                            let filtered: Vec<Source> = next.iter()
                                .zip(next_labels.iter())
                                .filter(|(s, _)| s.cases.len() <= 1)
                                .filter(|(_, lbl)| match lbl {
                                    Some(l) if l.starts_with("KU:") =>
                                        !case_used.contains(l),
                                    _ => true,
                                })
                                .map(|(s, _)| s.clone())
                                .collect();
                            let picked_label =
                                pick_matching_ku_source_label(
                                    &filtered, &fa_ku);
                            if let (Some(picked), Some(grafted)) = (
                                picked_label,
                                saturate_ku_action_via_sources(
                                    ctx, &filtered, sys,
                                    &goal_node, &fa_ku, name),
                            ) {
                                for (sub_name, sub_sys) in grafted {
                                    let mut sub_used = case_used.clone();
                                    sub_used.insert(picked.clone());
                                    new_inner_cases.push((sub_name, sub_sys));
                                    new_inner_used.push(sub_used);
                                }
                                changed = true;
                                continue;
                            }
                        }
                    }
                    new_inner_cases.push((name.clone(), sys.clone()));
                    new_inner_used.push(case_used);
                }
                next[src_idx].cases = new_inner_cases;
                if let Some(slot) = next_used.get_mut(src_idx) {
                    *slot = new_inner_used;
                }
            }
        }
        current = next;
        current_used = next_used;
        if !changed { break; }
    }
    // Haskell's `saturateSources` keeps every case after iterating
    // `solveAllSafeGoals`, regardless of whether open premises remain.
    // Runtime's `applySource` handles cases with open Proto premises.
    // The previous Rust-only post-filter (drop cases with any open Proto
    // premise) was a soundness hack that masked search-completeness bugs
    // and dropped legitimate destructor-chain cases (e.g. NSPK3's I_2
    // producing KU(~nr) via aenc-decomposition).
    current
}

/// Canonicalise a `System` by renaming every LVar to a sequential idx
/// based on first appearance during a deterministic traversal, then
/// serialise to a string.  Two systems that are structurally equivalent
/// modulo variable renaming produce the same canonical string.
///
/// Currently kept for diagnostic probes (compare two precomputed cases
/// for structural equivalence).  Was experimentally wired into
/// `saturate_sources_inner_with_options` to dedup new_cases at each
/// iteration; that didn't help TLS_Handshake (the two S_2 cases turned
/// out to be legitimately different — different `In` premise unifications
/// — not freshen-order duplicates), so the dedup call was removed.
#[allow(dead_code)]
pub fn canonicalise_system(sys: &crate::constraint::system::System) -> String {
    use tamarin_term::lterm::{HasFrees, LVar};
    use std::collections::BTreeMap;
    // Build the variable renaming map in deterministic order.
    let mut rename: BTreeMap<LVar, u64> = BTreeMap::new();
    let mut next_idx: u64 = 0;
    let intern = |v: &LVar, rename: &mut BTreeMap<LVar, u64>, next: &mut u64| {
        if !rename.contains_key(v) {
            rename.insert(v.clone(), *next);
            *next += 1;
        }
    };
    // Walk nodes (sorted by current idx so traversal is deterministic).
    let mut sorted_nodes: Vec<_> = sys.nodes.iter().collect();
    sorted_nodes.sort_by(|(a, _), (b, _)| a.cmp(b));
    for (id, ru) in &sorted_nodes {
        id.for_each_free(&mut |v| intern(v, &mut rename, &mut next_idx));
        ru.for_each_free(&mut |v| intern(v, &mut rename, &mut next_idx));
    }
    let mut sorted_edges: Vec<_> = sys.edges.iter().collect();
    sorted_edges.sort();
    for e in &sorted_edges {
        e.src.0.for_each_free(&mut |v| intern(v, &mut rename, &mut next_idx));
        e.tgt.0.for_each_free(&mut |v| intern(v, &mut rename, &mut next_idx));
    }
    // Now serialise the system using the rename map.  The exact format
    // is irrelevant as long as it's deterministic and unique modulo
    // the rename.
    let r = |v: &LVar| -> String {
        format!("v{}:{:?}", rename.get(v).cloned().unwrap_or(u64::MAX), v.sort)
    };
    let term_str = |t: &tamarin_term::lterm::LNTerm| -> String {
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        fn rec(
            t: &tamarin_term::lterm::LNTerm,
            rename: &BTreeMap<LVar, u64>,
        ) -> String {
            match t {
                Term::Lit(Lit::Var(v)) => format!(
                    "v{}:{:?}",
                    rename.get(v).cloned().unwrap_or(u64::MAX),
                    v.sort
                ),
                Term::Lit(Lit::Con(c)) => format!("{:?}", c),
                Term::App(sym, args) => {
                    let mut s = format!("{:?}(", sym);
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 { s.push(','); }
                        s.push_str(&rec(a, rename));
                    }
                    s.push(')');
                    s
                }
            }
        }
        rec(t, &rename)
    };
    let _ = r;  // silence unused-var
    let mut out = String::new();
    out.push_str("NODES:");
    for (id, ru) in &sorted_nodes {
        out.push_str(&format!("[id={}:{:?},info={:?}",
            rename.get(id).cloned().unwrap_or(u64::MAX), id.sort, ru.info));
        for p in &ru.premises {
            out.push_str(&format!(",p:{:?}:", p.tag));
            for t in &p.terms { out.push_str(&term_str(t)); out.push(','); }
        }
        for c in &ru.conclusions {
            out.push_str(&format!(",c:{:?}:", c.tag));
            for t in &c.terms { out.push_str(&term_str(t)); out.push(','); }
        }
        for a in &ru.actions {
            out.push_str(&format!(",a:{:?}:", a.tag));
            for t in &a.terms { out.push_str(&term_str(t)); out.push(','); }
        }
        out.push(']');
    }
    out.push_str("EDGES:");
    for e in &sorted_edges {
        out.push_str(&format!(
            "{}.{:?}->{}.{:?};",
            rename.get(&e.src.0).cloned().unwrap_or(u64::MAX), e.src.1,
            rename.get(&e.tgt.0).cloned().unwrap_or(u64::MAX), e.tgt.1));
    }
    out
}

/// Walk every free `LVar` of a `Goal`, mirroring Haskell's `frees`
/// instance.  Bound vars in formulas are skipped.
fn goal_free_vars(g: &crate::constraint::constraints::Goal, f: &mut dyn FnMut(&tamarin_term::lterm::LVar)) {
    use crate::constraint::constraints::Goal;
    use tamarin_term::lterm::HasFrees;
    match g {
        Goal::Action(i, fa) => {
            f(i);
            fa.for_each_free(f);
        }
        Goal::Premise(p, fa) => {
            f(&p.0);
            fa.for_each_free(f);
        }
        Goal::Chain(c, p) => {
            f(&c.0);
            f(&p.0);
        }
        Goal::Disj(_) => {
            // Disj contents are formulas; bound vars excluded.  For
            // restrict purposes, we don't need to enumerate these.
        }
        Goal::Split(_) => {}
        Goal::Subterm((a, b)) => {
            a.for_each_free(f);
            b.for_each_free(f);
        }
    }
}

/// Fuller canonical form for case dedup — extends `canonicalise_system`
/// to also cover less_atoms, last_atom, open goals, formulas+solved,
/// lemmas, used_sources, source_kind/side, and the eq_store's free
/// substitution.  Used by `saturate_sources_with_simp_opt`'s
/// multi-branch dedup so that two branches differing in goals/formulas
/// (but identical in nodes/edges) are treated as distinct cases.
///
/// We deliberately keep `canonicalise_system` minimal because its
/// callers in solve_with_source_cases use it to match cases against
/// runtime goals — at that point, goal-list differences are what we
/// WANT to ignore.  This fuller variant is for the precompute-time
/// dedup where every semantic difference matters.
pub fn canonicalise_system_full(
    sys: &crate::constraint::system::System,
) -> String {
    use tamarin_term::lterm::{HasFrees, LVar};
    use std::collections::BTreeMap;
    let mut rename: BTreeMap<LVar, u64> = BTreeMap::new();
    let mut next_idx: u64 = 0;
    let intern = |v: &LVar,
                  rename: &mut BTreeMap<LVar, u64>,
                  next: &mut u64| {
        if !rename.contains_key(v) {
            rename.insert(v.clone(), *next);
            *next += 1;
        }
    };
    // Walk in deterministic order so var renaming is stable.
    let mut sorted_nodes: Vec<_> = sys.nodes.iter().collect();
    sorted_nodes.sort_by(|(a, _), (b, _)| a.cmp(b));
    for (id, ru) in &sorted_nodes {
        id.for_each_free(&mut |v| intern(v, &mut rename, &mut next_idx));
        ru.for_each_free(&mut |v| intern(v, &mut rename, &mut next_idx));
    }
    let mut sorted_edges: Vec<_> = sys.edges.iter().collect();
    sorted_edges.sort();
    for e in &sorted_edges {
        e.src.0.for_each_free(&mut |v| intern(v, &mut rename, &mut next_idx));
        e.tgt.0.for_each_free(&mut |v| intern(v, &mut rename, &mut next_idx));
    }
    // LVar is itself an LVar (NodeId/Suffix etc.), so intern directly.
    for la in &sys.less_atoms {
        intern(&la.smaller, &mut rename, &mut next_idx);
        intern(&la.larger, &mut rename, &mut next_idx);
    }
    if let Some(j) = &sys.last_atom {
        intern(j, &mut rename, &mut next_idx);
    }
    // Formulas / goals / lemmas: their vars are usually a subset of
    // nodes/edges/less/last atom vars (which are already interned).
    // We include their Debug-stringified form below for content
    // distinction; any extra vars they reference will appear as
    // raw (un-renamed) — still useful for distinguishing branches,
    // just less canonical.

    let term_str = |t: &tamarin_term::lterm::LNTerm| -> String {
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        fn rec(t: &tamarin_term::lterm::LNTerm, rename: &BTreeMap<LVar, u64>) -> String {
            match t {
                Term::Lit(Lit::Var(v)) => format!(
                    "v{}:{:?}",
                    rename.get(v).cloned().unwrap_or(u64::MAX),
                    v.sort),
                Term::Lit(Lit::Con(c)) => format!("{:?}", c),
                Term::App(sym, args) => {
                    let mut s = format!("{:?}(", sym);
                    for (i, a) in args.iter().enumerate() {
                        if i > 0 { s.push(','); }
                        s.push_str(&rec(a, rename));
                    }
                    s.push(')');
                    s
                }
            }
        }
        rec(t, &rename)
    };

    let mut out = String::new();
    out.push_str(&format!("SK={:?};SIDE={:?};NODES:",
        sys.source_kind, sys.side));
    for (id, ru) in &sorted_nodes {
        out.push_str(&format!("[id={}:{:?},info={:?}",
            rename.get(id).cloned().unwrap_or(u64::MAX), id.sort, ru.info));
        for p in &ru.premises {
            out.push_str(&format!(",p:{:?}:", p.tag));
            for t in &p.terms { out.push_str(&term_str(t)); out.push(','); }
        }
        for c in &ru.conclusions {
            out.push_str(&format!(",c:{:?}:", c.tag));
            for t in &c.terms { out.push_str(&term_str(t)); out.push(','); }
        }
        for a in &ru.actions {
            out.push_str(&format!(",a:{:?}:", a.tag));
            for t in &a.terms { out.push_str(&term_str(t)); out.push(','); }
        }
        out.push(']');
    }
    out.push_str(";EDGES:");
    for e in &sorted_edges {
        out.push_str(&format!(
            "{}.{:?}->{}.{:?};",
            rename.get(&e.src.0).cloned().unwrap_or(u64::MAX), e.src.1,
            rename.get(&e.tgt.0).cloned().unwrap_or(u64::MAX), e.tgt.1));
    }
    // Less atoms (sorted for determinism — order varies between branches).
    let mut sorted_less: Vec<_> = sys.less_atoms.iter().collect();
    sorted_less.sort_by(|a, b| (
            rename.get(&a.smaller).cloned().unwrap_or(u64::MAX),
            rename.get(&a.larger).cloned().unwrap_or(u64::MAX),
            format!("{:?}", a.reason))
        .cmp(&(
            rename.get(&b.smaller).cloned().unwrap_or(u64::MAX),
            rename.get(&b.larger).cloned().unwrap_or(u64::MAX),
            format!("{:?}", b.reason))));
    out.push_str(";LESS:");
    for la in sorted_less {
        out.push_str(&format!("{}<{}|{:?};",
            rename.get(&la.smaller).cloned().unwrap_or(u64::MAX),
            rename.get(&la.larger).cloned().unwrap_or(u64::MAX),
            la.reason));
    }
    out.push_str(";LAST:");
    if let Some(j) = &sys.last_atom {
        out.push_str(&format!("{}", rename.get(j).cloned().unwrap_or(u64::MAX)));
    }
    // Open goals (drop solved goals for dedup — semantically irrelevant).
    let mut goal_strs: Vec<String> = sys.goals.iter()
        .filter(|(_, st)| !st.solved)
        .map(|(g, _)| format!("{:?}", g))
        .collect();
    goal_strs.sort();
    out.push_str(";GOALS:");
    for g in &goal_strs { out.push_str(g); out.push(';'); }
    // Formulas (sorted for canonical order).
    let mut form_strs: Vec<String> = sys.formulas.iter()
        .map(|f| format!("{:?}", f))
        .collect();
    form_strs.sort();
    out.push_str(";FORMS:");
    for f in &form_strs { out.push_str(f); out.push(';'); }
    let mut solved_strs: Vec<String> = sys.solved_formulas.iter()
        .map(|f| format!("{:?}", f))
        .collect();
    solved_strs.sort();
    out.push_str(";SOLVED:");
    for f in &solved_strs { out.push_str(f); out.push(';'); }
    // Used sources — affects what future runtime steps can/can't do.
    let mut used: Vec<&String> = sys.used_sources.iter().collect();
    used.sort();
    out.push_str(";USED:");
    for u in &used { out.push_str(u); out.push(','); }
    // Eq-store free subst — distinguishes branches that committed to
    // different equation bindings.
    let subst_pairs = sys.eq_store.subst.to_list();
    let mut subst_strs: Vec<String> = subst_pairs.iter()
        .map(|(v, t)| format!(
            "v{}:{:?}={}",
            rename.get(v).cloned().unwrap_or(u64::MAX),
            v.sort,
            term_str(t)))
        .collect();
    subst_strs.sort();
    out.push_str(";SUBST:");
    for s in &subst_strs { out.push_str(s); out.push(','); }
    out
}

/// Remove cases that have the same canonical form (structurally
/// equivalent modulo variable renaming).  Preserves the FIRST
/// occurrence and updates `used` in lockstep.
///
/// Unused at present — see [`canonicalise_system`] for context.
#[allow(dead_code)]
fn dedup_cases_by_canonical(
    cases: Vec<(String, crate::constraint::system::System)>,
    used: &mut Vec<std::collections::BTreeSet<String>>,
) -> Vec<(String, crate::constraint::system::System)> {
    use std::collections::BTreeSet;
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut out: Vec<(String, crate::constraint::system::System)> = Vec::with_capacity(cases.len());
    let mut new_used: Vec<BTreeSet<String>> = Vec::with_capacity(cases.len());
    for (i, (name, sys)) in cases.into_iter().enumerate() {
        let key = canonicalise_system(&sys);
        if seen.insert(key) {
            new_used.push(used.get(i).cloned().unwrap_or_default());
            out.push((name, sys));
        }
    }
    *used = new_used;
    out
}

/// Determine the source label that `saturate_ku_action_via_sources`
/// would pick for the open KU action `fa_live` if given `sources` as
/// the candidate list.  Mirrors the matcher inside
/// `solve_with_source_cases_action` exactly so the saturate loop can
/// record the picked source in the per-case `used` set BEFORE actually
/// calling the expansion (whose result includes the case-label but not
/// the source-label).
fn pick_matching_ku_source_label(
    sources: &[Source],
    fa_live: &crate::fact::LNFact,
) -> Option<String> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    if fa_live.tag != FactTag::Ku || fa_live.terms.len() != 1 { return None; }
    let m_live = &fa_live.terms[0];
    sources.iter().find_map(|s| match &s.goal {
        Goal::Action(_, gfa) if gfa.tag == FactTag::Ku && gfa.terms.len() == 1 => {
            let pat = &gfa.terms[0];
            let matches = match (pat, m_live) {
                (Term::Lit(Lit::Var(pv)), _) => {
                    let live_sort = sort_of_lnterm(m_live);
                    sort_ge(pv.sort, live_sort)
                }
                (Term::App(pf, pargs), Term::App(lf, largs)) => {
                    pf == lf && pargs.len() == largs.len()
                }
                _ => false,
            };
            if matches { source_label(s) } else { None }
        }
        _ => None,
    })
}

/// Return `Some((NodePrem, LNFact))` for the first open protocol-fact
/// premise goal in `sys`, or `None` if none.
fn first_open_proto_premise(
    sys: &System,
) -> Option<(crate::constraint::constraints::NodePrem, crate::fact::LNFact)> {
    use crate::constraint::constraints::Goal;
    sys.goals.iter().find_map(|(g, st)| {
        if st.solved { return None; }
        // Loop-breaker premises must NOT be expanded during saturation —
        // expanding them feeds back into the same rule and the chain
        // never terminates.  Mirrors Haskell's `saturateSources` where
        // self-loops on loop-breaker premises are pruned via
        // `useAutoLoopBreakersAC`'s flagging.
        if st.looping { return None; }
        match g {
            Goal::Premise(p, fa) if matches!(fa.tag, crate::fact::FactTag::Proto(_, _, _))
                => Some((p.clone(), fa.clone())),
            _ => None,
        }
    })
}

/// Graft producer-rule(s) onto an `Out` premise within a source-case.
/// Runs `solve_premise_goal` over a Reduction wrapping the case's
/// system; each returned case becomes a new sub-case of the outer
/// source, named `<outer>_<producer-rule>`.
///
/// Returns `None` if `solve_premise_goal` couldn't make progress
/// (contradictory or no candidates) — the caller then leaves the
/// case un-folded.
fn saturate_out_premise(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: &System,
    p: &crate::constraint::constraints::NodePrem,
    fa: &crate::fact::LNFact,
    outer_name: &str,
    incomplete_out: &mut bool,
) -> Option<Vec<(String, System)>> {
    use crate::constraint::solver::reduction::{
        GoalCases, Reduction, rule_case_name,
    };
    use crate::constraint::constraints::Goal;
    // Run solve_premise_goal in precompute mode so it routes through
    // rule enumeration (same path the runtime uses, but folded into
    // the source-case at precompute time).
    set_precompute_mode(true);
    let mut red = Reduction::new(ctx, sys.clone());
    let outcome = red.solve_premise_goal(p, fa);
    set_precompute_mode(false);
    let producer_name = |s: &System| -> String {
        s.edges.iter()
            .find(|e| e.tgt == *p)
            .and_then(|e| s.nodes.iter()
                .find(|(nid, _)| nid == &e.src.0)
                .map(|(_, r)| rule_case_name(r)))
            .unwrap_or_else(|| "case_1".into())
    };
    // Drop cases that leave open non-msg-var KD `Chain` goals.
    //
    // Haskell-faithful: msg-var KD chains are excluded from
    // `openGoals` (Goals.hs:92-100 — `chainToEquality` returns
    // False for non-IEquality premises), so saturate doesn't try
    // to close them.  Cases with open msg-var KD chains are
    // acceptable — they mirror Haskell's `saturateSources`
    // leaving these chains open in the saved source case.  Cases
    // with other unresolved chain goals (non-msg-var KD, or
    // non-KD) are dropped.
    let chain_acceptable = |s: &System| -> bool {
        !s.goals.iter().any(|(g, st)| {
            if st.solved { return false; }
            if let Goal::Chain(c, _) = g {
                if let Some(m) = chain_kd_conc_term_local(s, c) {
                    if is_msg_var_local(&m) { return false; }
                }
                true
            } else { false }
        })
    };
    if std::env::var("TAM_DBG_SAT").is_ok() {
        eprintln!("[sat] outer={} fa.tag={:?} fa.terms[0]={:?}",
            outer_name, fa.tag,
            fa.terms.first().map(|t|
                format!("{:?}", t).chars().take(100).collect::<String>())
                .unwrap_or_default());
    }
    // Cache (name_before_extension, system) — name is provisional and
    // recomputed after chain extension below, since the producer that
    // saturate_out_premise's `producer_name` resolves to changes after
    // `solve_chain_goal` adds edges from intermediate intruder rules
    // (e.g. irecv) to the upstream protocol producer.
    let raw: Vec<(String, System)> = match outcome {
        GoalCases::Contradictory => {
            if std::env::var("TAM_DBG_SAT").is_ok() {
                eprintln!("[sat]   → Contradictory");
            }
            return None;
        }
        GoalCases::Linear => {
            // Use a placeholder; chain extension below produces the
            // final producer rule's name via `producer_name`.
            vec![(String::new(), red.sys)]
        }
        GoalCases::LinearNamed(n) => {
            vec![(n, red.sys)]
        }
        GoalCases::Cases(cases) => cases.into_iter().collect(),
    };
    if std::env::var("TAM_DBG_SAT").is_ok() {
        eprintln!("[sat]   → {} cases: {:?}",
            raw.len(), raw.iter().map(|(n, _)| n).collect::<Vec<_>>());
    }
    // For each grafted case, also close any open Chain goal the KD
    // branch of `solve_premise_goal` introduced.  Without this, the
    // chain endpoint stays open and the runtime's separate
    // `solve_chain_goal` pass interacts unpredictably with the rest
    // of the proof state.
    set_precompute_mode(true);
    let mut closed_cases: Vec<(String, System)> = Vec::new();
    // DFS chain-closure backtracking — Haskell-faithful: enumerate
    // ALL successful chain closures, not just the first.  Haskell's
    // `disjunctionOfList` returns a Disj over all alternatives; each
    // becomes a separate source-case in the precomputed list.
    //
    // Previously we returned the FIRST closure, missing other
    // destructor-chain paths.  For C_1 with Out=<C, nc, sid, pc>,
    // the first closure picks snd-fst (extracting nc) — but the
    // snd-snd-fst path (extracting sid) was lost, so applying the
    // C_1 source to a `KU(~sid)` goal would over-conflate sid with
    // nc (the source's `t` was bound to nc, not sid).  This was the
    // root cause of TLS_Handshake's prem_idx_clash cascade.
    //
    // Returning a Vec lets us collect every chain-extension path
    // separately.  Each path becomes its own case in `closed_cases`.
    //
    // `last_term`: the conclusion term of the chain we just solved.
    // Mirrors Haskell `solveAllSafeGoals`'s `lastChainTerm` filter
    // (Sources.hs:181-186) — if a candidate chain's conclusion is
    // equal modulo freshness to the previous step's, skip it.  This
    // is the loop-breaking heuristic that prevents user-equation
    // destructor explosions: when `dec(enc(M,k),k) = M` is active
    // and a chain produces `K(enc(...))`, the next destructor step
    // would produce another `K(enc(...))` — same conclusion term,
    // path skipped.
    fn close_chains_dfs(
        ctx: &crate::constraint::solver::context::ProofContext,
        s: System,
        budget: usize,
        last_term: Option<&tamarin_term::lterm::LNTerm>,
        cases_remaining: &mut usize,
    ) -> Vec<System> {
        if *cases_remaining == 0 { return Vec::new(); }
        // Check FIRST whether there's any chain left to close,
        // filtering out chains whose conclusion term equals
        // `last_term` (Haskell-faithful loop-break).
        //
        // Haskell-faithful: msg-var KD chains are auto-handled
        // (Goals.hs:92-100 `chainToEquality` returns False for
        // non-IEquality premises). Haskell's `solveAllSafeGoals`
        // doesn't try to close them — they stay open in the saved
        // source case.  Mirroring this aligns saturate's output
        // with Haskell's, even though it exposes pre-existing
        // soundness bugs in NSPK3 et al. that were being masked by
        // our over-eager closure.  Those bugs are tracked separately
        // (see project memory) — the right fix is to find what
        // Haskell does instead that catches the same scenarios.
        let chain = s.goals.iter().find_map(|(g, st)| {
            if st.solved || st.looping { return None; }
            if let Goal::Chain(c, p) = g {
                if let Some(t) = last_term {
                    if let Some(this_t) = chain_conc_term(&s, c) {
                        if eq_modulo_freshness(t, &this_t) { return None; }
                    }
                }
                // Haskell-faithful: msg-var KD chains are auto-handled.
                if let Some(m) = chain_kd_conc_term_local(&s, c) {
                    if is_msg_var_local(&m) { return None; }
                }
                Some((c.clone(), p.clone()))
            } else { None }
        });
        let Some((c, p)) = chain else {
            *cases_remaining = cases_remaining.saturating_sub(1);
            return vec![s];
        };
        if budget == 0 { return Vec::new(); }
        let this_term = chain_conc_term(&s, &c);
        let mut sub = Reduction::new(ctx, s);
        set_precompute_mode(false);
        let outcome = sub.solve_chain_goal(&c, &p);
        set_precompute_mode(true);
        // Contradiction filter: drop branches whose post-solve state
        // is contradictory.  Haskell's `solveAllSafeGoals` calls
        // `contradictoryIf =<< gets contradictorySystem` between safe
        // goals (Sources.hs:178); Disj-monad branches that contradict
        // are mzero'd before the next safe-goal step.
        //
        // Without this, our DFS keeps every chain-extension combo
        // including the ones that immediately contradict.  chaum
        // B_1 had 85 closures where only ~1 is actually viable in
        // Haskell because the other 84 contradict at the next step.
        //
        // Uses `contradictions()` directly (no full simplify pass) —
        // that's the same check Haskell calls.  Full simplify is
        // unnecessary here because we're inside close_chains_dfs's
        // step-by-step iteration; the outer saturate runs simplify.
        let is_dead = |sys: &System| -> bool {
            use crate::constraint::solver::contradictions::contradictions;
            if sys.eq_store.is_false() { return true; }
            if sys.formulas.iter().any(|f|
                matches!(f, crate::guarded::Guarded::Disj(v) if v.is_empty()))
            { return true; }
            !contradictions(ctx, sys).is_empty()
        };
        match outcome {
            GoalCases::Contradictory => Vec::new(),
            GoalCases::Linear | GoalCases::LinearNamed(_) => {
                if is_dead(&sub.sys) { return Vec::new(); }
                close_chains_dfs(ctx, sub.sys, budget - 1, this_term.as_ref(), cases_remaining)
            }
            GoalCases::Cases(cases) => {
                // Allocate budget fairly across alternatives so a single
                // explosive branch (e.g. _0_fst leading to many sub-chains)
                // doesn't starve later destructor alternatives (_0_snd).
                // Without this, the DFS exhausts cases_remaining on the
                // first destructor's subtree, dropping snd-paths entirely
                // — which was the root cause of denning_sacco_symmetric_cbc::
                // sessionsmatch being wrong-VERIFIED (missing Server source
                // case for inner-enc extraction via _0_dec → _0_snd).
                //
                // Mirrors Haskell's Disj-monad branching: each destructor
                // alternative gets its own slice of the closure budget,
                // matching the saturate_out_premise top-level allocation.
                let live_cases: Vec<_> = cases.into_iter()
                    .filter(|(_, c_sys)| !is_dead(c_sys))
                    .collect();
                let n = live_cases.len();
                if n == 0 { return Vec::new(); }
                let total_budget = *cases_remaining;
                let per_alt = (total_budget / n).max(1);
                let mut leftover = total_budget.saturating_sub(per_alt * n);
                let mut out = Vec::new();
                for (_, c_sys) in live_cases {
                    if *cases_remaining == 0 { break; }
                    // Give this alternative its share plus accumulated
                    // leftover from earlier alternatives that finished
                    // under budget.  Always at least 1 so no alternative
                    // is silently dropped.
                    let mut alt_budget = (per_alt + leftover).min(*cases_remaining);
                    if alt_budget == 0 { alt_budget = (*cases_remaining).min(1); }
                    let pre = alt_budget;
                    let alt_results = close_chains_dfs(
                        ctx, c_sys, budget - 1, this_term.as_ref(), &mut alt_budget);
                    let used = pre.saturating_sub(alt_budget);
                    // Deduct used budget from the shared counter.
                    *cases_remaining = cases_remaining.saturating_sub(used);
                    // Carry leftover forward to later alternatives.
                    leftover = (per_alt + leftover).saturating_sub(used);
                    out.extend(alt_results);
                }
                out
            }
        }
    }
    // Read the first term of node `c.0`'s conclusion `c.1`.
    fn chain_conc_term(sys: &System, c: &crate::constraint::constraints::NodeConc)
        -> Option<tamarin_term::lterm::LNTerm>
    {
        let (id, idx) = (&c.0, &c.1);
        let rule = sys.nodes.iter().find(|(n, _)| n == id).map(|(_, r)| r)?;
        let fact = rule.conclusions.get(idx.0)?;
        fact.terms.first().cloned()
    }
    // Same as chain_conc_term but only returns Some when the conclusion
    // is KD-tagged.  Used by the msg-var KD chain filter.
    fn chain_kd_conc_term_local(sys: &System, c: &crate::constraint::constraints::NodeConc)
        -> Option<tamarin_term::lterm::LNTerm>
    {
        use crate::fact::FactTag;
        let (id, idx) = (&c.0, &c.1);
        let rule = sys.nodes.iter().find(|(n, _)| n == id).map(|(_, r)| r)?;
        let fact = rule.conclusions.get(idx.0)?;
        if fact.tag != FactTag::Kd { return None; }
        fact.terms.first().cloned()
    }
    fn is_msg_var_local(t: &tamarin_term::lterm::LNTerm) -> bool {
        use tamarin_term::lterm::LSort;
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        matches!(t, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg)
    }
    // Structural equality modulo fresh variable renaming and AC.
    // Mirrors Haskell's `eqModuloFreshnessNoAC` (LTerm.hs:632):
    //   normIndices = mapFrees (Arbitrary $ \x -> importBinding (LVar lvarSort x) x "")
    // Two terms are equal modulo freshness iff they're structurally
    // identical after renaming every free var to a fresh canonical
    // name preserving ONLY sort (name and idx are reset).
    //
    // The earlier port compared `va.name == vb.name && va.sort == vb.sort`
    // which is too strict — `enc(x:Msg, ~k:Fresh)` vs `enc(y:Msg, ~m:Fresh)`
    // would NOT be equal-mod-freshness in Rust but ARE in Haskell.  This
    // under-detected chain loops in close_chains_dfs, letting Rust extend
    // chains where Haskell would loop-break.  Root cause of task #164
    // denning_sacco Initiator2_case_N over-enumeration: Rust enumerates
    // chain extensions that Haskell drops via `lastChainTerm` filter.
    fn eq_modulo_freshness(
        a: &tamarin_term::lterm::LNTerm,
        b: &tamarin_term::lterm::LNTerm,
    ) -> bool {
        use tamarin_term::lterm::LVar;
        use std::collections::HashMap;
        // Walk both terms in lockstep, assigning each var pair a
        // canonical idx.  Two vars at corresponding positions must
        // (a) have the same sort and (b) map to the same canonical idx.
        fn go(
            a: &tamarin_term::lterm::LNTerm,
            b: &tamarin_term::lterm::LNTerm,
            ma: &mut HashMap<LVar, u64>,
            mb: &mut HashMap<LVar, u64>,
            next: &mut u64,
        ) -> bool {
            use tamarin_term::term::Term;
            use tamarin_term::vterm::Lit;
            match (a, b) {
                (Term::Lit(Lit::Var(va)), Term::Lit(Lit::Var(vb))) => {
                    if va.sort != vb.sort { return false; }
                    let ka = ma.get(va).cloned();
                    let kb = mb.get(vb).cloned();
                    match (ka, kb) {
                        (Some(x), Some(y)) => x == y,
                        (None, None) => {
                            let k = *next;
                            *next += 1;
                            ma.insert(va.clone(), k);
                            mb.insert(vb.clone(), k);
                            true
                        }
                        _ => false,
                    }
                }
                (Term::Lit(Lit::Con(ca)), Term::Lit(Lit::Con(cb))) => ca == cb,
                (Term::App(oa, xs), Term::App(ob, ys)) =>
                    oa == ob && xs.len() == ys.len()
                        && xs.iter().zip(ys).all(|(x, y)| go(x, y, ma, mb, next)),
                _ => false,
            }
        }
        let mut ma = HashMap::new();
        let mut mb = HashMap::new();
        let mut next = 0;
        go(a, b, &mut ma, &mut mb, &mut next)
    }
    // Cap on closures per source — bounds the explosion when user
    // equations introduce many destructors. Default 256; tunable via
    // TAM_MAX_CLOSURES_PER_SOURCE.  Haskell prunes via removeRedundant
    // Cases + protocol-specific heuristics that we don't fully port.
    // Threaded through close_chains_dfs so DFS terminates early when
    // the per-source cap is reached (not just at the outer loop).
    let max_closures: usize = std::env::var("TAM_MAX_CLOSURES_PER_SOURCE")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(256);
    // Per-chain destructor-extension budget.  Mirrors Haskell's
    // `openChainsLimit` (Sources.hs:144-215, default 10 from
    // `TheoryLoader.hs:244`).  Each recursive `close_chains_dfs` call
    // decrements this budget on a successful chain-extension step; when
    // it hits 0, `safeGoal` in Haskell's `solveAllSafeGoals` returns
    // False for `ChainG _ _` and the chain stays open.  Previously
    // hardcoded to 8 — two steps shorter than Haskell, which truncated
    // legitimately reachable destructor cases on protocols like NSPK3
    // (KU(t:Fresh) source enumeration via I_2's deeper d_aenc chain).
    // Tunable via TAM_CHAIN_BUDGET; default 10 matches Haskell.
    let chain_budget: usize = std::env::var("TAM_CHAIN_BUDGET")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(10);
    // Divide the closure budget across raw sub_names so each
    // top-level producer rule (e.g. Register_pk_Bank, B_1, S_1) gets
    // a fair share.  Without this, a single explosive sub_name (one
    // that fans out via user-equation destructors like `unblind`)
    // would consume the entire budget and starve the others — which
    // is exactly what happened on chaum_unforgeability / foo_eligibility:
    // `Register_pk_Bank` ate all 256 closures, leaving `B_1`
    // (the protocol's actual signing rule) unenumerated. The remaining
    // budget is given to the first sub_name to avoid wasting it
    // when most sub_names produce few closures.
    let n_subs = raw.len().max(1);
    let per_sub_share = max_closures / n_subs;
    let mut leftover = max_closures - per_sub_share * n_subs;
    for (sub_name, sys) in raw {
        if closed_cases.len() >= max_closures {
            *incomplete_out = true;
            break;
        }
        // Give this sub_name its share plus any unused leftover from
        // earlier sub_names that finished under budget.  Always at
        // least 1 so we never silently drop a producer entirely.
        let mut cases_remaining = (per_sub_share + leftover).max(1);
        let pre = cases_remaining;
        let close_results = close_chains_dfs(ctx, sys, chain_budget, None, &mut cases_remaining);
        let used = pre.saturating_sub(cases_remaining);
        // Carry forward unused share so producers that finish quickly
        // donate their budget to later (potentially explosive) ones.
        leftover = (per_sub_share + leftover).saturating_sub(used);
        if std::env::var("TAM_DBG_SAT").is_ok() {
            eprintln!("[sat]   close_chains_dfs sub_name={:?} share={} → {} closures",
                sub_name, pre, close_results.len());
        }
        // Buffer this sub_name's closures first so we can decide names
        // based on the kept count (Haskell convention: a single
        // surviving closure has no `_case_N` suffix; multiple get
        // 1-based suffixes).
        let mut this_sub: Vec<System> = Vec::new();
        // Dedup chain-extension paths by canonical structural form.
        // close_chains_dfs enumerates ALL viable destructor-chain
        // combinations; many produce structurally-equivalent final
        // source-cases (same nodes/edges, just walked through different
        // destructor intermediates).  Haskell's saturate-time apply
        // selects via runtime matching, naturally collapsing
        // structurally-equivalent paths to one rendered case.
        // Without dedup, our runtime apply produces hundreds of
        // `_case_N` survivors for what Haskell renders as one case
        // (e.g. denning_sacco Initiator2_case_1..164).
        // Haskell-faithful `removeRedundantCases` gate (Sources.hs:240):
        // BP/MSet only.  Outside those theories, sibling cases with same
        // canonical form (post `restrict stableVars`) must be PRESERVED
        // so the runtime renderer's `distinguish` can rename them
        // `RULE_case_1`/`RULE_case_2`.  Collapsing them here causes the
        // FOO/TLS/NSLPK3 case_N cluster — Haskell renders 5 sibling
        // cases under C_1 (A_1, V_1_case_1, V_1_case_2, V_2, c_sign),
        // Rust drops A_1 because two A_1-rooted closures canonicalise
        // equal after restrict.
        let sub_canon_dedup = {
            let s = ctx.maude.maude_sig();
            s.enable_bp || s.enable_mset
        };
        let mut sub_canon_seen: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        for s in close_results.into_iter() {
            if !chain_acceptable(&s) { continue; }
            if closed_cases.len() + this_sub.len() >= max_closures {
                *incomplete_out = true;
                break;
            }
            if sub_canon_dedup {
                let canon = canonicalise_system(&s);
                if !sub_canon_seen.insert(canon) { continue; }
            }
            this_sub.push(s);
        }
        let multi = this_sub.len() > 1;
        for (k, s) in this_sub.into_iter().enumerate() {
            let base_name = if !sub_name.is_empty() {
                format!("{}_{}", outer_name, sub_name)
            } else {
                let final_producer = producer_name(&s);
                format!("{}_{}", outer_name, final_producer)
            };
            let name = if multi {
                format!("{}_case_{}", base_name, k + 1)
            } else {
                base_name
            };
            closed_cases.push((name, s));
        }
    }
    set_precompute_mode(false);
    if closed_cases.is_empty() { return None; }
    Some(closed_cases)
}

/// First open KU action goal — used for source-case expansion during
/// saturation.  Mirrors part of Haskell's `solveAllSafeGoals` arm for
/// `ActionG _ fa` where `isKUFact fa`.  These goals arise from
/// destructor-rule premises (`d_aenc`, `d_senc`, etc.) being grafted
/// during chain saturation: their `!KU(aenc(...))` and `!KU(ltkA)`
/// premises spawn as Action goals at fresh sub-nodes.
fn first_open_ku_action_goal(
    sys: &System,
) -> Option<(crate::constraint::constraints::NodeId, crate::fact::LNFact)> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    sys.goals.iter().find_map(|(g, st)| {
        if st.solved { return None; }
        if st.looping { return None; }
        match g {
            Goal::Action(i, fa) if matches!(fa.tag, FactTag::Ku) => {
                // Skip KU actions on terms that are auto-handled by
                // openGoals (pair / inv / product / union / pub /
                // nat) — these are decomposed at insert time, not
                // expanded via source-case graft.
                let m = fa.terms.first()?;
                if let tamarin_term::term::Term::App(
                    tamarin_term::function_symbols::FunSym::NoEq(s), _) = m
                {
                    if s.name == b"pair" { return None; }
                    use tamarin_term::function_symbols::INV_SYM_STRING;
                    if s.name == INV_SYM_STRING { return None; }
                }
                Some((i.clone(), fa.clone()))
            }
            _ => None,
        }
    })
}

/// Return a stable label for a source's goal pattern — used by the
/// filterCases tracking in `saturate_sources_inner_with_options`.  Two
/// sources with the same pattern term-head get the same label, so the
/// per-case `used` set correctly excludes them from re-application.
///
/// For KU-action sources: `"KU:<head>"` where `<head>` is `"fresh"`
/// for a Fresh-sorted variable pattern, the function-symbol name for
/// constructor patterns, or `"msg"` for a Msg-sorted variable.
/// For Premise sources: `"PR:<tag>"` where tag is the fact-tag debug.
/// Other goal kinds: None.
pub(crate) fn source_label(src: &Source) -> Option<String> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    match &src.goal {
        Goal::Action(_, fa) if fa.tag == FactTag::Ku && fa.terms.len() == 1 =>
            ku_source_label_for_fa(fa),
        Goal::Premise(_, fa) => Some(format!("PR:{:?}", fa.tag)),
        _ => None,
    }
}

/// Compute the source label that would identify a KU-action source
/// matching the given live `fa` (a KU fact with a single term).
/// Mirrors `source_label`'s KU arm — used at the runtime filterCases
/// step where we have the live fa (not the source).  Two KU sources
/// are identified as "the same source" when their labels are equal,
/// approximating Haskell's full-`Source` equality (Sources.hs:218-219
/// `filterCases usedCase cds = filter (\x -> usedCase /= x) cds`).
pub(crate) fn ku_source_label_for_fa(
    fa: &crate::fact::LNFact,
) -> Option<String> {
    use crate::fact::FactTag;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_term::lterm::LSort;
    if fa.tag != FactTag::Ku || fa.terms.len() != 1 {
        return None;
    }
    match &fa.terms[0] {
        Term::Lit(Lit::Var(v)) => Some(match v.sort {
            LSort::Fresh => "KU:fresh".to_string(),
            LSort::Pub => "KU:pub".to_string(),
            LSort::Nat => "KU:nat".to_string(),
            LSort::Node => "KU:node".to_string(),
            LSort::Msg => "KU:msg".to_string(),
        }),
        Term::App(tamarin_term::function_symbols::FunSym::NoEq(s), _) =>
            Some(format!("KU:{}", String::from_utf8_lossy(&s.name))),
        Term::App(tamarin_term::function_symbols::FunSym::Ac(_), _) =>
            Some("KU:ac".to_string()),
        Term::App(tamarin_term::function_symbols::FunSym::C(_), _) =>
            Some("KU:c".to_string()),
        Term::App(tamarin_term::function_symbols::FunSym::List, _) =>
            Some("KU:list".to_string()),
        _ => None,
    }
}

/// Expand an open KU action goal in `sys` by grafting a matching
/// source-case from `sources` (the current saturating list).
/// Mirrors Haskell's `solveWithSourceAndReturn` step in
/// `solveAllSafeGoals`.  Returns the chain-saturated sub-cases or
/// None if no matching source applies.
fn saturate_ku_action_via_sources(
    ctx: &crate::constraint::solver::context::ProofContext,
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    fa_ku: &crate::fact::LNFact,
    outer_name: &str,
) -> Option<Vec<(String, System)>> {
    use crate::constraint::solver::reduction::{Reduction, SolveOutcome, SplitStrategy};
    use crate::constraint::solver::contradictions::contradictions;
    let avoid_max = system_max_idx(sys);
    let case_pairs = solve_with_source_cases_action(
        sources, sys, goal_node, fa_ku, avoid_max)?;
    let mut out: Vec<(String, System)> = Vec::new();
    set_precompute_mode(true);
    let live_goal = crate::constraint::constraints::Goal::Action(
        goal_node.clone(), fa_ku.clone());
    for (case_label, grafted, case_action) in case_pairs {
        let mut sub = Reduction::new(ctx, grafted);
        // Unify the case's KU action with the live KU action.
        let res = sub.solve_fact_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal {
                lhs: case_action.clone(), rhs: fa_ku.clone() }]);
        match res {
            Err(_) | Ok(SolveOutcome::Contradictory) => continue,
            Ok(_) => {}
        }
        sub.subst_system();
        // Skip cases that hit immediate contradiction after subst.
        if !contradictions(ctx, &sub.sys).is_empty() { continue; }
        // Mark the live KU goal as solved.  Mirrors Haskell's
        // `_applySource` (Sources.hs:346) which calls
        // `markGoalAsSolved "precomputed" goal` before conjoinSystem.
        // Without this, the KU sub-goal stays open in the
        // saturated case-system and runtime's smartRanking picks
        // it instead of the protocol-rule-driven sub-goal.
        for (g, st) in sub.sys.goals.iter_mut() {
            if g == &live_goal { st.solved = true; break; }
        }
        // Haskell `refineSource.combine` (Sources.hs:135-137):
        //   combine (n:_) _ = [n]
        // — keep the FIRST non-coerce name, DISCARD the new step's
        // name.  So `combine ["B_1_case_1"] ["c_blind"]` = ["B_1_case_1"].
        //
        // Previously we used `format!("{}_{}", outer_name, case_label)`
        // which appends the source's case_label (e.g. `c_blind`).  The
        // renderer's `saturated_chain_root` then strips the `_case_<N>_`
        // middle of `B_1_case_1_c_blind`, leaving `c_blind` — but the
        // case is actually a chain-folded variant of KU(sign) via B_1.
        //
        // Haskell renders this case as `B_1` (it never had the
        // `c_blind` suffix in the first place).  Use `combine_case_names`
        // to match.
        let name = combine_case_names(outer_name, &case_label);
        out.push((name, sub.sys));
    }
    set_precompute_mode(false);
    if out.is_empty() { return None; }
    Some(out)
}

/// First open intruder-chain premise (`Out` or `KD`) — used for
/// chain-folding during saturation.  Intruder rules `coerce` (has KD
/// premise) and `irecv` (has Out premise) appear in KU source-cases
/// with their input premises still open; if we leave them open,
/// runtime sees them as nested cases (`case coerce / case irecv /
/// case <rule>`) rather than as a single saturated `case <rule>`.
/// Mirrors Haskell's `solveAllSafeGoals` which iterates `solveGoal`
/// on every "safe" goal during `saturateSources`.
fn first_open_out_premise(
    sys: &System,
) -> Option<(crate::constraint::constraints::NodePrem, crate::fact::LNFact)> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    sys.goals.iter().find_map(|(g, st)| {
        if st.solved { return None; }
        if st.looping { return None; }
        match g {
            Goal::Premise(p, fa) if matches!(fa.tag, FactTag::Out | FactTag::Kd)
                => Some((p.clone(), fa.clone())),
            _ => None,
        }
    })
}

/// Apply an `LVar → LNTerm` substitution to every term in a `System`.
/// Used by saturation to align abstract source terms with the open-
/// premise live terms before grafting (so subsequent graft calls
/// don't introduce dangling `t_i` placeholders).
fn apply_lvar_subst(
    sys: &System,
    subst: &std::collections::BTreeMap<
        tamarin_term::lterm::LVar,
        tamarin_term::lterm::LNTerm>,
) -> System {
    use tamarin_term::lterm::HasFrees;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    if subst.is_empty() { return sys.clone(); }
    // Walk LVars: if mapped to a Var, rename in place; otherwise
    // bail back to a no-op rename for that one var.  Full term-
    // substitution is only needed when a target is non-Var, which
    // doesn't arise from `precompute_full_sources` (all abstract
    // terms are vars).
    let mut out = sys.clone();
    let map_var = |v: tamarin_term::lterm::LVar| {
        if let Some(t) = subst.get(&v) {
            if let Term::Lit(Lit::Var(nv)) = t { nv.clone() }
            else { v }
        } else { v }
    };
    out.nodes = out.nodes.into_iter()
        .map(|(id, ru)| {
            let new_id = if let Some(t) = subst.get(&id) {
                if let Term::Lit(Lit::Var(nv)) = t { nv.clone() }
                else { id }
            } else { id };
            (new_id, ru.map_free(&mut |v| map_var(v)))
        })
        .collect();
    out.edges = out.edges.into_iter()
        .map(|e| {
            let new_src = if let Some(t) = subst.get(&e.src.0) {
                if let Term::Lit(Lit::Var(nv)) = t { nv.clone() } else { e.src.0.clone() }
            } else { e.src.0.clone() };
            let new_tgt = if let Some(t) = subst.get(&e.tgt.0) {
                if let Term::Lit(Lit::Var(nv)) = t { nv.clone() } else { e.tgt.0.clone() }
            } else { e.tgt.0.clone() };
            crate::constraint::constraints::Edge {
                src: (new_src, e.src.1),
                tgt: (new_tgt, e.tgt.1),
            }
        })
        .collect();
    out.less_atoms = out.less_atoms.into_iter()
        .map(|l| {
            let smaller = if let Some(t) = subst.get(&l.smaller) {
                if let Term::Lit(Lit::Var(nv)) = t { nv.clone() } else { l.smaller.clone() }
            } else { l.smaller.clone() };
            let larger = if let Some(t) = subst.get(&l.larger) {
                if let Term::Lit(Lit::Var(nv)) = t { nv.clone() } else { l.larger.clone() }
            } else { l.larger.clone() };
            crate::constraint::constraints::LessAtom::new(smaller, larger, l.reason)
        })
        .collect();
    out.goals = out.goals.into_iter()
        .map(|(g, st)| {
            let g2 = match g {
                crate::constraint::constraints::Goal::Premise(p, fa) => {
                    let new_p0 = if let Some(t) = subst.get(&p.0) {
                        if let Term::Lit(Lit::Var(nv)) = t { nv.clone() } else { p.0 }
                    } else { p.0 };
                    crate::constraint::constraints::Goal::Premise(
                        (new_p0, p.1),
                        fa.map_free(&mut |v| map_var(v)))
                }
                crate::constraint::constraints::Goal::Action(n, fa) => {
                    let new_n = if let Some(t) = subst.get(&n) {
                        if let Term::Lit(Lit::Var(nv)) = t { nv.clone() } else { n }
                    } else { n };
                    crate::constraint::constraints::Goal::Action(
                        new_n,
                        fa.map_free(&mut |v| map_var(v)))
                }
                other => other,
            };
            (g2, st)
        })
        .collect();
    // Also rewrite the eq_store: both the free subst (keys + RHS
    // terms) and the conjunctive disj substs.  Without this, the
    // saturate's sort-narrowing rewrites system nodes from
    // `kZero:Msg:2` to `kZero:Fresh:2` while the eq_store keeps
    // stale bindings like `t:Msg:1 → kZero:Msg:2` — orphan because
    // `kZero:Msg:2` is no longer referenced anywhere.  Runtime
    // applySource can't chase `t → seed:Fresh` through this
    // disconnected chain, so matchSubst doesn't reach the case's
    // saturated terms.  Minimal_HashChain (3 lemmas) wrong-falsified
    // root cause.
    let lookup_term = |v: &tamarin_term::lterm::LVar| -> tamarin_term::lterm::LNTerm {
        subst.get(v).cloned().unwrap_or_else(|| Term::Lit(Lit::Var(v.clone())))
    };
    out.eq_store.subst = {
        let pairs: Vec<_> = out.eq_store.subst.to_list().into_iter()
            .map(|(v, t)| {
                let new_v = if let Some(replacement) = subst.get(&v) {
                    if let Term::Lit(Lit::Var(nv)) = replacement {
                        nv.clone()
                    } else { v }
                } else { v };
                let new_t = t.map_free(&mut |w| {
                    if let Term::Lit(Lit::Var(nw)) = lookup_term(&w) {
                        nw
                    } else { w }
                });
                (new_v, new_t)
            })
            .collect();
        tamarin_term::subst::Subst::from_list(pairs)
    };
    for disj in out.eq_store.conj.iter_mut() {
        for s in disj.substs.iter_mut() {
            let pairs: Vec<_> = s.to_list().into_iter()
                .map(|(v, t)| {
                    let new_v = if let Some(replacement) = subst.get(&v) {
                        if let Term::Lit(Lit::Var(nv)) = replacement {
                            nv.clone()
                        } else { v }
                    } else { v };
                    let new_t = t.clone().map_free(&mut |w| {
                        if let Term::Lit(Lit::Var(nw)) = lookup_term(&w) {
                            nw
                        } else { w }
                    });
                    (new_v, new_t)
                })
                .collect();
            *s = tamarin_term::subst_vfresh::SubstVFresh::from_list(pairs);
        }
    }
    out
}

fn system_max_idx(sys: &System) -> u64 {
    use std::cell::Cell;
    use tamarin_term::lterm::HasFrees;
    use crate::constraint::constraints::Goal;
    let max = Cell::new(0u64);
    let mut visit = |v: &tamarin_term::lterm::LVar| {
        let cur = max.get();
        if v.idx > cur { max.set(v.idx); }
    };
    for (id, ru) in &sys.nodes {
        id.for_each_free(&mut visit);
        ru.for_each_free(&mut visit);
    }
    for e in &sys.edges {
        e.src.0.for_each_free(&mut visit);
        e.tgt.0.for_each_free(&mut visit);
    }
    for l in &sys.less_atoms {
        l.smaller.for_each_free(&mut visit);
        l.larger.for_each_free(&mut visit);
    }
    if let Some(la) = &sys.last_atom {
        la.for_each_free(&mut visit);
    }
    // Goals: walk node-ids and fact terms.
    for (g, _) in &sys.goals {
        match g {
            Goal::Action(i, fa) => {
                i.for_each_free(&mut visit);
                fa.for_each_free(&mut visit);
            }
            Goal::Premise(p, fa) => {
                p.0.for_each_free(&mut visit);
                fa.for_each_free(&mut visit);
            }
            Goal::Chain(c, p) => {
                c.0.for_each_free(&mut visit);
                p.0.for_each_free(&mut visit);
            }
            Goal::Subterm((s, t)) => {
                s.for_each_free(&mut visit);
                t.for_each_free(&mut visit);
            }
            Goal::Disj(_) | Goal::Split(_) => {}
        }
    }
    // Formulas (Guarded over parser AST) — use the explicit max helper.
    for f in sys.formulas.iter()
        .chain(sys.solved_formulas.iter())
        .chain(sys.lemmas.iter())
    {
        let n = crate::guarded::max_var_idx(f);
        if n > max.get() { max.set(n); }
    }
    // Eq-store: domain + range vars must not collide with freshened sub-case
    // vars.  Without including these here, a sub-case freshened against an
    // outer system that has high-idx Maude witnesses in its eq-store
    // (e.g. from a prior solve_fact_eqs) can be assigned colliding idxs,
    // causing the rule-var conflation diagnosed in task #119.
    for (v, t) in sys.eq_store.subst.to_list() {
        if v.idx > max.get() { max.set(v.idx); }
        t.for_each_free(&mut visit);
    }
    for d in &sys.eq_store.conj {
        for s in &d.substs {
            for (v, t) in s.to_list() {
                if v.idx > max.get() { max.set(v.idx); }
                t.for_each_free(&mut visit);
            }
        }
    }
    max.get()
}

/// `refineWithSourceAsms` — direct port of Haskell's
/// `Theory.Constraint.Solver.Sources.refineWithSourceAsms`.
///
/// Takes the precomputed (saturated) source cases and a list of
/// `[sources]`-tagged lemma formulas, and prunes any case whose
/// system becomes contradictory once the assumptions are folded in.
/// Mirrors the Haskell flow:
///
/// ```text
///   for each (name, sys) in src.cases:
///     sys' = sys with assumptions added to formulas
///     re-simplify sys'
///     if simplifySystem produced a contradiction → drop the case
///     else → strip the assumptions back out (they were only added
///            for refinement) and keep
/// ```
///
/// Without this, the precomputed source cases include ones that
/// violate the user's typing/`[sources]` invariants — at runtime,
/// our search explores those spurious cases and reports false
/// counterexamples.
pub fn refine_with_source_asms(
    sources: Vec<Source>,
    assumptions: &[crate::guarded::Guarded],
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    if assumptions.is_empty() { return sources; }

    // Step 1: match Haskell's `updateSystem` (Sources.hs:466-468):
    //
    //   updateSystem se =
    //     modify sFormulas (S.union (S.fromList assumptions)) $
    //     set sSourceKind RefinedSource                       $ se
    //
    // Just inject assumptions into formulas — no simplify, no drop.
    // Haskell's `saturateSources` then handles drops via
    // `solveAllSafeGoals` Disj-monad (our `run_solve_all_safe_goals_disj`
    // mzero-equivalent).  Dropping in Step 1 with single-pass simplify
    // is non-Haskell-faithful — it misses cases where the typing
    // violation only surfaces after exhaustive Disj exploration.
    let mut intermediate: Vec<Source> = Vec::new();
    for src in sources {
        let mut new_cases: Vec<(String, System)> = Vec::new();
        for (name, sys) in src.cases {
            let mut refined = sys.clone();
            for a in assumptions {
                if !refined.formulas.contains(a) && !refined.solved_formulas.contains(a) {
                    refined.formulas.push(a.clone());
                }
            }
            // Mirror Haskell `set sSourceKind RefinedSource`.
            refined.source_kind = Some(crate::constraint::system::SourceKind::RefinedSources);
            new_cases.push((name, refined));
        }
        if !new_cases.is_empty() {
            intermediate.push(Source { goal: src.goal, cases: new_cases, incomplete: src.incomplete });
        }
    }

    // Step 2 (Haskell `saturateSources`): re-saturate with the
    // assumption-augmented cases.  This is the critical step our
    // earlier port skipped — it propagates the typing constraints
    // through the recursive premise expansion, pruning cases whose
    // continuation introduces premises that violate the [sources]
    // typing.
    // Haskell uses `paramSaturationLimit=5` for `saturateSources`. Our
    // multi-branch port grows the case set with each iteration (each
    // iter forks at every source-pick).  Capping iterations bounds
    // growth.  `TAM_REFINE_SAT_LIMIT` overrides.
    let limit: usize = std::env::var("TAM_REFINE_SAT_LIMIT")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(5);
    let saturated = saturate_sources_with_simp(intermediate, limit, ctx);

    // Step 3 (Haskell `removeFormulas`): strip formulas + solved
    // formulas after saturation, and drop disjunction goals derived
    // from the assumptions.
    let mut out: Vec<Source> = Vec::new();
    for mut src in saturated {
        let mut new_cases: Vec<(String, System)> = Vec::new();
        for (name, mut sys) in src.cases.drain(..) {
            sys.formulas.clear();
            sys.solved_formulas.clear();
            sys.goals.retain(|(g, _)|
                !matches!(g, crate::constraint::constraints::Goal::Disj(_)));
            new_cases.push((name, sys));
        }
        if !new_cases.is_empty() {
            out.push(Source { goal: src.goal, cases: new_cases, incomplete: src.incomplete });
        }
    }
    out
}

/// Convert an LVar→LNTerm map into an LNSubst usable by apply_vterm.
fn lvar_map_to_subst(
    m: &std::collections::BTreeMap<
        tamarin_term::lterm::LVar,
        tamarin_term::lterm::LNTerm>,
) -> tamarin_term::subst::Subst<tamarin_term::lterm::Name, tamarin_term::lterm::LVar> {
    tamarin_term::subst::Subst::from_list(
        m.iter().map(|(v, t)| (v.clone(), t.clone())))
}

/// Maude-align a grafted system: run `solve_fact_eqs(SplitNow, [conc =
/// fa])` on the system so that order-sorted AC unification narrows
/// sorts and equates shared sub-terms.  Then run `simplify_system` to
/// propagate the resulting eq-store substitution.  Returns `None` if
/// the alignment surfaces a contradiction.
fn maude_align_and_simplify(
    ctx: &crate::constraint::solver::context::ProofContext,
    grafted: System,
    conc_fact: &crate::fact::LNFact,
    fa_prem: &crate::fact::LNFact,
) -> Option<System> {
    use crate::constraint::solver::reduction::{
        Reduction, SolveOutcome, SplitStrategy};
    use crate::constraint::solver::contradictions::contradictions;
    let mut r = Reduction::new(ctx, grafted);
    let res = r.solve_fact_eqs(
        SplitStrategy::SplitNow,
        &[tamarin_term::rewriting::Equal {
            lhs: conc_fact.clone(),
            rhs: fa_prem.clone(),
        }],
    );
    match res {
        Err(_) | Ok(SolveOutcome::Contradictory) => return None,
        _ => {}
    }
    // Apply the freshly-built eq-store substitution to the system so
    // narrowed sorts and equated subterms propagate into nodes/edges.
    // We deliberately DON'T run the full `simplify_system` here — that
    // would fire CR-rules (enforce_*, simp_injective, etc.) which can
    // introduce extra equations that the saturation iteration is not
    // expecting and which spuriously merge cases.  Just propagate.
    r.subst_system();
    if !contradictions(ctx, &r.sys).is_empty() { return None; }
    Some(r.sys)
}

/// Variant of `saturate_sources` that re-simplifies every grafted
/// case so that any newly-fired implied formulas (from the assumption
/// universals) get a chance to prune.  Mirrors Haskell's
/// `saturateSources` invocation inside `refineWithSourceAsms`.
fn saturate_sources_with_simp(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    saturate_sources_with_simp_opt(sources, limit, ctx, /*aggressive_drop=*/false)
}

fn saturate_sources_with_simp_opt(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
    aggressive_drop: bool,
) -> Vec<Source> {
    use crate::constraint::solver::contradictions::contradictions;
    use crate::constraint::solver::reduction::Reduction;
    let mut current = sources;
    let dbg = std::env::var("TAM_DBG_REFINE").is_ok();
    if dbg {
        eprintln!("[refine] starting saturate_sources_with_simp over {} sources",
            current.len());
        for (i, src) in current.iter().enumerate() {
            eprintln!("  source[{}] goal={:?}", i, src.goal);
            for (n, sys) in &src.cases {
                let open_count = sys.goals.iter().filter(|(_, st)| !st.solved).count();
                eprintln!("    case {:?}: {} formulas, {} open goals, {} nodes, eq_store={} entries",
                    n, sys.formulas.len(), open_count, sys.nodes.len(),
                    sys.eq_store.subst.to_list().len());
                if n.contains("Initiator_Setup_Key") {
                    for (v, t) in sys.eq_store.subst.to_list().iter() {
                        let v_str = format!("{}#{}({:?})", v.name, v.idx, v.sort);
                        let t_str = format!("{:?}", t).chars().take(180).collect::<String>();
                        eprintln!("      eq {} → {}", v_str, t_str);
                    }
                    for (nid, rule) in &sys.nodes {
                        let rname = match &rule.info {
                            crate::rule::RuleInfo::Proto(p) =>
                                format!("Proto({:?})", p.name),
                            crate::rule::RuleInfo::Intr(i) =>
                                format!("Intr({:?})", i),
                        };
                        eprintln!("      node {:?} = {}", nid, rname);
                        for p in &rule.premises {
                            eprintln!("        prem  tag={:?} terms={:?}",
                                p.tag,
                                p.terms.first().map(|t|
                                    format!("{:?}", t).chars().take(80).collect::<String>())
                                .unwrap_or_default());
                        }
                        for a in &rule.actions {
                            eprintln!("        act   tag={:?} terms={:?}",
                                a.tag,
                                a.terms.first().map(|t|
                                    format!("{:?}", t).chars().take(80).collect::<String>())
                                .unwrap_or_default());
                        }
                        for c in &rule.conclusions {
                            eprintln!("        conc  tag={:?} terms={:?}",
                                c.tag,
                                c.terms.first().map(|t|
                                    format!("{:?}", t).chars().take(80).collect::<String>())
                                .unwrap_or_default());
                        }
                    }
                    for e in &sys.edges {
                        eprintln!("      edge {:?}.{:?} → {:?}.{:?}",
                            e.src.0, e.src.1, e.tgt.0, e.tgt.1);
                    }
                    for (g, st) in &sys.goals {
                        eprintln!("      goal solved={} {:?}", st.solved, g);
                    }
                }
            }
        }
    }
    for _ in 0..limit {
        // Use the Maude-backed saturate here.  Inside
        // refine_with_source_asms the source-case formulas already
        // carry the [sources] assumption universals, so the Maude
        // alignment + simp loop has visibility into the typing
        // constraints and can prune cases that violate them.  The
        // top-level context init uses the lightweight aligner because
        // it doesn't have the assumptions to drive pruning.
        let saturated = saturate_sources_maude(current.clone(), 1, ctx);
        // Haskell-faithful `goodTh` filter (Sources.hs:380-381):
        //
        //   goodTh th = length (getDisj (get cdCases th)) <= 1
        //   solver = solveAllSafeGoals (filter goodTh ths) ...
        //
        // Haskell passes ONLY single-case sources to `solveAllSafeGoals`
        // during refine/saturate.  This is what bounds Haskell's
        // multi-branch refineSource case-set growth.  Without it,
        // multi-branch explodes to 234+ cases for NSPK3 Pre/Secret
        // (vs Haskell's handful), losing the Lowe attack case.
        //
        // BUT: applying this filter under our (legacy) single-pick
        // saturate regresses corpus from 53/103 to 49/97 (single-pick's
        // saturate relies on having full source-set to drive typing
        // refinements).  So we apply the filter ONLY when multi-branch
        // is active.  Haskell always uses multi-branch with the filter
        // paired.
        let multi_branch_active = std::env::var("TAM_LEGACY_SINGLE_PICK").is_err();
        let ths_snapshot: Vec<Source> = if multi_branch_active {
            saturated.iter()
                .filter(|s| s.cases.len() <= 1)
                .cloned()
                .collect()
        } else {
            saturated.clone()
        };
        // Inside refine_with_source_asms, drive each case forward by
        // SOLVING its safe goals (chain/KD-premise/non-KU action) —
        // not just simplifying.  Mirrors Haskell's `solveAllSafeGoals`-
        // driven `saturateSources` (`Sources.hs:144,355`).  This is
        // what propagates typing assumptions transitively: each safe
        // goal we solve adds a new node/edge whose fact constraints
        // get unified against the assumption's pattern, eventually
        // pruning typing-violating cases.  Bare simplify alone misses
        // most of these because the impl_formulas pass relies on
        // term-shape match against system actions, which only get
        // grafted by goal-solving.
        let mut next: Vec<Source> = Vec::new();
        let mut changed = false;
        // Haskell-faithful multi-branch refineSource (task #160):
        // run the saturate as a Disj of branches per input case,
        // emit each surviving branch as its own output case.  This
        // is what `refineSource` (Sources.hs:118-133) does via
        // `runReduction proofStep ctxt se fs`.
        //
        // Per-input-case branch cap (TAM_DISJ_BRANCH_CAP, default 50):
        // bounds the worklist size to avoid exponential blow-up on
        // protocols with many source-pick candidates.  Haskell uses
        // lazy evaluation to dodge this; we need an explicit cap.
        let branch_cap: usize = std::env::var("TAM_DISJ_BRANCH_CAP")
            .ok().and_then(|s| s.parse().ok()).unwrap_or(50);
        // Default is single-pick saturate (pre-#160 behaviour) — it
        // gives 53/103 corpus baseline and finds NSPK3 attack within
        // budget=500.  TAM_DISJ_REFINE=1 enables Haskell-faithful
        // multi-branch refineSource, which produces ~5x more output
        // cases per input case (matching Haskell's `runReduction
        // proofStep ctxt se fs` Disj output).  The increased case
        // count exhausts the corpus probe's default budget on attack
        // lemmas (NSPK3 nonce_secrecy → Sorry instead of Solved)
        // but improves proof-tree fidelity for typing-class lemmas
        // where Haskell's multi-case output is load-bearing.
        // Haskell-faithful default: multi-branch refineSource.
        // Sources.hs's `saturateSources` runs `solveAllSafeGoals`
        // through the `Reduction` monad which is `Disj`-shaped — every
        // branch survives or dies independently via `mzero`.  The
        // surviving branches become separate output cases.
        //
        // Combined with the `goodTh` filter (Sources.hs:380-381),
        // case-set growth is bounded so attack-class lemmas (NSPK3)
        // remain findable via runtime case enumeration.  Toggle off
        // via `TAM_LEGACY_SINGLE_PICK=1` for diagnostic comparisons.
        let single_pick = std::env::var("TAM_LEGACY_SINGLE_PICK").is_ok();
        for (i, src) in saturated.into_iter().enumerate() {
            let prev_case_count = current.get(i).map(|s| s.cases.len()).unwrap_or(0);
            let mut new_cases: Vec<(String, System)> = Vec::new();
            for (name, sys) in src.cases {
                let case_name_for_dbg = name.clone();
                if single_pick {
                    // Pre-#160 single-pick fallback.
                    let sys_orig = sys.clone();
                    let mut red = Reduction::new(ctx, sys);
                    set_precompute_mode(true);
                    let mut used: std::collections::BTreeSet<String> = Default::default();
                    let sasg_outcome = solve_all_safe_goals_tracked(
                        &mut red, &ths_snapshot, &mut used, 10);
                    set_precompute_mode(false);
                    let after_contras = contradictions(ctx, &red.sys);
                    if !after_contras.is_empty() {
                        use crate::constraint::solver::contradictions::Contradiction;
                        let only_eq_or_subterm = after_contras.iter().all(|c|
                            matches!(c, Contradiction::IncompatibleEqs
                                      | Contradiction::SubtermCyclic
                                      | Contradiction::NonNormalTerms));
                        let pre_has_contras = !contradictions(ctx, &sys_orig).is_empty();
                        let saturate_branched = sasg_outcome.disj_pick || sasg_outcome.source_pick;
                        let preserve = !aggressive_drop
                            && only_eq_or_subterm
                            && !pre_has_contras
                            && saturate_branched;
                        if preserve {
                            new_cases.push((name, sys_orig));
                            changed = true;
                            continue;
                        }
                        changed = true;
                        continue;
                    }
                    new_cases.push((name, red.sys));
                    continue;
                }
                // === Multi-branch path (default — Haskell-faithful) ===
                set_precompute_mode(true);
                let branches = run_solve_all_safe_goals_disj(
                    ctx, sys, &ths_snapshot, /*chains_limit*/ 10,
                    /*outer_cap*/ 40, branch_cap, name);
                set_precompute_mode(false);
                if dbg {
                    eprintln!("  case {:?}: refineSource produced {} branches",
                        case_name_for_dbg, branches.len());
                }
                // Haskell `refineSource`:
                //   map (second (modify sSubst (restrict stableVars)))
                // restricts each branch's eq-store subst to the
                // STABLE vars (frees of the source's cdGoal) before
                // dedup.  This narrows the subst to bindings the
                // runtime case-matcher cares about; internal fresh
                // bindings are dropped so equivalent branches dedupe.
                // Without this, branches differing only in internal
                // fresh-var bindings stay distinct → case explosion.
                let mut stable_vars: std::collections::BTreeSet<
                    tamarin_term::lterm::LVar> = std::collections::BTreeSet::new();
                goal_free_vars(&src.goal, &mut |v| {
                    stable_vars.insert(v.clone());
                });
                // Haskell-faithful `removeRedundantCases` (Sources.hs:240):
                //   if enableBP msig || enableMSet msig then cases else cases0
                // Outside BP/MSet theories, redundant-case dedup is a no-op —
                // sibling cases with the same parent rule (e.g. multiple
                // `A_1` cases under KU(sign(...)) for foo_eligibility) MUST
                // be preserved so the renderer's `distinguish` can rename
                // them `A_1_case_1`/`A_1_case_2`.
                //
                // The dedup-on-by-default behaviour collapsed those siblings
                // under canonical-form equality, leaving Haskell-rendered
                // siblings (A_1) missing from the Rust proof skeleton —
                // root cause of the 8-lemma case_N cluster (foo/okamoto/
                // NSLPK3/NSLPK3_untagged/TLS).
                let msig = ctx.maude.maude_sig();
                let dedup_enabled = msig.enable_bp || msig.enable_mset;
                let mut seen: std::collections::BTreeSet<String> =
                    std::collections::BTreeSet::new();
                for (mut branch_sys, branch_name) in branches {
                    if aggressive_drop && !contradictions(ctx, &branch_sys).is_empty() {
                        changed = true;
                        continue;
                    }
                    // Apply `restrict stableVars` to the branch's subst.
                    let restricted_pairs: Vec<_> = branch_sys.eq_store.subst.to_list()
                        .into_iter()
                        .filter(|(v, _)| stable_vars.contains(v))
                        .collect();
                    branch_sys.eq_store.subst =
                        tamarin_term::subst::Subst::from_list(restricted_pairs);
                    if dedup_enabled {
                        let key = canonicalise_system_full(&branch_sys);
                        if !seen.insert(key) { continue; }
                    }
                    new_cases.push((branch_name, branch_sys));
                }
            }
            // Determine if the case count changed for this source.
            let new_case_count = new_cases.len();
            if dbg {
                eprintln!("[refine] source goal={:?} -> {} output cases:",
                    src.goal, new_case_count);
                let mut name_counts: std::collections::BTreeMap<String, usize>
                    = std::collections::BTreeMap::new();
                for (n, _) in &new_cases {
                    *name_counts.entry(n.clone()).or_insert(0) += 1;
                }
                for (n, c) in &name_counts {
                    eprintln!("[refine]   {}: {}", n, c);
                }
            }
            if !new_cases.is_empty() {
                next.push(Source { goal: src.goal, cases: new_cases, incomplete: src.incomplete });
            } else {
                changed = true;
            }
            if new_case_count != prev_case_count {
                changed = true;
            }
        }
        current = next;
        if !changed { break; }
    }
    current
}

/// `SolveSaturateOutcome` distinguishes cases where saturate picked a
/// Disj-goal (meaning any post-saturate contradiction might be from
/// exploring one branch of a Disj where Haskell would have explored
/// others — i.e. truly speculative) vs cases where saturate took
/// no Disj-goal step (so any contradiction follows from non-branching
/// propagation, matching Haskell's mzero on a non-branching path).
///
/// This is the key signal that lets `refine_with_source_asms` drop
/// typing-violating cases at precompute without losing the legitimate
/// "branch explored was the wrong one" speculative cases.
#[derive(Debug, Clone, Copy)]
pub(super) struct SaturateOutcome {
    /// True iff saturate solved at least one Disj/Split/Subterm goal
    /// (where we picked one branch and committed).
    pub disj_pick: bool,
    /// True iff saturate solved at least one KU-source case (where we
    /// picked one source case from `solveWithSource`'s candidates).
    pub source_pick: bool,
    /// True iff Haskell's Disj-monad would mzero this case: we tried
    /// every candidate (within budget) for the source-pick step and
    /// every one ended in contradiction.  Caller should drop.
    pub dead_end: bool,
}

fn solve_all_safe_goals_tracked(
    red: &mut crate::constraint::solver::reduction::Reduction,
    ths: &[Source],
    used: &mut std::collections::BTreeSet<String>,
    chains_limit: i64,
) -> SaturateOutcome {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::contradictions::contradictions;
    use crate::constraint::solver::goals::dispatch_solve_goal;
    use crate::constraint::solver::reduction::{GoalCases, SolveOutcome, SplitStrategy};
    use crate::constraint::solver::simplify::simplify_system;
    use crate::fact::FactTag;

    let mut chains_left = chains_limit;
    let mut outcome = SaturateOutcome {
        disj_pick: false,
        source_pick: false,
        dead_end: false,
    };
    // Bound the outer loop to prevent runaway iteration (matches
    // Haskell's reliance on `openChainsLimit` plus the natural
    // monotonicity of goal-solving; we add a hard cap for safety).
    let outer_cap: i64 = 40;
    for _iter in 0..outer_cap {
        simplify_system(red);
        if !contradictions(&red.ctx, &red.sys).is_empty() {
            return outcome;
        }
        // Snapshot open goals using Haskell's `openGoals` view (via
        // `is_open_for_saturate` — same function as `is_open_in_sys`,
        // since Haskell uses a single openGoals).  This drops msg-var
        // KD `ChainG` and KU(msg_var, no-node) auto-solve cases, so
        // `splitAllowed` correctly flips True when only auto-handled
        // chains remain — letting DisjG/SplitG/SubtermG count as
        // "safe" goals for saturate's case-split step.
        //
        // Haskell-faithful Goal-Ord (Goals.hs:69 `M.toList sGoals`):
        // sort by `goal_cmp` to match Haskell's BTreeMap iteration
        // order (ActionG < ChainG < PremiseG < SplitG < DisjG <
        // SubtermG).  Without this, our insertion-order iteration
        // picks a different goal than Haskell at the first
        // `headMay safeGoals` step, causing proof-shape divergence.
        let mut goals: Vec<(Goal, bool /* looping */)> = red.sys.goals.iter()
            .filter(|(_, st)| !st.solved && !st.looping)
            .filter(|(g, _)| crate::constraint::solver::goals::is_open_for_saturate(g, &red.sys))
            .map(|(g, st)| (g.clone(), st.looping))
            .collect();
        goals.sort_by(|a, b| crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
        // UNFILTERED chains view — mirrors Haskell's `unsolvedChains`
        // (NOT `openGoals`).  Together with the filtered `goals`,
        // `splitAllowed` flips True when there are chains present but
        // they're all auto-handled msg-var KD ones.
        let any_unsolved_chain = red.sys.goals.iter().any(|(g, st)|
            !st.solved && matches!(g, Goal::Chain(_, _)));
        let any_chain_goal = goals.iter().any(|(g, _)| matches!(g, Goal::Chain(_, _)));
        let split_allowed = !any_chain_goal && any_unsolved_chain;

        // Classify goals into kd_prem (priority) and safe.
        // Haskell parity (Sources.hs:169-170, 159):
        //   isKDPrem (PremiseG _ fa,_) = isKDFact fa && not (isKDXorFact fa)
        //   PremiseG _ fa -> not (isKUFact fa) && not (isKDXorFact fa)
        //                     && not (isNoSourcesFact fa)
        // Previously we excluded ALL KD premises (Ku | Kd) — too
        // restrictive; Haskell solves non-Xor non-NoSources KD
        // premises as safe goals.
        let is_kd_prem = |g: &Goal| -> bool {
            matches!(g, Goal::Premise(_, fa)
                if fa.tag == FactTag::Kd && !crate::fact::is_kd_xor_fact(fa))
        };
        let is_chain_prem1 = |g: &Goal| -> bool {
            matches!(g, Goal::Chain(_, (_, pi)) if pi.0 == 1)
        };
        let is_safe = |g: &Goal| -> bool {
            match g {
                Goal::Chain(_, _) => chains_left > 0,
                Goal::Action(_, fa) => !matches!(fa.tag, FactTag::Ku),
                Goal::Premise(_, fa) => {
                    !matches!(fa.tag, FactTag::Ku)
                        && !crate::fact::is_kd_xor_fact(fa)
                        && !fa.is_no_sources()
                }
                Goal::Disj(_) | Goal::Split(_) | Goal::Subterm(_) => split_allowed,
            }
        };
        // Priority order: KD-premise / chain-prem1 first, then safe.
        let pick = goals.iter()
            .find(|(g, _)| is_kd_prem(g) || is_chain_prem1(g))
            .or_else(|| goals.iter().find(|(g, _)| is_safe(g)));

        if std::env::var("TAM_DBG_SAS_FLOW").is_ok() {
            let goal_kinds: Vec<String> = goals.iter().map(|(g, _)| match g {
                Goal::Chain(_, _) => "Chain".to_string(),
                Goal::Disj(_) => "Disj".to_string(),
                Goal::Split(_) => "Split".to_string(),
                Goal::Subterm(_) => "Subterm".to_string(),
                Goal::Action(_, fa) => format!("Action({:?})", fa.tag),
                Goal::Premise(_, fa) => format!("Premise({:?})", fa.tag),
            }).collect();
            let pick_kind = pick.map(|(g, _)| match g {
                Goal::Chain(_, _) => "Chain",
                Goal::Disj(_) => "Disj",
                Goal::Split(_) => "Split",
                Goal::Subterm(_) => "Subterm",
                Goal::Action(_, _) => "Action",
                Goal::Premise(_, _) => "Premise",
            }).unwrap_or("None");
            eprintln!("[SAS-flow] split_allowed={} goals=[{}] pick={} eq_entries={}",
                split_allowed, goal_kinds.join(","), pick_kind,
                red.sys.eq_store.subst.to_list().len());
        }

        if let Some((goal, _)) = pick {
            let goal = goal.clone();
            // Track chain budget: if we're solving a chain goal, decrement.
            if matches!(goal, Goal::Chain(_, _)) {
                chains_left -= 1;
            }
            // Track whether we're committing to a Disj/Split/Subterm
            // branch — this signals to the caller that the post-
            // saturate state depends on a one-branch choice that
            // Haskell's Disj-monad would have explored exhaustively.
            let is_disj_like = matches!(goal,
                Goal::Disj(_) | Goal::Split(_) | Goal::Subterm(_));
            // Solve the goal.  For multi-case outcomes, take the FIRST
            // case — saturation is one branch of the precompute, mirroring
            // Haskell's single-branch threading inside the Reduction monad.
            let inner_outcome = dispatch_solve_goal(red, &goal);
            match inner_outcome {
                GoalCases::Contradictory => return outcome,
                GoalCases::Linear | GoalCases::LinearNamed(_) => {}
                GoalCases::Cases(cases) => {
                    let cases_vec: Vec<_> = cases.into_iter().collect();
                    if is_disj_like && cases_vec.len() > 1 {
                        outcome.disj_pick = true;
                    }
                    if let Some((_, first)) = cases_vec.into_iter().next() {
                        red.sys = first;
                    } else {
                        return outcome;
                    }
                }
            }
            continue;
        }

        // No safe goal left — try the `solveWithSourceAndReturn`
        // branch of Haskell's `solveAllSafeGoals.solve`.  Two modes:
        //
        //   * Default (single-pick): pick the first unused source-case.
        //     Source-pick flag records whether multiple candidates
        //     existed (diagnostic, drives speculative-restore in
        //     `saturate_sources_with_simp_opt`).
        //
        //   * `TAM_DISJ_MONAD_BACKTRACK=1` (recursive backtracking):
        //     Haskell-faithful — try each candidate via recursion; if
        //     all candidates leave the system contradictory after
        //     complete saturation, set `outcome.dead_end = true` so
        //     the caller drops the case unconditionally (matches
        //     Haskell's Disj-monad `mzero` propagation when no branch
        //     survives).
        if ths.is_empty() { return outcome; }
        // Haskell-faithful `filterCases`: skip useful_kus whose source
        // label is already in `used` (whole source consumed).  Mirrors
        // Sources.hs:218-219 — picking case X from Source1 removes
        // Source1 entirely from the candidate list, not just the X
        // case-name.  When ALL useful_kus map to consumed sources,
        // return outcome (saturate complete for this iteration).
        let useful_ku = goals.iter().find_map(|(g, _)| match g {
            Goal::Action(i, fa) if matches!(fa.tag, FactTag::Ku) => {
                if let Some(label) = ku_source_label_for_fa(fa) {
                    if used.contains(&label) { return None; }
                }
                Some((i.clone(), fa.clone()))
            }
            _ => None,
        });
        let Some((i, fa)) = useful_ku else { return outcome };
        let avoid_max = system_max_idx(&red.sys);
        let Some(case_pairs) = solve_with_source_cases_action(
            ths, &red.sys, &i, &fa, avoid_max) else { return outcome };
        // `used` now tracks SOURCE LABELS (not case names) — once we
        // pick a case from Source S, S as a whole becomes unavailable.
        // No per-case-name filter needed here: case_pairs all come
        // from a single source whose label is NOT in used (verified
        // above).
        let unused: Vec<_> = case_pairs;
        let unused_count = unused.len();
        if unused_count == 0 { return outcome; }
        if unused_count > 1 {
            outcome.source_pick = true;
        }

        // TAM_DISJ_MONAD_BACKTRACK: previously enabled the
        // backtracking path below.  Now no-op — kept as historical
        // infrastructure for future Disj-monad work, but disabled at
        // runtime because single-pick saturate can't faithfully
        // emulate Haskell's Disj-monad multi-branch refineSource
        // semantics.  The alternative-check it performed, even with
        // dead_end ignored, caused subtle state-divergence on
        // time-sensitive lemmas (TESLA_Scheme1::authentic).  See
        // memory: project_rust_disj_monad_source_pick.md.
        let backtrack = false;
        let _ = std::env::var("TAM_DISJ_MONAD_BACKTRACK").is_ok();

        // Inline closure applying one candidate.  Returns Ok(()) if
        // applied without immediate contradiction; Err(()) otherwise.
        // Mutates `red.sys` and (on success) inserts into `used`.
        let apply_one =
            |red: &mut crate::constraint::solver::reduction::Reduction,
             case_name: &str,
             sys_cand: crate::constraint::system::System,
             case_action: crate::fact::LNFact,
             fa: &crate::fact::LNFact,
             used: &mut std::collections::BTreeSet<String>|
            -> Result<(), ()>
        {
            red.sys = sys_cand;
            let res = red.solve_fact_eqs(
                SplitStrategy::SplitNow,
                &[tamarin_term::rewriting::Equal {
                    lhs: case_action, rhs: fa.clone(),
                }],
            );
            if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
                return Err(());
            }
            let mut tag_mismatch_edge = false;
            let chain_eqs: Vec<_> = red.sys.edges.iter()
                .filter_map(|e| {
                    let (_, src_rule) = red.sys.nodes.iter()
                        .find(|(n, _)| n == &e.src.0)?;
                    let (_, tgt_rule) = red.sys.nodes.iter()
                        .find(|(n, _)| n == &e.tgt.0)?;
                    let fc = src_rule.conclusions.get(e.src.1.0)?.clone();
                    let fp = tgt_rule.premises.get(e.tgt.1.0)?.clone();
                    if fc.tag != fp.tag || fc.terms.len() != fp.terms.len() {
                        tag_mismatch_edge = true;
                        return None;
                    }
                    if fc == fp { return None; }
                    Some(tamarin_term::rewriting::Equal { lhs: fc, rhs: fp })
                })
                .collect();
            if tag_mismatch_edge { return Err(()); }
            if !chain_eqs.is_empty() {
                let r2 = red.solve_fact_eqs(SplitStrategy::SplitNow, &chain_eqs);
                if matches!(r2, Err(_) | Ok(SolveOutcome::Contradictory)) {
                    return Err(());
                }
            }
            red.subst_system();
            // Haskell-faithful `filterCases`: track SOURCE LABEL (not
            // case name).  When the source label is unavailable
            // (shouldn't happen for KU goals reaching this point),
            // fall back to case_name to retain a guard.
            if let Some(label) = ku_source_label_for_fa(fa) {
                used.insert(label);
            } else {
                used.insert(case_name.to_string());
            }
            Ok(())
        };

        if !backtrack {
            // SINGLE-PICK PATH (default).
            let (case_name, sys, case_action) = unused.into_iter().next().unwrap();
            if apply_one(red, &case_name, sys, case_action, &fa, used).is_err() {
                return outcome;
            }
            continue;
        }

        // BACKTRACKING PATH — DEFAULT-COMPATIBLE WITH dead_end SIGNAL.
        //
        // Same primary behaviour as the default single-pick path:
        // try the FIRST unused candidate's immediate apply.
        //   * If succeeds → commit, continue the saturate loop (same
        //     as default).  This preserves the proof-tree shape for
        //     lemmas where the default's first-candidate pick is
        //     correct.
        //   * If fails → give up on this source-pick step (same as
        //     default's `return outcome`).  BUT before returning, we
        //     check the remaining candidates: if ALL also fail their
        //     immediate apply, set `outcome.dead_end = true`.  This
        //     adds the Haskell `mzero` signal without changing the
        //     primary behaviour: Haskell would mzero this case if no
        //     branch is viable, regardless of which branch its asum
        //     ordering would have committed to first.
        //
        // Why not commit to a later candidate when first fails?
        // Because saturate_sources_with_simp_opt produces ONE output
        // case per input case — committing to a different branch than
        // Haskell's asum ordering would have collected first would
        // over-constrain that single output, potentially dropping
        // attack-path source-cases at runtime (the NSPK3 Lowe attack
        // was lost when we committed to a non-Reveal_ltk candidate).
        // Haskell's `refineSource` collects ALL branches; our
        // single-output approximation must commit to the same one
        // default picks to preserve runtime behaviour.
        let dbg = std::env::var("TAM_TRACE_DM_BACKTRACK").is_ok();
        let cand_names: Vec<String> = unused.iter().map(|(n, _, _)| n.clone()).collect();
        let mut unused_iter = unused.into_iter();
        let first = unused_iter.next().unwrap();
        let first_name = first.0.clone();
        let saved_sys = red.sys.clone();
        let saved_used = used.clone();
        let saved_changed = red.changed;
        let first_ok = apply_one(red, &first.0, first.1, first.2, &fa, used).is_ok();
        if first_ok {
            if dbg {
                eprintln!("[dm-bt] candidates={:?} picked={} (committed)",
                    cand_names, first_name);
            }
            continue;
        }
        // First failed — restore and check remaining candidates for
        // dead_end signal.
        red.sys = saved_sys.clone();
        *used = saved_used.clone();
        red.changed = saved_changed;
        let mut any_alt_viable = false;
        for (case_name, sys_cand, case_action) in unused_iter {
            if apply_one(red, &case_name, sys_cand, case_action, &fa, used).is_ok() {
                any_alt_viable = true;
            }
            red.sys = saved_sys.clone();
            *used = saved_used.clone();
            red.changed = saved_changed;
            if any_alt_viable { break; }  // Found one, that's enough.
        }
        if dbg {
            eprintln!("[dm-bt] candidates={:?} picked=NONE (first {} failed; alt_viable={})",
                cand_names, first_name, any_alt_viable);
        }
        if !any_alt_viable {
            // No candidate is viable — Haskell mzero on entire
            // source-pick step.  Signal dead_end so caller drops case.
            outcome.dead_end = true;
        }
        return outcome;
    }
    outcome
}

/// Multi-branch port of `solveAllSafeGoals` matching Haskell's
/// Disj-monad semantics.  Returns ALL surviving branches as separate
/// `(System, name)` pairs.  This is the multi-output that
/// `refineSource` (Sources.hs:118-133) relies on via:
///
/// ```haskell
/// refinement = do
///     (names, se)        <- get cdCases th
///     ((x, names'), se') <- fst <$> runReduction proofStep ctxt se fs
///     return (x, (combine names names', se'))
/// ```
///
/// `runReduction proofStep ctxt se fs` returns the full Disj of
/// branches from one saturate invocation; each becomes its own output
/// case.  Our port enumerates these branches via a worklist:
///
/// - One worklist entry per alive branch.
/// - At each branching point (`GoalCases::Cases` from Disj/Split/
///   Subterm/rule-instantiation, or source-pick over multiple unused
///   candidates), the entry is replaced by N successor entries.
/// - Branches hitting a contradiction are DROPPED (Haskell mzero).
/// - Branches with no safe-goal AND no viable source-pick candidate
///   are pushed to finished (Haskell `nextStep = Nothing → return
///   caseNames`).
///
/// Termination:
/// - `outer_cap` bounds the per-branch saturate iterations (default 40,
///   same as `solve_all_safe_goals_tracked`).
/// - `branch_cap` caps total output branches.  When exceeded, alive
///   branches are pushed to finished with their accumulated state.
/// Probe-only wrapper around the internal `run_solve_all_safe_goals_disj`.
/// Mirrors the same signature minus the source list (always `&[]`).
/// Lets external probes exercise the Disj-monad explorer without
/// going through `refine_with_source_asms`.
pub fn run_solve_all_safe_goals_disj_for_probe(
    ctx: &crate::constraint::solver::context::ProofContext,
    initial_sys: System,
    chains_limit: i64,
    outer_cap: i64,
    branch_cap: usize,
    initial_name: String,
) -> Vec<(System, String)> {
    run_solve_all_safe_goals_disj(ctx, initial_sys, &[],
        chains_limit, outer_cap, branch_cap, initial_name)
}

/// Like `run_solve_all_safe_goals_disj_for_probe` but takes a `ths`
/// snapshot for source-pick.  Mirrors what `refine_with_source_asms`
/// passes to the inner Disj-monad.
pub fn run_solve_all_safe_goals_disj_for_probe_with_ths(
    ctx: &crate::constraint::solver::context::ProofContext,
    initial_sys: System,
    ths: &[Source],
    chains_limit: i64,
    outer_cap: i64,
    branch_cap: usize,
    initial_name: String,
) -> Vec<(System, String)> {
    run_solve_all_safe_goals_disj(ctx, initial_sys, ths,
        chains_limit, outer_cap, branch_cap, initial_name)
}

fn run_solve_all_safe_goals_disj(
    ctx: &crate::constraint::solver::context::ProofContext,
    initial_sys: System,
    ths: &[Source],
    chains_limit: i64,
    outer_cap: i64,
    branch_cap: usize,
    initial_name: String,
) -> Vec<(System, String)> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::contradictions::contradictions;
    use crate::constraint::solver::goals::dispatch_solve_goal;
    use crate::constraint::solver::reduction::{
        GoalCases, Reduction, SolveOutcome, SplitStrategy};
    use crate::constraint::solver::simplify::simplify_system;
    use crate::fact::FactTag;

    type Entry = (System, String, std::collections::BTreeSet<String>, i64, i64);
    let mut worklist: Vec<Entry> = vec![
        (initial_sys, initial_name, std::collections::BTreeSet::new(),
         chains_limit, outer_cap)
    ];
    let mut finished: Vec<(System, String)> = Vec::new();
    // Safety: hard limit on total worklist processing iterations to
    // avoid runaway exploration if branching is pathological.
    let mut total_steps: usize = 0;
    let total_step_cap: usize = branch_cap.saturating_mul(50).max(2000);

    while let Some((sys, name, used, chains_left, iters_left)) = worklist.pop() {
        total_steps += 1;
        if total_steps > total_step_cap {
            finished.push((sys, name));
            continue;
        }
        // Branch cap: if total alive+finished would exceed cap,
        // park this branch as-is (its final state is whatever we
        // accumulated so far).
        if finished.len() + 1 > branch_cap || iters_left <= 0 {
            finished.push((sys, name));
            continue;
        }

        let mut red = Reduction::new(ctx, sys);
        simplify_system(&mut red);
        if !contradictions(red.ctx, &red.sys).is_empty() {
            // Haskell mzero — drop branch (don't push to finished).
            continue;
        }

        // Pick a goal — mirrors `solve_all_safe_goals_tracked` exactly.
        // Saturate-time filter (Haskell `openGoals`) drops msg-var KD
        // ChainG so `split_allowed` correctly flips True when only
        // auto-handled chains remain.  See `is_open_for_saturate` in
        // goals.rs for the rationale.
        //
        // Haskell-faithful Goal-Ord (Goals.hs:69 `M.toList sGoals`).
        let mut goals: Vec<(Goal, bool)> = red.sys.goals.iter()
            .filter(|(_, st)| !st.solved && !st.looping)
            .filter(|(g, _)| crate::constraint::solver::goals::is_open_for_saturate(g, &red.sys))
            .map(|(g, st)| (g.clone(), st.looping))
            .collect();
        goals.sort_by(|a, b| crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
        // Unfiltered chains view — Haskell's `unsolvedChains`.
        let any_unsolved_chain = red.sys.goals.iter().any(|(g, st)|
            !st.solved && matches!(g, Goal::Chain(_, _)));
        let any_chain_goal = goals.iter()
            .any(|(g, _)| matches!(g, Goal::Chain(_, _)));
        let split_allowed = !any_chain_goal && any_unsolved_chain;
        // Haskell parity (Sources.hs:169-170, 159) — same fix as
        // solve_all_safe_goals_tracked above.
        let is_kd_prem = |g: &Goal| -> bool {
            matches!(g, Goal::Premise(_, fa)
                if fa.tag == FactTag::Kd && !crate::fact::is_kd_xor_fact(fa))
        };
        let is_chain_prem1 = |g: &Goal| -> bool {
            matches!(g, Goal::Chain(_, (_, pi)) if pi.0 == 1)
        };
        let is_safe = |g: &Goal| -> bool {
            match g {
                Goal::Chain(_, _) => chains_left > 0,
                Goal::Action(_, fa) => !matches!(fa.tag, FactTag::Ku),
                Goal::Premise(_, fa) => {
                    !matches!(fa.tag, FactTag::Ku)
                        && !crate::fact::is_kd_xor_fact(fa)
                        && !fa.is_no_sources()
                }
                Goal::Disj(_) | Goal::Split(_) | Goal::Subterm(_) => split_allowed,
            }
        };
        let pick = goals.iter()
            .find(|(g, _)| is_kd_prem(g) || is_chain_prem1(g))
            .or_else(|| goals.iter().find(|(g, _)| is_safe(g)));

        if let Some((goal, _)) = pick {
            let goal = goal.clone();
            let new_chains_left = if matches!(goal, Goal::Chain(_, _)) {
                chains_left - 1
            } else { chains_left };
            let inner_outcome = dispatch_solve_goal(&mut red, &goal);
            match inner_outcome {
                GoalCases::Contradictory => {
                    // Drop branch — Haskell mzero.
                    continue;
                }
                GoalCases::Linear => {
                    // Single output, no name added.  red.sys was
                    // mutated in place.
                    worklist.push((red.sys, name, used,
                        new_chains_left, iters_left - 1));
                }
                GoalCases::LinearNamed(sub_name) => {
                    let combined = combine_case_names(&name, &sub_name);
                    worklist.push((red.sys, combined, used,
                        new_chains_left, iters_left - 1));
                }
                GoalCases::Cases(cases) => {
                    // Multi-output — fork.  Each case's System
                    // becomes a new alive branch.  But: if
                    // `TAM_DISJ_REFINE_TOPLEVEL=1`, we collapse to
                    // single-pick at inner goals (take first case)
                    // and only fork at the top-level source-pick
                    // step below.  This produces fewer, less-
                    // specialized output cases — closer to what
                    // single-pick saturate yields, while still
                    // enumerating source-pick alternatives.
                    let toplevel_only = std::env::var("TAM_DISJ_REFINE_TOPLEVEL").is_ok();
                    let mut cases_iter = cases.into_iter();
                    if toplevel_only {
                        if let Some((sub_name, case_sys)) = cases_iter.next() {
                            let combined = combine_case_names(&name, &sub_name);
                            worklist.push((case_sys, combined, used.clone(),
                                new_chains_left, iters_left - 1));
                        }
                    } else {
                        for (sub_name, case_sys) in cases_iter {
                            let combined = combine_case_names(&name, &sub_name);
                            worklist.push((case_sys, combined, used.clone(),
                                new_chains_left, iters_left - 1));
                        }
                    }
                }
            }
            continue;
        }

        // No safe goal — try source-pick (Haskell's third disjunct
        // of `nextStep`, line 205).
        if ths.is_empty() {
            finished.push((red.sys, name));
            continue;
        }
        // Haskell-faithful: `asum [solveWithSourceAndReturn ctxt ths g
        // | g <- usefulGoals]` iterates over ALL useful KU goals,
        // returning the FIRST goal whose source-pick has a matching
        // source. Previously we picked only `goals.iter().find_map`
        // for the first KU action goal — if no source matched that
        // goal, we treated the current state as a survivor (push to
        // `finished`). But Haskell would proceed to the next goal.
        // This caused destructor-baked source cases (Resolve1/Resolve2
        // with d_1_check_getmsg) to survive our drop pass, where
        // Haskell drops them via Cyclic+ForbiddenChain after
        // source-picking on a *later* KU goal (e.g. KU(pcs(...))).
        // Haskell-faithful `filterCases` (Sources.hs:218-219):
        // skip useful_kus whose source LABEL is already in `used` —
        // picking a case from Source S consumes S entirely, not just
        // the picked case-name.  See `ku_source_label_for_fa`.
        let useful_kus: Vec<(crate::constraint::constraints::NodeId,
                              crate::fact::LNFact)> =
            goals.iter().filter_map(|(g, _)| match g {
                Goal::Action(i, fa) if matches!(fa.tag, FactTag::Ku) => {
                    if let Some(label) = ku_source_label_for_fa(fa) {
                        if used.contains(&label) { return None; }
                    }
                    Some((i.clone(), fa.clone()))
                }
                _ => None,
            }).collect();
        if useful_kus.is_empty() {
            finished.push((red.sys, name));
            continue;
        }
        let avoid_max = system_max_idx(&red.sys);
        let use_ctx_aware = std::env::var("TAM_DISJ_REFINE_CTX").is_ok();
        let trace = std::env::var("TAM_DISJ_REFINE_TRACE").is_ok();
        // Iterate useful goals in order; first one with a matching
        // source wins (Haskell `asum`).
        let mut picked: Option<(crate::constraint::constraints::NodeId,
                                crate::fact::LNFact,
                                Vec<(String,
                                     crate::constraint::system::System,
                                     crate::fact::LNFact)>)> = None;
        for (i_cand, fa_cand) in useful_kus {
            let case_pairs_opt = if use_ctx_aware {
                solve_with_source_cases_action_with_ctx(
                    ths, &red.sys, &i_cand, &fa_cand, avoid_max, Some(ctx))
            } else {
                solve_with_source_cases_action(
                    ths, &red.sys, &i_cand, &fa_cand, avoid_max)
            };
            if let Some(case_pairs) = case_pairs_opt {
                if !case_pairs.is_empty() {
                    picked = Some((i_cand, fa_cand, case_pairs));
                    break;
                }
            }
        }
        let Some((i, fa, case_pairs)) = picked else {
            // No useful goal has a matching source — Haskell's
            // `nextStep = Nothing` → `return caseNames` (current
            // state survives).
            if trace {
                eprintln!("[disj-refine] name={} -- no goal had matching source", name);
            }
            finished.push((red.sys, name));
            continue;
        };
        if trace {
            let names: Vec<&str> = case_pairs.iter().map(|(n, _, _)| n.as_str()).collect();
            eprintln!("[disj-refine] name={} i={:?} -- {} cases: {:?}",
                name, i, case_pairs.len(), names);
        }
        // Source-label-based filter (Haskell-faithful): the picked
        // useful_ku's source label was verified NOT in `used` above,
        // so all case_pairs from this single source are available.
        // No per-case-name filter needed.
        let unused: Vec<_> = case_pairs;
        if unused.is_empty() {
            // No candidates returned by solve_with_source_cases_action
            // — surface as survivor (Haskell's asum returns [] here).
            if trace {
                eprintln!("[disj-refine] name={} -- ALL USED", name);
            }
            finished.push((red.sys, name));
            continue;
        }

        // Fork: try each viable candidate as a separate branch.
        // Mirrors Haskell `asum [solveWithSourceAndReturn ctxt ths g
        // | g <- usefulGoals]` — collects all branches that survive.
        //
        // TAM_DISJ_REFINE_NO_SOURCE_PICK=1: commit to FIRST viable
        // source-pick (single-pick semantics) instead of forking.  This
        // makes source-pick behave like single-pick while keeping
        // Disj/Split/Subterm branching active.  Tests whether the
        // wrong-VERIFY on NSPK3 attack comes from source-pick branching
        // or from safe-goal branching.
        let no_source_pick_fork = std::env::var("TAM_DISJ_REFINE_NO_SOURCE_PICK").is_ok();
        let mut any_branched = false;
        for (case_name, sys_cand, case_action) in unused {
            if use_ctx_aware {
                // Ctx-aware path: apply_source_case_action has already
                // done `someInst keepVarBindings` + `conjoinSystem`,
                // so the system is fully merged.  No follow-up
                // solve_fact_eqs needed — push directly.
                let mut new_used = used.clone();
                // Haskell-faithful: track SOURCE LABEL.
                if let Some(label) = ku_source_label_for_fa(&fa) {
                    new_used.insert(label);
                } else {
                    new_used.insert(case_name.clone());
                }
                let combined = combine_case_names(&name, &case_name);
                if trace {
                    eprintln!("[disj-refine] commit ctx-aware case={} -> {}",
                        case_name, combined);
                }
                worklist.push((sys_cand, combined, new_used,
                    chains_left, iters_left - 1));
                any_branched = true;
                continue;
            }
            // Legacy graft path: caller runs solve_fact_eqs(action) +
            // chain_eqs over the grafted system.
            let mut sub = Reduction::new(ctx, sys_cand);
            let res = sub.solve_fact_eqs(
                SplitStrategy::SplitNow,
                &[tamarin_term::rewriting::Equal {
                    lhs: case_action, rhs: fa.clone(),
                }],
            );
            if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
                if trace {
                    eprintln!("[disj-refine] drop case={} (action-eq failed)",
                        case_name);
                }
                continue;
            }
            let mut tag_mismatch_edge = false;
            let chain_eqs: Vec<_> = sub.sys.edges.iter()
                .filter_map(|e| {
                    let (_, src_rule) = sub.sys.nodes.iter()
                        .find(|(n, _)| n == &e.src.0)?;
                    let (_, tgt_rule) = sub.sys.nodes.iter()
                        .find(|(n, _)| n == &e.tgt.0)?;
                    let fc = src_rule.conclusions.get(e.src.1.0)?.clone();
                    let fp = tgt_rule.premises.get(e.tgt.1.0)?.clone();
                    if fc.tag != fp.tag || fc.terms.len() != fp.terms.len() {
                        tag_mismatch_edge = true;
                        return None;
                    }
                    if fc == fp { return None; }
                    Some(tamarin_term::rewriting::Equal { lhs: fc, rhs: fp })
                })
                .collect();
            if tag_mismatch_edge {
                if trace {
                    eprintln!("[disj-refine] drop case={} (tag mismatch)",
                        case_name);
                }
                continue;
            }
            if !chain_eqs.is_empty() {
                let r2 = sub.solve_fact_eqs(SplitStrategy::SplitNow, &chain_eqs);
                if matches!(r2, Err(_) | Ok(SolveOutcome::Contradictory)) {
                    if trace {
                        eprintln!("[disj-refine] drop case={} (chain-eq failed)",
                            case_name);
                    }
                    continue;
                }
            }
            sub.subst_system();

            // This candidate is viable — push as a new alive branch.
            let mut new_used = used.clone();
            // Haskell-faithful: track SOURCE LABEL.
            if let Some(label) = ku_source_label_for_fa(&fa) {
                new_used.insert(label);
            } else {
                new_used.insert(case_name.clone());
            }
            let combined = combine_case_names(&name, &case_name);
            if trace {
                eprintln!("[disj-refine] commit legacy case={} -> {}",
                    case_name, combined);
            }
            worklist.push((sub.sys, combined, new_used,
                chains_left, iters_left - 1));
            any_branched = true;
            if no_source_pick_fork { break; }
        }

        if !any_branched {
            // No candidate was viable — Haskell `asum [mzero, ...] =
            // mzero` → `nextStep = Nothing` → `solve` returns
            // `caseNames` (keep current state).
            finished.push((red.sys, name));
        }
    }

    finished
}

/// `solveWithSource` lite — match a precomputed source against a live
/// premise goal.  Returns one `(System, conclusion_fact)` per
/// applicable case: the system has the case's nodes/edges grafted in,
/// and the conclusion fact is the case's abstract producer-conclusion
/// term-vector to be unified against `fa_prem` by the caller (so the
/// case's terms align with the live premise's terms).
///
/// Mirrors Haskell's `applySource`:
/// ```text
///   _applySource th = do
///     markGoalAsSolved "precomputed" goal
///     (names, sysTh0) <- disjunctionOfList $ getDisj $ get cdCases th
///     sysTh <- evalBindT (someInst sysTh0) keepVarBindings
///     conjoinSystem sysTh
/// ```
/// The `someInst` step renames the case to fresh vars; `conjoinSystem`
/// merges its nodes/edges/etc into the live one — but it also runs
/// `solveFactEqs` implicitly via the unification path that aligns the
/// abstract goal's bound variables with the live goal's terms.
///
/// Caller (in `Reduction::solve_premise_goal`) drives the
/// `solveFactEqs(SplitNow, [Equal { lhs: conc_fact, rhs: fa_prem }])`
/// step over each returned tuple — that's why we hand back the
/// conclusion fact rather than running unification here (we don't have
/// a `&mut Reduction` at this layer).
/// Haskell-faithful `applySource` driver for Premise goals.  Walks
/// the source's cases, invoking `apply_source_case_premise` per case
/// (which mirrors `matchToGoal` + `_applySource` from Sources.hs).
///
/// Returns `(case_name, fully_conjoined_system)` per case that
/// successfully matched + conjoined.  The system is already aligned
/// against the live goal via `conjoinSystem`'s `solveSubstEqs +
/// substSystem` plus a defensive `chain_eqs` pass — no additional
/// fact-eq work needed by the caller.
pub fn solve_with_source_cases_ctx(
    ctx: &crate::constraint::solver::context::ProofContext,
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    goal_prem_idx: crate::rule::PremIdx,
    fa_prem: &crate::fact::LNFact,
) -> Option<Vec<(String, System)>> {
    use crate::constraint::constraints::Goal;

    let src = sources.iter().find(|s| match &s.goal {
        Goal::Premise(_, fa) => fa.tag == fa_prem.tag,
        _ => false,
    })?;

    let mut out: Vec<(String, System)> = Vec::new();
    for (name, case_sys) in &src.cases {
        // Normalize precompute case-name by stripping `_case_<N>_` and
        // intruder-rule prefixes (coerce_, irecv_, c_<sym>_) so that
        // runtime emits the canonical Haskell name (e.g. `Recv1`).
        let case_label = saturated_chain_root(name);
        if let Some(final_sys) = apply_source_case_premise(
            ctx, sys, src, case_sys,
            goal_node, goal_prem_idx, fa_prem,
        ) {
            out.push((case_label, final_sys));
        }
    }
    if out.is_empty() { return None; }
    Some(out)
}

pub fn solve_with_source_cases(
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    goal_prem_idx: crate::rule::PremIdx,
    fa_prem: &crate::fact::LNFact,
    avoid_max: u64,
) -> Option<Vec<(System, crate::fact::LNFact)>> {
    use crate::constraint::constraints::Goal;

    let src = sources.iter().find(|s| match &s.goal {
        Goal::Premise(_, fa) => fa.tag == fa_prem.tag,
        _ => false,
    })?;

    let abstract_orig = match &src.goal {
        Goal::Premise((n, _), _) => n.clone(),
        _ => return None,
    };
    let abstract_orig_idx = match &src.goal {
        Goal::Premise((_, p), _) => *p,
        _ => return None,
    };

    let mut out: Vec<(System, crate::fact::LNFact)> = Vec::new();
    for (_name, case_sys) in &src.cases {
        // Legacy caller (no MaudeHandle available) — keep avoid_max-only
        // shift.  Haskell-faithful counter path: callers that hand us
        // a context use the with_ctx variant above (which threads
        // `Some(&ctx.maude)` into freshen_system).
        let renamed = freshen_system(case_sys, avoid_max, None);
        // After `freshen_system`, every var idx in the case shifted by
        // `avoid_max + 1`. The abstract_node was at idx=0 in the
        // original; it's at `avoid_max + 1` now.
        let abstract_renamed = {
            let mut v = abstract_orig.clone();
            v.idx = v.idx.saturating_add(avoid_max.saturating_add(1));
            v
        };
        // Locate the producer-conclusion edge into the abstract goal.
        // That edge's source rule's conclusion at `c_idx` is the fact
        // we hand back to the caller for unification.
        let conc_fact = renamed.edges.iter().find_map(|e| {
            if e.tgt.0 == abstract_renamed && e.tgt.1 == abstract_orig_idx {
                renamed.nodes.iter()
                    .find(|(id, _)| id == &e.src.0)
                    .and_then(|(_, ru)| ru.conclusions.get(e.src.1.0).cloned())
            } else { None }
        });
        let conc_fact = match conc_fact { Some(f) => f, None => continue };
        let mut grafted = match graft_case_into(
            sys, &renamed, &abstract_renamed, goal_node,
            goal_prem_idx, fa_prem,
        ) {
            Some(g) => g, None => continue,
        };
        if src.incomplete { grafted.used_incomplete_source = true; }
        out.push((grafted, conc_fact));
    }
    if out.is_empty() { return None; }
    Some(out)
}

/// Fresh-rename every LVar in a system so its indices don't clash
/// with `avoid_max`. Mirrors Haskell's `evalFresh ... rename`.
///
/// **Haskell-faithful counter**: the shift amount comes from the
/// MaudeHandle's global `fresh_counter` (mirroring `MonadFresh`),
/// not from `avoid_max + 1` alone.  Without a global counter, two
/// freshen_system calls with the same `avoid_max` (e.g. precompute
/// enumeration where the system isn't updated between calls) shift
/// every var to the same idxs and produce cross-call collisions.
/// Drawing from the global counter guarantees each freshen produces
/// a globally-unique idx range.
///
/// Walks every LVar-bearing field of `System` and shifts each var's
/// `idx` by the reserved base.  We can't use `HasFrees::map_free`
/// directly because `System` doesn't implement it (it's a top-level
/// solver type rather than a term-bearing one).  Doing this by hand
/// keeps the dependency graph clean.
fn freshen_system(
    sys: &System,
    avoid_max: u64,
    maude: Option<&tamarin_term::maude_proc::MaudeHandle>,
) -> System {
    use tamarin_term::lterm::HasFrees;
    // Find the system's max var idx — we need to reserve `max + 1`
    // consecutive idxs from the global counter (so the shifted range
    // [shift..shift+max] is uniquely reserved).
    let shift: u64 = if let Some(h) = maude {
        let sys_max = {
            let mut m: u64 = 0;
            let mut walk = |v: &tamarin_term::lterm::LVar| { if v.idx > m { m = v.idx; } };
            for (id, ru) in &sys.nodes {
                id.for_each_free(&mut walk);
                ru.for_each_free(&mut walk);
            }
            for e in &sys.edges {
                e.src.0.for_each_free(&mut walk);
                e.tgt.0.for_each_free(&mut walk);
            }
            for l in &sys.less_atoms {
                l.smaller.for_each_free(&mut walk);
                l.larger.for_each_free(&mut walk);
            }
            for (g, _) in &sys.goals {
                match g {
                    crate::constraint::constraints::Goal::Action(n, fa) => {
                        n.for_each_free(&mut walk); fa.for_each_free(&mut walk);
                    }
                    crate::constraint::constraints::Goal::Premise(p, fa) => {
                        p.0.for_each_free(&mut walk); fa.for_each_free(&mut walk);
                    }
                    crate::constraint::constraints::Goal::Chain(c, p) => {
                        c.0.for_each_free(&mut walk); p.0.for_each_free(&mut walk);
                    }
                    _ => {}
                }
            }
            if let Some(la) = &sys.last_atom { la.for_each_free(&mut walk); }
            for (v, t) in sys.eq_store.subst.to_list() {
                walk(&v);
                t.for_each_free(&mut walk);
            }
            m
        };
        h.ensure_above(avoid_max);
        h.reserve_idxs(sys_max.saturating_add(1))
    } else {
        avoid_max.saturating_add(1)
    };
    let shift_lvar = |v: &tamarin_term::lterm::LVar| {
        let mut v2 = v.clone();
        v2.idx = v2.idx.saturating_add(shift);
        v2
    };
    let mut out = sys.clone();
    out.nodes = out.nodes.into_iter()
        .map(|(id, ru)| {
            (shift_lvar(&id),
             ru.map_free(&mut |v| shift_lvar(&v))) })
        .collect();
    out.edges = out.edges.into_iter()
        .map(|e| crate::constraint::constraints::Edge {
            src: (shift_lvar(&e.src.0), e.src.1),
            tgt: (shift_lvar(&e.tgt.0), e.tgt.1),
        })
        .collect();
    out.less_atoms = out.less_atoms.into_iter()
        .map(|l| crate::constraint::constraints::LessAtom::new(
            shift_lvar(&l.smaller),
            shift_lvar(&l.larger),
            l.reason))
        .collect();
    out.goals = out.goals.into_iter()
        .map(|(g, st)| {
            let g2 = match g {
                crate::constraint::constraints::Goal::Action(n, fa) =>
                    crate::constraint::constraints::Goal::Action(
                        shift_lvar(&n),
                        fa.map_free(&mut |v| shift_lvar(&v))),
                crate::constraint::constraints::Goal::Premise(p, fa) =>
                    crate::constraint::constraints::Goal::Premise(
                        (shift_lvar(&p.0), p.1),
                        fa.map_free(&mut |v| shift_lvar(&v))),
                crate::constraint::constraints::Goal::Chain(c, p) =>
                    crate::constraint::constraints::Goal::Chain(
                        (shift_lvar(&c.0), c.1),
                        (shift_lvar(&p.0), p.1)),
                other => other,
            };
            (g2, st)
        })
        .collect();
    if let Some(la) = out.last_atom.take() {
        out.last_atom = Some(shift_lvar(&la));
    }
    // Formulas / solved-formulas / lemmas: shift parser-AST vars too.
    // These can reference rule vars (after `subst_guarded` propagation)
    // and Maude witnesses that ALSO live in nodes — if we don't shift
    // them, the formulas end up referencing un-shifted vars that the
    // grafted system's nodes no longer have.
    let shift_parser_var = |v: &tamarin_parser::ast::VarSpec| -> tamarin_parser::ast::VarSpec {
        let mut v2 = v.clone();
        v2.idx = v2.idx.saturating_add(shift);
        v2
    };
    fn shift_guarded(
        g: &crate::guarded::Guarded,
        shift: &dyn Fn(&tamarin_parser::ast::VarSpec) -> tamarin_parser::ast::VarSpec,
    ) -> crate::guarded::Guarded {
        use crate::guarded::Guarded;
        match g {
            Guarded::Atom(a) => Guarded::Atom(shift_atom(a, shift)),
            Guarded::Conj(xs) => Guarded::Conj(xs.iter().map(|x| shift_guarded(x, shift)).collect()),
            Guarded::Disj(xs) => Guarded::Disj(xs.iter().map(|x| shift_guarded(x, shift)).collect()),
            Guarded::GGuarded { qua, vars, guards, body } => {
                // Bound vars get shifted too (they're locally scoped but
                // we keep the global shift to maintain the invariant that
                // ALL idxs in this case have been shifted).
                let vars2: Vec<_> = vars.iter().map(shift).collect();
                let guards2: Vec<_> = guards.iter().map(|a| shift_atom(a, shift)).collect();
                Guarded::GGuarded {
                    qua: qua.clone(),
                    vars: vars2,
                    guards: guards2,
                    body: Box::new(shift_guarded(body, shift)),
                }
            }
        }
    }
    fn shift_atom(
        a: &tamarin_parser::ast::Atom,
        shift: &dyn Fn(&tamarin_parser::ast::VarSpec) -> tamarin_parser::ast::VarSpec,
    ) -> tamarin_parser::ast::Atom {
        use tamarin_parser::ast::Atom;
        match a {
            Atom::Eq(s, t) => Atom::Eq(shift_term(s, shift), shift_term(t, shift)),
            Atom::Less(s, t) => Atom::Less(shift_term(s, shift), shift_term(t, shift)),
            Atom::LessMset(s, t) => Atom::LessMset(shift_term(s, shift), shift_term(t, shift)),
            Atom::Subterm(s, t) => Atom::Subterm(shift_term(s, shift), shift_term(t, shift)),
            Atom::Action(fact, t) => {
                let mut f2 = fact.clone();
                f2.args = f2.args.into_iter().map(|tm| shift_term(&tm, shift)).collect();
                Atom::Action(f2, shift_term(t, shift))
            }
            Atom::Last(t) => Atom::Last(shift_term(t, shift)),
            Atom::Pred(fact) => {
                let mut f2 = fact.clone();
                f2.args = f2.args.into_iter().map(|tm| shift_term(&tm, shift)).collect();
                Atom::Pred(f2)
            }
        }
    }
    fn shift_term(
        t: &tamarin_parser::ast::Term,
        shift: &dyn Fn(&tamarin_parser::ast::VarSpec) -> tamarin_parser::ast::VarSpec,
    ) -> tamarin_parser::ast::Term {
        use tamarin_parser::ast::Term;
        match t {
            Term::Var(v) => Term::Var(shift(v)),
            Term::App(n, args) => Term::App(n.clone(),
                args.iter().map(|a| shift_term(a, shift)).collect()),
            Term::AlgApp(n, a, b) => Term::AlgApp(n.clone(),
                Box::new(shift_term(a, shift)), Box::new(shift_term(b, shift))),
            Term::Pair(args) => Term::Pair(args.iter().map(|a| shift_term(a, shift)).collect()),
            Term::Diff(a, b) => Term::Diff(
                Box::new(shift_term(a, shift)), Box::new(shift_term(b, shift))),
            Term::BinOp(op, a, b) => Term::BinOp(*op,
                Box::new(shift_term(a, shift)), Box::new(shift_term(b, shift))),
            Term::PatMatch(inner) => Term::PatMatch(Box::new(shift_term(inner, shift))),
            other => other.clone(),
        }
    }
    let shift_g = |g: &crate::guarded::Guarded| shift_guarded(g, &shift_parser_var);
    out.formulas = out.formulas.iter().map(shift_g).collect();
    out.solved_formulas = out.solved_formulas.iter().map(shift_g).collect();
    out.lemmas = out.lemmas.iter().map(shift_g).collect();
    // Eq-store: shift both domain LVars and range terms.
    {
        let shifted_subst: Vec<_> = out.eq_store.subst.to_list().iter()
            .map(|(v, t)| {
                let v2 = shift_lvar(v);
                let t2 = (*t).clone().map_free(&mut |w| shift_lvar(&w));
                (v2, t2)
            })
            .collect();
        out.eq_store.subst = tamarin_term::subst::Subst::from_list(shifted_subst);
        for d in out.eq_store.conj.iter_mut() {
            for s in d.substs.iter_mut() {
                let shifted: Vec<_> = s.to_list().iter()
                    .map(|(v, t)| {
                        let v2 = shift_lvar(v);
                        let t2 = (*t).clone().map_free(&mut |w| shift_lvar(&w));
                        (v2, t2)
                    })
                    .collect();
                *s = tamarin_term::subst_vfresh::SubstVFresh::from_list(shifted.into_iter());
            }
        }
    }
    // Subterm-store: shift the LNTerm pairs (small/big).
    {
        let shift_st = |s: &crate::tools::subterm_store::SubtermConstraint|
            -> crate::tools::subterm_store::SubtermConstraint {
            crate::tools::subterm_store::SubtermConstraint {
                small: s.small.clone().map_free(&mut |w| shift_lvar(&w)),
                big: s.big.clone().map_free(&mut |w| shift_lvar(&w)),
                propagated: s.propagated,
            }
        };
        out.subterm_store.subterms = out.subterm_store.subterms.iter()
            .map(shift_st).collect();
        out.subterm_store.solved_subterms = out.subterm_store.solved_subterms.iter()
            .map(shift_st).collect();
    }
    out
}

/// Graft a precomputed-case subsystem `case_sys` into `live_sys`.
/// The case's `abstract_node` (placeholder consumer for the original
/// abstract goal) is mapped to `live_node`; the abstract goal's
/// premise edge becomes an edge into the live premise position.
fn graft_case_into(
    live_sys: &System,
    case_sys: &System,
    abstract_node: &crate::constraint::constraints::NodeId,
    live_node: &crate::constraint::constraints::NodeId,
    live_prem_idx: crate::rule::PremIdx,
    fa_prem: &crate::fact::LNFact,
) -> Option<System> {
    let mut out = live_sys.clone();
    let rename_node = |n: &crate::constraint::constraints::NodeId| {
        if n == abstract_node { live_node.clone() } else { n.clone() }
    };
    for (id, rule) in &case_sys.nodes {
        if id == abstract_node { continue; }
        let new_id = rename_node(id);
        if !out.nodes.iter().any(|(n, _)| n == &new_id) {
            out.add_node(new_id, rule.clone());
        }
    }
    for e in &case_sys.edges {
        let new_src_node = rename_node(&e.src.0);
        let new_tgt_node = rename_node(&e.tgt.0);
        let new_tgt_idx = if &e.tgt.0 == abstract_node {
            live_prem_idx
        } else {
            e.tgt.1
        };
        out.add_edge(crate::constraint::constraints::Edge {
            src: (new_src_node, e.src.1),
            tgt: (new_tgt_node, new_tgt_idx),
        });
    }
    for l in &case_sys.less_atoms {
        out.add_less(crate::constraint::constraints::LessAtom::new(
            rename_node(&l.smaller),
            rename_node(&l.larger),
            l.reason,
        ));
    }
    // Mirrors Haskell `conjoinSystem` (Reduction.hs:671):
    //     mapM_ (uncurry insertGoalStatus) $
    //         filter (not . isSplitGoal . fst) $ M.toList $ get sGoals sys
    // ALL of the case's goals are merged into the live system, PRESERVING
    // their solved status. Previously we skipped solved goals here, but
    // that broke source-case grafting: the source case for a fact premise
    // has its pre-wired Register_pk / Fresh / ISend producers' premise
    // goals marked [S] (solved by saturate_sources). Skipping them meant
    // those goals weren't in the live sys.goals — and some downstream
    // pass (subst_system / simplify) was re-deriving them as [-] unsolved,
    // causing the search to re-pick `case Register_pk` for premises that
    // Haskell shows as already resolved. Now we add them with their
    // solved flag intact, matching Haskell's behaviour.
    for (g, st) in &case_sys.goals {
        let renamed_goal = match g {
            crate::constraint::constraints::Goal::Premise(p, _fa)
                if &p.0 == abstract_node => continue,
            crate::constraint::constraints::Goal::Premise(p, fa) => {
                crate::constraint::constraints::Goal::Premise(
                    (rename_node(&p.0), p.1), fa.clone())
            }
            crate::constraint::constraints::Goal::Action(n, fa) =>
                crate::constraint::constraints::Goal::Action(rename_node(n), fa.clone()),
            other => other.clone(),
        };
        // Add the goal, preserving solved/looping flags from the case.
        // If the goal already exists in `out` (from `live_sys`), don't
        // overwrite — Haskell's `M.union` is left-biased.  Otherwise
        // push with the case's status.
        if !out.goals.iter().any(|(existing, _)| existing == &renamed_goal) {
            out.goals.push((renamed_goal, st.clone()));
        }
    }
    let live_goal = crate::constraint::constraints::Goal::Premise(
        (live_node.clone(), live_prem_idx), fa_prem.clone());
    if let Some(slot) = out.goals.iter_mut().find(|(g, _)| g == &live_goal) {
        slot.1.solved = true;
    }
    // Copy the case's variant SplitG disjunctions into the live system.
    // Without this, when saturate grafts a case (e.g. Receiver0b's case
    // with its 2-variant SplitG `signature → ~mw` vs `signature → sign(...)`)
    // into a chain, the SplitG is silently dropped — the resulting case
    // has the rule's facts un-narrowed (signature stays free) AND no
    // SplitG goal to later resolve.  At runtime when this case is
    // applied, the search sees an untyped signature variable and
    // reaches a spurious Solved leaf.  Mirrors Haskell's `conjoinSystem`
    // (Reduction.hs:707-708) which copies the case's `sEqStore.eqsConj`
    // disjunctions, then inserts a SplitG goal for each new disj id.
    //
    // We have to rename nodes referenced inside the variant substs
    // (the subst's range may contain LVars; if any reference the
    // abstract node it must be renamed to live_node).  Haskell's
    // domain/range of the variant subst is bound vars of the abstracted
    // rule, which don't include the abstract goal node, so this rename
    // is usually a no-op — but doing it consistently keeps the graft
    // semantics uniform.
    use tamarin_term::lterm::HasFrees;
    for d in &case_sys.eq_store.conj {
        let renamed_substs: Vec<_> = d.substs.iter().map(|s| {
            let pairs: Vec<_> = s.to_list().into_iter().map(|(v, t)| {
                let new_v = if &v == abstract_node { live_node.clone() } else { v };
                let new_t = t.map_free(&mut |w| {
                    if &w == abstract_node { live_node.clone() } else { w }
                });
                (new_v, new_t)
            }).collect();
            tamarin_term::subst_vfresh::SubstVFresh::from_list(pairs)
        }).collect();
        let new_id = out.eq_store.add_disj(renamed_substs);
        // Add the goal at the same position as the new disj.
        out.add_goal(crate::constraint::constraints::Goal::Split(new_id));
    }
    // Merge the case's free subst (eq_store.subst) into the live system's
    // free subst.  Mirrors Haskell's `conjoinSystem` (Reduction.hs:671) which
    // composes the case's eqStore subst into the live's via `applyEqStore`.
    // Without this, when a case carrying a Haskell-faithful `t#1 → kZero`
    // binding is grafted at saturate, the binding is silently dropped — and
    // subsequent saturate iterations lose the constraint that the goal var
    // is equated with the rule's internal var.  This was the missing piece
    // making Minimal_HashChain::Loop_and_success wrong-falsified post-LVar.
    //
    // Rename abstract_node → live_node in keys + values, mirroring the
    // rename done above for disj substs and edges.
    if !case_sys.eq_store.subst.is_empty() {
        for (v, t) in case_sys.eq_store.subst.to_list() {
            let new_v = if &v == abstract_node { live_node.clone() } else { v };
            let new_t = t.map_free(&mut |w| {
                if &w == abstract_node { live_node.clone() } else { w }
            });
            // Compose: new_v → new_t goes into out.eq_store.subst.  Use
            // simple insertion since the live system's subst typically has
            // disjoint domain at this point in saturate.
            let added = tamarin_term::subst::Subst::from_list(vec![(new_v, new_t)]);
            out.eq_store.subst = added.compose(&out.eq_store.subst);
        }
    }
    Some(out)
}

/// `solveWithSource` for ActionG / KU goals.  Mirrors the msgGoals
/// branch of Haskell's `applySource` flow.  Given a live
/// `Action(node_live, KU(m_live))` goal, finds a precomputed source
/// whose abstract KU pattern is head-compatible with `m_live` and
/// returns one `(System, action_fact)` per applicable case.
///
/// Compatibility (mirrors Haskell `matchToGoal` for KU patterns):
///   - bare-var pattern (`KU(t:s)`):  sort `s` of pattern must be
///     ≥ sort of `m_live`.  In our typed surface, the only bare-var
///     KU source we generate is `KU(t:Fresh)`, which fires when
///     `m_live` is itself a Fresh-sorted variable / constant.
///   - app pattern (`KU(f(...))`):  `m_live` must have the same head
///     symbol `f` with matching arity.
///
/// The caller drives `solveFactEqs(SplitNow, [Equal { case_action,
/// fa_live }])` on each returned tuple — that runs Maude AC
/// unification across the case's abstract terms and the concrete
/// `m_live`, exactly mirroring Haskell's `someInst >> conjoinSystem`.
pub fn solve_with_source_cases_action(
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
    avoid_max: u64,
) -> Option<Vec<(String, System, crate::fact::LNFact)>> {
    solve_with_source_cases_action_with_ctx(sources, sys, goal_node, fa_live, avoid_max, None)
}

/// Variant that takes an optional `ProofContext` to enable the
/// Haskell-faithful `applySource` path (`apply_source_case_action`).
/// When `ctx_opt = Some(ctx)`, uses one-way Maude matching +
/// `someInst keepVarBindings` + `conjoinSystem` setNodes-collision
/// rule-eqs. When `None`, falls back to the legacy graft (preserves
/// older behaviour for callers that don't have a context — e.g.
/// saturate-time helpers).
pub fn solve_with_source_cases_action_with_ctx(
    sources: &[Source],
    sys: &System,
    goal_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
    avoid_max: u64,
    ctx_opt: Option<&crate::constraint::solver::context::ProofContext>,
) -> Option<Vec<(String, System, crate::fact::LNFact)>> {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Only KU-tagged Action goals consult action sources.
    if fa_live.tag != FactTag::Ku || fa_live.terms.len() != 1 {
        return None;
    }
    let m_live = &fa_live.terms[0];
    let _ = LSort::Msg; // silence unused-import warning at low cost
    if std::env::var("TAM_DBG_SRC_CASE").is_ok() {
        let live_str = format!("{:?}", fa_live).chars().take(120).collect::<String>();
        eprintln!("[src_case] solve_with_source_cases CALLED for live={}", live_str);
    }

    // Find a source whose abstract pattern matches `m_live`.
    let src = sources.iter().find(|s| match &s.goal {
        Goal::Action(_, gfa) => {
            if gfa.tag != FactTag::Ku || gfa.terms.len() != 1 {
                return false;
            }
            let pat = &gfa.terms[0];
            match (pat, m_live) {
                (Term::Lit(Lit::Var(pv)), _) => {
                    let live_sort = sort_of_lnterm(m_live);
                    sort_ge(pv.sort, live_sort)
                }
                (Term::App(pf, pargs), Term::App(lf, largs)) => {
                    pf == lf && pargs.len() == largs.len()
                }
                _ => false,
            }
        }
        _ => false,
    })?;

    let abstract_orig = match &src.goal {
        Goal::Action(n, _) => n.clone(),
        _ => return None,
    };

    if std::env::var("TAM_RS_TRACE_APPLY_SRC").is_ok() {
        let goal_str = format!("{:?}", fa_live).chars().take(200).collect::<String>();
        let case_names: Vec<&String> = src.cases.iter().map(|(n, _)| n).collect();
        eprintln!("[RS_APPLY_SRC_PRE] live_goal={} cases={:?}", goal_str, case_names);
    }
    if std::env::var("TAM_DBG_SRC_CASE").is_ok() {
        let goal_str = format!("{:?}", fa_live).chars().take(120).collect::<String>();
        eprintln!("[src_case] LIVE goal={}", goal_str);
        for (n, c) in &src.cases {
            eprintln!("[src_case] name={} nodes={} edges={} goals={} last_atom={:?}",
                n, c.nodes.len(), c.edges.len(), c.goals.len(), c.last_atom);
            for (id, ru) in &c.nodes {
                let nm = crate::constraint::solver::reduction::rule_case_name(ru);
                eprintln!("[src_case]   node {:?} → {}", id, nm);
            }
        }
    }

    let mut out: Vec<(String, System, crate::fact::LNFact)> = Vec::new();
    for (name, case_sys) in &src.cases {
        let case_label = saturated_chain_root(name);
        // Haskell-faithful `applySource` path when a ProofContext is
        // available.  Matches the live goal against the source's
        // ABSTRACT `cdGoal` (`src.goal`) — NOT a case-specific action.
        // This mirrors `matchToGoal` (Sources.hs:268) which always
        // uses `cdGoal`.  Then runs `someInst keepVarBindings` +
        // `conjoinSystem`.
        //
        // The legacy fallback remains for `saturate_out_premise` etc.
        // which compute source-cases at precompute time and don't have
        // a ProofContext handy.  Setting `TAM_LEGACY_APPLY_SOURCE=1`
        // forces the legacy path everywhere for diagnostics.
        let use_legacy = std::env::var("TAM_LEGACY_APPLY_SOURCE").is_ok();
        if let Some(ctx) = ctx_opt {
            if !use_legacy {
                let result = apply_source_case_action(
                    ctx, sys, src, case_sys, goal_node, fa_live);
                if let Some((mut grafted_sys, live_action)) = result {
                    if src.incomplete { grafted_sys.used_incomplete_source = true; }
                    // Eagerly fan out small variant SplitG goals into
                    // separate Disj cases.  Mirrors Haskell's saturate
                    // which (via solveAllSafeGoals's Disj-monad
                    // branching on small SplitG) produces one case per
                    // variant arm at PRECOMPUTE time — leaving no
                    // SplitG in the runtime state.  Our precompute
                    // single-branches, so the variant SplitG survives
                    // until runtime; without this fan-out, runtime
                    // goal-ranking picks `case split` (S2 cluster).
                    //
                    // Skip when TAM_DISABLE_VARIANT_FANOUT=1 (diagnostic).
                    let fanout = std::env::var("TAM_DISABLE_VARIANT_FANOUT").is_err();
                    if fanout {
                        let expanded = fanout_variant_splits(
                            ctx, grafted_sys, &live_action, &case_label);
                        for (sub_name, mut sub_sys, sub_action) in expanded {
                            // Haskell `solveAllSafeGoals` (saturate-time)
                            // applies 1-case `c_<sym>` constructor
                            // sources to open KU goals whose head
                            // matches.  These pass `goodTh` (Sources.hs:381)
                            // — saturate's source-pick (`asum`
                            // Sources.hs:206) eagerly applies them at
                            // PRECOMPUTE time.  Multi-case sources (KU
                            // sign with c_sign + Abort1 + Resolve*) FAIL
                            // goodTh and stay open for runtime selection.
                            //
                            // Our precomputed source cases don't always
                            // reflect saturate's auto-resolution because
                            // the variant SplitG is collapsed before the
                            // KU-expansion pass sees the variant-
                            // substituted head term (e.g. Abort1's
                            // `pcsig1 = pcs(sign(...),...)`).  Replicate
                            // the effect at runtime: walk open KU goals
                            // and auto-apply single-case `c_<sym>`
                            // sources whose abstract head matches.
                            //
                            // Skip via TAM_DISABLE_KU_AUTORESOLVE=1.
                            if std::env::var("TAM_DISABLE_KU_AUTORESOLVE").is_err() {
                                if let Some(ctx_ref) = ctx_opt {
                                    auto_resolve_single_case_ku(
                                        ctx_ref, &mut sub_sys);
                                }
                            }
                            out.push((sub_name, sub_sys, sub_action));
                        }
                    } else {
                        out.push((case_label, grafted_sys, live_action));
                    }
                }
                let _ = name;
                continue;
            }
        }
        // Legacy path: freshen + graft + caller-runs-solve_fact_eqs.
        // Used at saturate time (no ProofContext) and when
        // TAM_LEGACY_APPLY_SOURCE=1 forces it.
        let renamed = freshen_system(case_sys, avoid_max, ctx_opt.map(|c| &c.maude));
        let abstract_renamed = {
            let mut v = abstract_orig.clone();
            v.idx = v.idx.saturating_add(avoid_max.saturating_add(1));
            v
        };
        let action_fact = renamed.nodes.iter().find_map(|(id, ru)| {
            if id == &abstract_renamed {
                ru.actions.iter().find(|a| a.tag == FactTag::Ku).cloned()
            } else { None }
        });
        let Some(action_fact) = action_fact else { continue };
        let Some(mut grafted) = graft_case_into_action(
            sys, &renamed, &abstract_renamed, goal_node, fa_live,
        ) else { continue };
        if src.incomplete { grafted.used_incomplete_source = true; }
        out.push((case_label, grafted, action_fact));
    }
    if out.is_empty() { return None; }
    Some(out)
}

/// Eagerly fan out small variant SplitG goals from a grafted source
/// case into separate Disj cases (one per surviving variant arm).
/// Mirrors Haskell's saturate's solveAllSafeGoals Disj-monad branching
/// on small SplitGs — Haskell's precomputed source cases contain NO
/// SplitG (each variant arm became its own case during saturate).
/// Our precompute single-branches, so the variant SplitG persists; we
/// fan it out at apply-source-case time instead.
///
/// Limited to "small" SplitG (size ≤ 3) — same threshold as
/// `is_split_goal_small`.  Large SplitGs stay as goals (matching
/// Haskell's smartRanking, which only ranks small SplitGs in
/// solveFirst).
///
/// Returns Vec<(case_name, sys, action)> — one entry per surviving
/// variant arm.  Empty Vec when no fan-out applies (returns the
/// original triple).
fn fanout_variant_splits(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: crate::constraint::system::System,
    live_action: &crate::fact::LNFact,
    case_label: &str,
) -> Vec<(String, crate::constraint::system::System, crate::fact::LNFact)> {
    use crate::constraint::solver::reduction::{Reduction, SolveOutcome, GoalCases};
    use crate::constraint::constraints::Goal;
    const SMALL: usize = 3;
    // Find first small SplitG goal.
    let small_split: Option<crate::tools::equation_store::SplitId> =
        sys.goals.iter().find_map(|(g, st)| {
            if st.solved || st.looping { return None; }
            let Goal::Split(id) = g else { return None };
            let sz = sys.eq_store.split_size(*id)?;
            if sz > 1 && sz <= SMALL { Some(*id) } else { None }
        });
    let Some(split_id) = small_split else {
        return vec![(case_label.to_string(), sys, live_action.clone())];
    };
    let mut red = Reduction::new(ctx, sys);
    let outcome = red.solve_split_goal(split_id);
    let raw_cases: Vec<crate::constraint::system::System> = match outcome {
        GoalCases::Cases(cases) if !cases.is_empty() => {
            cases.into_iter().map(|(_, sub_sys)| sub_sys).collect()
        }
        GoalCases::Linear | GoalCases::LinearNamed(_) => {
            vec![red.sys]
        }
        GoalCases::Contradictory | GoalCases::Cases(_) => {
            return Vec::new();
        }
    };
    // Dedup variant fanout by canonical-system structural form.
    // Haskell's saturate-time fanout produces source cases that look
    // distinct in eq_store but identical in structural (nodes/edges/
    // premises/conclusions/actions) shape.  Without dedup, our runtime
    // apply emits N variant-cases that each render an identical proof
    // subtree under `_case_N` suffixes — Haskell shows ONE case.
    //
    // Use canonicalise_system which renames vars deterministically and
    // ignores eq_store; this catches "same shape, different name hints"
    // variants that produce equivalent downstream proofs.
    //
    // Haskell-faithful `removeRedundantCases` gate (Sources.hs:240):
    // BP/MSet only.  See site at refineSource (line ~3107).
    let dedup_enabled = {
        let s = ctx.maude.maude_sig();
        s.enable_bp || s.enable_mset
    };
    let mut seen_keys: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut out: Vec<(String, crate::constraint::system::System, crate::fact::LNFact)> = Vec::new();
    for sub_sys in raw_cases {
        if dedup_enabled {
            let key = canonicalise_system(&sub_sys);
            if !seen_keys.insert(key) { continue; }
        }
        out.push((case_label.to_string(), sub_sys, live_action.clone()));
    }
    out
}

/// Apply 1-case `c_<sym>` constructor sources to any open KU goal in
/// `sys` whose head term matches the source's abstract head.  Iterates
/// to fixpoint (up to a small cap to bound runtime).  Mutates `sys`
/// in place, marking the resolved KU goal as solved and grafting the
/// source case's nodes/edges/sub-goals.
///
/// Mirrors the effect of Haskell `solveAllSafeGoals`'s saturate-time
/// source-pick on `filter goodTh ths` (Sources.hs:206, 380-385).
/// Haskell pre-resolves these constructor decompositions during
/// `saturateSources` so their renderings collapse via `refineSource.
/// combine` (Sources.hs:135-137 keeps the FIRST non-coerce name).
/// Our precomputed cases don't always do this — the variant SplitG
/// collapses before KU-expansion sees the substituted head — so we
/// apply the auto-resolution here at runtime instead.
fn auto_resolve_single_case_ku(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: &mut System,
) {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::Reduction;
    use crate::fact::FactTag;
    use tamarin_term::term::Term;
    use tamarin_term::function_symbols::FunSym;

    // Build (source-index → head sym name) map for 1-case `c_<sym>`
    // sources whose abstract goal is `KU(<sym>(t.1, t.2, …))` (an
    // App-headed pattern).  These are the only sources we will
    // auto-apply: 1 case (passes goodTh), head is a NoEqSym App.
    let candidates: Vec<(usize, Vec<u8>)> = ctx.full_sources.iter().enumerate()
        .filter_map(|(idx, s)| {
            if s.cases.len() != 1 { return None; }
            match &s.goal {
                Goal::Action(_, fa)
                    if fa.tag == FactTag::Ku && fa.terms.len() == 1 =>
                {
                    match &fa.terms[0] {
                        Term::App(FunSym::NoEq(noeq), _) => {
                            Some((idx, noeq.name.clone()))
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        })
        .collect();
    if candidates.is_empty() { return; }

    // Iterate to fixpoint (cap at 16 to avoid runaway).
    for _iter in 0..16 {
        // Find an open KU action goal whose term head matches a
        // candidate source's head.
        let pick: Option<(crate::constraint::constraints::NodeId,
                          crate::fact::LNFact,
                          usize)> = sys.goals.iter().find_map(|(g, st)| {
            if st.solved || st.looping { return None; }
            let (node, fa) = match g {
                Goal::Action(n, fa) if matches!(fa.tag, FactTag::Ku)
                    && fa.terms.len() == 1 => (n.clone(), fa.clone()),
                _ => return None,
            };
            // Live term must have a NoEqSym App head matching a
            // candidate source.
            let live_name: &[u8] = match &fa.terms[0] {
                Term::App(FunSym::NoEq(noeq), _) => &noeq.name,
                _ => return None,
            };
            // Skip pair/inv (handled by insertAction).
            if live_name == b"pair" { return None; }
            use tamarin_term::function_symbols::INV_SYM_STRING;
            if live_name == INV_SYM_STRING { return None; }
            // Find matching candidate source.
            candidates.iter()
                .find(|(_, sym)| sym.as_slice() == live_name)
                .map(|(idx, _)| (node, fa, *idx))
        });
        let Some((live_node, live_fa, src_idx)) = pick else { break; };
        let src = &ctx.full_sources[src_idx];
        let avoid_max = system_max_idx(sys);
        // Apply the source's single case via `apply_source_case_action`
        // (the Haskell-faithful `applySource` path).
        let Some((_, case_sys)) = src.cases.first() else { break; };
        let Some((mut grafted, _)) = apply_source_case_action(
            ctx, sys, src, case_sys, &live_node, &live_fa
        ) else { break; };
        // Sanity: mark the live KU goal solved if not already.
        let live_goal = Goal::Action(live_node.clone(), live_fa.clone());
        for (g, st) in grafted.goals.iter_mut() {
            if g == &live_goal { st.solved = true; break; }
        }
        let _ = avoid_max;  // avoid unused-var warning
        // Run a quick simplify on the grafted system.
        let mut r = Reduction::new(ctx, grafted);
        crate::constraint::solver::simplify::simplify_system(&mut r);
        // If the simplify produced a contradictory state, stop —
        // caller will detect and drop.
        let contradicted = !crate::constraint::solver::contradictions::
            contradictions(ctx, &r.sys).is_empty();
        if contradicted { break; }
        *sys = r.sys;
    }
}

/// Extract the chain-root case name from a saturated source-case
/// name.  Names are built by `saturate_out_premise` appending
/// `_<producer>` for each fold:
///
///   "coerce_case_1_A"        → "A"        (legacy: case-marker form)
///   "coerce_irecv_SendBoth"  → "SendBoth" (post-chain-extension form)
///   "coerce_irecv"           → "irecv"    (un-folded leaf)
///   "c_fresh"                → "c_fresh"  (no chain, single rule)
///   "coerce"                 → "coerce"   (un-folded)
///
/// The strategy:
///   1. Strip a leading `_case_<n>_` segment if present (legacy).
///   2. Strip leading intruder-rule prefixes (`coerce_`, `irecv_`,
///      `c_<sym>_`) — the chain's interior intruder hops.  Remaining
///      head is the protocol producer (or the last intruder if no
///      protocol producer was reached).
/// Mirror Haskell `refineSource`'s `combine` function
/// (`Sources.hs:135-137`):
///
/// ```haskell
/// combine []            ns' = ns'
/// combine ("coerce":ns) ns' = combine ns ns'
/// combine (n       :_)  _   = [n]
/// ```
///
/// Treats the underscore-separated `name` as the accumulated case-name
/// list and `sub_name` as the new step's single-element list.
/// Result is the underscore-joined effective list — the FIRST
/// non-coerce segment from `name`, falling back to `sub_name` if
/// `name` is empty or entirely "coerce" segments.
fn combine_case_names(name: &str, sub_name: &str) -> String {
    // Haskell `combine`:
    //   combine []            ns' = ns'
    //   combine ("coerce":ns) ns' = combine ns ns'
    //   combine (n       :_)  _   = [n]
    //
    // Treats names as a LIST of (single) case-names accumulated from
    // each refinement step. Strips leading "coerce" entries, then keeps
    // the FIRST non-coerce name and DISCARDS the rest (including the
    // new step's name).
    //
    // Our representation accumulates the name list as a single
    // underscore-joined string. To recover the list boundary correctly
    // for rule names like `I_1`, we treat known intruder prefixes as
    // their own list entries: `coerce`, `irecv`, `ipub`, `isend`, and
    // `c_<sym>` (constructors). Anything else, including `I_1` /
    // `Reveal_ltk`, is the actual rule name and stops the strip.
    let mut tail = name;
    loop {
        if let Some(rest) = tail.strip_prefix("coerce_") {
            tail = rest; continue;
        }
        if tail == "coerce" {
            // All-coerce name → fall through to sub_name.
            return sub_name.to_string();
        }
        if let Some(rest) = tail.strip_prefix("irecv_") {
            tail = rest; continue;
        }
        if tail == "irecv" {
            return sub_name.to_string();
        }
        if let Some(rest) = tail.strip_prefix("ipub_") {
            tail = rest; continue;
        }
        if let Some(rest) = tail.strip_prefix("isend_") {
            tail = rest; continue;
        }
        // `c_<sym>_<rest>` — strip leading constructor.  We require the
        // sym segment (after `c_`) to be a single underscore-bounded
        // ident — `c_aenc`, `c_h`, `c_pk`, etc.  A bare `c_fresh` /
        // `c_pub` (no trailing `_<rest>`) is the actual case name and
        // stops the strip.
        if let Some(rest_after_c) = tail.strip_prefix("c_") {
            if let Some(pos) = rest_after_c.find('_') {
                tail = &rest_after_c[pos + 1..];
                continue;
            }
        }
        break;
    }
    if tail.is_empty() { sub_name.to_string() } else { tail.to_string() }
}

fn saturated_chain_root(name: &str) -> String {
    // Step 1: legacy `_case_<n>_` stripping.
    let bytes = name.as_bytes();
    let mut best_end = 0usize;
    let mut i = 0;
    while i + 6 < bytes.len() {
        if &bytes[i..i+6] == b"_case_" {
            let mut j = i + 6;
            while j < bytes.len() && bytes[j].is_ascii_digit() { j += 1; }
            if j > i + 6 && j < bytes.len() && bytes[j] == b'_' {
                best_end = j + 1;
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
    let mut tail: &str = if best_end > 0 && best_end < bytes.len() {
        &name[best_end..]
    } else {
        name
    };
    // Step 2: strip leading intruder-rule chain prefixes.  Each iter
    // peels one segment if it matches a known intruder rule.
    loop {
        let next = if let Some(s) = tail.strip_prefix("coerce_") {
            Some(s)
        } else if let Some(s) = tail.strip_prefix("irecv_") {
            Some(s)
        } else if let Some(s) = tail.strip_prefix("ipub_") {
            Some(s)
        } else if let Some(s) = tail.strip_prefix("isend_") {
            Some(s)
        } else if tail.starts_with("c_") {
            // `c_<sym>_<rest>` — strip `c_<sym>_`.
            if let Some(pos) = tail[2..].find('_') {
                Some(&tail[2 + pos + 1..])
            } else { None }
        } else { None };
        match next {
            Some(n) if !n.is_empty() => tail = n,
            _ => break,
        }
    }
    // Step 3: strip trailing `_case_<N>` suffix.  Saturate
    // (`saturate_out_premise`) appends `_case_<k>` to disambiguate
    // multiple closures of the same sub-rule chain.  Haskell's
    // `refineSource.combine` (Sources.hs:135-137) just keeps the first
    // non-coerce name without a per-closure suffix — multiple cases
    // sharing the same root name are disambiguated at runtime via
    // `distinguish` (ProofMethod.hs:468-473) IF their proof-tree
    // siblings collide.  By stripping the saturate-time suffix here, we
    // let the runtime renderer's dedup do the same job from a clean
    // slate, matching Haskell's `Alice` vs `Alice_case_1`/`_case_2`
    // sibling layout.
    let stripped: &str = {
        // Walk back from the end looking for `_case_<digits>` (no
        // trailing underscore — `_case_<N>` is the LAST segment).
        let b = tail.as_bytes();
        let mut k = b.len();
        // Trailing digits.
        let mut d = 0;
        while k > 0 && b[k - 1].is_ascii_digit() {
            k -= 1; d += 1;
        }
        // Need `_case_` before the digits.
        if d > 0 && k >= 6 && &b[k - 6..k] == b"_case_" {
            &tail[..k - 6]
        } else {
            tail
        }
    };
    stripped.to_string()
}

/// Compute the term's "effective" sort.  Variables carry their sort;
/// applications default to Msg (the join of all sub-sorts).
fn sort_of_lnterm(t: &tamarin_term::lterm::LNTerm) -> tamarin_term::lterm::LSort {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => v.sort,
        Term::Lit(Lit::Con(_)) => LSort::Pub,
        _ => LSort::Msg,
    }
}

/// `a >= b` in the sort order Pub/Fresh/Nat ⊂ Msg.
fn sort_ge(a: tamarin_term::lterm::LSort, b: tamarin_term::lterm::LSort) -> bool {
    use tamarin_term::lterm::LSort;
    if a == b { return true; }
    matches!(a, LSort::Msg) && matches!(b, LSort::Pub | LSort::Fresh | LSort::Nat)
}

/// `restrict` the system's eq-store `subst` (`sSubst`) to bindings
/// whose KEY var is in `stable_vars`.  Mirrors Haskell's
/// `modify sSubst (restrict stableVars)` inside `refineSource`
/// (Sources.hs:123).  All bindings keyed on rule-internal vars
/// (vars not free in the abstract `cdGoal`) are dropped.
///
/// Without this restriction, the case's eq-store at precompute time
/// retains `t:Fresh:1 → ~ltk:Fresh:N` (the abstract pattern var
/// bound to a rule's specific Fresh var).  At runtime, when
/// `apply_source_case_action` adds the match-subst `t:Fresh:1
/// (renamed) → ~ltkA:Fresh` to the eq-store, Maude's `addEqs`
/// chains: `~ltk:Fresh:N (renamed) = ~ltkA:Fresh`.  After
/// `subst_system`, the case's grafted Fresh-rule node has
/// conclusion `Fr(~ltkA)` — same as live's existing Fresh-rule.
/// `enforce_fresh_node_uniqueness_pass` then merges these into a
/// single producer, which later trips `prem_idx_clash` because the
/// merged producer feeds two distinct premise positions of different
/// rules.
///
/// Haskell prevents this by restricting `sSubst` to `stableVars`
/// after every `refineSource` call (saturateSources iterations
/// + matchToGoal's refineSubst).  Both places need the restrict
/// for runtime applySource to see a clean precomputed case.
/// Flip same-sort var-var bindings `x → y` where `y` is in `stable_vars`
/// but `x` is not.  Result `y → x` is Haskell-equivalent (both encode
/// `x = y`) but survives the subsequent key-filter restrict.
///
/// Why this is needed: Haskell-faithful LVar Ord (idx-first) +
/// `unify_lterm_factored` (larger-idx-as-key) orient bindings so the
/// rule-internal var (large idx, NOT stable) becomes the key.  Restrict
/// then drops the binding even though it carries load-bearing constraint
/// info (e.g. `t#1 = kZero` ↔ same goal var = rule's conclusion arg).
/// Without the binding, runtime `apply_source_case_premise`'s refineSubst
/// (sources.rs:5503) trivially succeeds where Haskell would contradict
/// via downstream substSystem propagation in the case_sys.
fn flip_to_stable_keys(
    sys: &mut System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let trace = std::env::var("TAM_DBG_FLIP").is_ok();
    let mut kept: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = Vec::new();
    let mut flipped: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = Vec::new();
    for (k, v) in sys.eq_store.subst.to_list() {
        let Term::Lit(Lit::Var(target_var)) = &v else {
            kept.push((k, v));
            continue;
        };
        // Already correct orientation (key is stable).
        if stable_vars.contains(&k) {
            kept.push((k, v));
            continue;
        }
        // Flip if value is stable AND sort-compatible (same sort, or
        // value's sort is broader so flipping doesn't widen).
        if stable_vars.contains(target_var) {
            // Allow flip when key's sort can be substituted by value's sort
            // (i.e. value sort >= key sort in the lattice).  Same sort is OK.
            // Cross-sort flip would invert direction which could widen the
            // sort of the stable var — skip those.
            if target_var.sort == k.sort {
                if trace {
                    eprintln!("[flip] {}#{}({:?})→{}#{}({:?})  TO  {}#{}({:?})→{}#{}({:?})",
                        k.name, k.idx, k.sort, target_var.name, target_var.idx, target_var.sort,
                        target_var.name, target_var.idx, target_var.sort,
                        k.name, k.idx, k.sort);
                }
                flipped.push((target_var.clone(), Term::Lit(Lit::Var(k))));
                continue;
            }
        }
        kept.push((k, v));
    }
    // Add flipped entries, but only if both:
    // (a) target isn't already a key (preserves domain disjointness), AND
    // (b) target isn't a VALUE of any kept binding (flipping would
    //     introduce a chain `kept_key → target → kept_value`, breaking
    //     idempotency — see `restrict_eq_store_does_not_chain_chase`
    //     test for the Haskell invariant).
    //
    // Haskell does NOT flip at all — `restrict` is a pure key-filter.
    // Our flip exists to preserve rule-internal-to-canonical bindings
    // that would otherwise be lost.  Skipping flips that would create
    // chains keeps the idempotency invariant Haskell relies on for
    // `applyVTerm` correctness.
    //
    // Concrete trigger for the chain-introducing case (task #222
    // Loop_Start): saturate-time `{loopId:6 → t:1, kOrig:6 → t:2,
    // t:3 → t:2}`.  Naively flipping `kOrig:6 → t:2` to `t:2 → kOrig:6`
    // would create the chain `t:3 → t:2 → kOrig:6`, breaking the
    // idempotency Haskell's `applyVTerm` relies on (it does ONE
    // lookup, not chain-chase).  The downstream runtime then fails to
    // propagate the Check0 repeated-arg equivalence to the lemma's
    // `k = kOrig` constraint.
    let mut existing_keys: std::collections::BTreeSet<tamarin_term::lterm::LVar> =
        kept.iter().map(|(k, _)| k.clone()).collect();
    let value_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar> = kept.iter()
        .filter_map(|(_, v)| match v {
            Term::Lit(Lit::Var(w)) => Some(w.clone()),
            _ => None,
        })
        .collect();
    for (k, v) in flipped {
        if existing_keys.contains(&k) { continue; }
        if value_vars.contains(&k) { continue; }   // flipping creates a chain
        existing_keys.insert(k.clone());
        kept.push((k, v));
    }
    sys.eq_store.subst = tamarin_term::subst::Subst::from_list(kept);
}

fn restrict_eq_store_to_stable_vars(
    sys: &mut System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) {
    // Flip non-stable→stable var-var bindings so the stable var becomes
    // the key, preserving the binding under the subsequent key-filter.
    // See doc-comment on `flip_to_stable_keys`.
    flip_to_stable_keys(sys, stable_vars);
    // Build a (name, idx) set from stable_vars: under cross-sort unification,
    // a stable var like `t#1:Msg` can be narrowed to `t#1:Fresh` and
    // re-appear in the eq_store as a different LVar (Rust's PartialEq
    // requires sort to match).  Haskell's `restrict` filters by full
    // LVar identity, but in Haskell the narrowing always produces a
    // binding `t#1:Msg → seed:Fresh` (Msg as key), so the issue doesn't
    // arise.  In Rust post-LVar, sort narrowing via apply_lvar_subst
    // can rebind the eq_store key to `t#1:Fresh`.  Keep both forms by
    // matching on (name, idx).
    // Haskell's `restrict` in `Theory.Tools.EquationStore`
    // (EquationStore.hs:289 via Term.Substitution.Subst.restrict) is a
    // simple key-filter: `Subst (M.filterWithKey (\k _ -> k `elem` vars) m)`.
    // It does NOT chase chains.  Keys not in `vars` are dropped, and
    // values that referenced those dropped keys become dangling — which
    // is fine because Haskell's substitution lookup falls back to
    // identity for unbound vars.
    //
    // Earlier this function chained-chased values to a fixed point
    // before filtering, which collapsed e.g. `t:1 → e_A_1 → blind(...)`
    // into `t:1 → blind(...)` directly.  The chain-chased binding
    // survived restrict (because t:1 is stable), and at runtime
    // `apply_source_case_action`'s `refineSubst` then tried to unify
    // `t:1 = commit(z, r)` against the now-direct binding
    // `t:1 → blind(...)`, which fails (commit vs blind).  Haskell
    // doesn't do this chain-chase, so its `t:1 → e_A_1` survives with
    // `e_A_1` unbound (since e_A_1 isn't in stable_vars); the
    // runtime match then binds `e_A_1 = commit(z, r)` cleanly, and any
    // downstream `[sources]`-axiom violation is caught via
    // `FormulasFalse` rather than `refineSubst-contradictory`.
    let stable_name_idx: std::collections::BTreeSet<(String, u64)> =
        stable_vars.iter().map(|v| (v.name.clone(), v.idx)).collect();
    let kept: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)>
        = sys.eq_store.subst.to_list().into_iter()
            .filter(|(v, _)| {
                stable_vars.contains(v)
                    || stable_name_idx.contains(&(v.name.clone(), v.idx))
            })
            .collect();
    sys.eq_store.subst = tamarin_term::subst::Subst::from_list(kept);
}

/// Compute the goal's free vars (= `stableVars` in Haskell).  For
/// an `ActionG i fa` this is `[i] ++ frees fa`; for `PremiseG (i,_) fa`
/// likewise.  Mirrors Haskell's `frees (cdGoal th)` (Sources.hs:126).
fn stable_vars_for_goal(
    goal: &crate::constraint::constraints::Goal,
) -> std::collections::BTreeSet<tamarin_term::lterm::LVar> {
    use tamarin_term::lterm::HasFrees;
    let mut out = std::collections::BTreeSet::new();
    match goal {
        crate::constraint::constraints::Goal::Action(i, fa) => {
            out.insert(i.clone());
            fa.for_each_free(&mut |v: &tamarin_term::lterm::LVar| {
                out.insert(v.clone());
            });
        }
        crate::constraint::constraints::Goal::Premise((i, _), fa) => {
            out.insert(i.clone());
            fa.for_each_free(&mut |v: &tamarin_term::lterm::LVar| {
                out.insert(v.clone());
            });
        }
        crate::constraint::constraints::Goal::Chain(c, p) => {
            out.insert(c.0.clone());
            out.insert(p.0.clone());
        }
        crate::constraint::constraints::Goal::Disj(_)
        | crate::constraint::constraints::Goal::Split(_)
        | crate::constraint::constraints::Goal::Subterm(_) => {}
    }
    out
}

/// Freshen all vars in `sys` EXCEPT those in `keep`. Mirrors Haskell's
/// `someInst sysTh0 keepVarBindings` (Sources.hs:348). Vars in `keep`
/// are preserved (they correspond to live-system vars introduced by
/// the match-subst); other vars get shifted via the MaudeHandle's
/// global counter so they don't collide with live-system vars OR with
/// vars from prior applySource grafts.
///
/// **Haskell-faithful counter (MonadFresh)**: when `maude` is supplied,
/// the shift base comes from `reserve_idxs(sys_max + 1)` against the
/// global counter — guaranteeing each apply_source graft gets a
/// globally-unique idx range.  Without this, two applySource calls
/// with the same `avoid_max` (e.g. the same live system at the same
/// step) would shift to identical idxs, creating spurious cycles in
/// the resulting joined system (TLS_Handshake::session_key_setup_possible
/// root cause).  Falls back to `avoid_max + 1` when no MaudeHandle
/// is supplied.
#[allow(dead_code)]
fn freshen_system_keep(
    sys: &System,
    avoid_max: u64,
    keep: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) -> System {
    freshen_system_keep_with_shift(sys, avoid_max.saturating_add(1), keep)
}

fn freshen_system_keep_with_shift(
    sys: &System,
    shift_amount: u64,
    keep: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) -> System {
    use tamarin_term::lterm::HasFrees;
    let shift_lvar = |v: &tamarin_term::lterm::LVar| {
        if keep.contains(v) {
            v.clone()
        } else {
            let mut v2 = v.clone();
            v2.idx = v2.idx.saturating_add(shift_amount);
            v2
        }
    };
    // Haskell-faithful `mapFrees` on parser-AST `VarSpec` (used by
    // Guarded formulas): mirror `shift_lvar` semantics — skip keep,
    // shift idx otherwise.  Project keep to `(name, idx)` since
    // VarSpec sort and LVar sort are distinct types and in-practice
    // names disambiguate node vs message vars.
    let keep_name_idx: std::collections::BTreeSet<(String, u64)> = keep.iter()
        .map(|v| (v.name.clone(), v.idx))
        .collect();
    let shift_vs = |v: &tamarin_parser::ast::VarSpec| {
        if keep_name_idx.contains(&(v.name.clone(), v.idx)) {
            v.clone()
        } else {
            tamarin_parser::ast::VarSpec {
                name: v.name.clone(),
                idx: v.idx.saturating_add(shift_amount),
                sort: v.sort,
                typ: v.typ.clone(),
            }
        }
    };
    let mut out = sys.clone();
    out.nodes = out.nodes.into_iter()
        .map(|(id, ru)| (shift_lvar(&id), ru.map_free(&mut |v| shift_lvar(&v))))
        .collect();
    out.edges = out.edges.into_iter()
        .map(|e| crate::constraint::constraints::Edge {
            src: (shift_lvar(&e.src.0), e.src.1),
            tgt: (shift_lvar(&e.tgt.0), e.tgt.1),
        })
        .collect();
    out.less_atoms = out.less_atoms.into_iter()
        .map(|l| crate::constraint::constraints::LessAtom::new(
            shift_lvar(&l.smaller),
            shift_lvar(&l.larger),
            l.reason,
        ))
        .collect();
    out.goals = out.goals.into_iter()
        .map(|(g, st)| {
            let g2 = match g {
                crate::constraint::constraints::Goal::Action(n, fa) =>
                    crate::constraint::constraints::Goal::Action(
                        shift_lvar(&n),
                        fa.map_free(&mut |v| shift_lvar(&v))),
                crate::constraint::constraints::Goal::Premise(p, fa) =>
                    crate::constraint::constraints::Goal::Premise(
                        (shift_lvar(&p.0), p.1),
                        fa.map_free(&mut |v| shift_lvar(&v))),
                crate::constraint::constraints::Goal::Chain(c, p) =>
                    crate::constraint::constraints::Goal::Chain(
                        (shift_lvar(&c.0), c.1),
                        (shift_lvar(&p.0), p.1)),
                // Haskell-faithful: Disj carries guarded formulas;
                // Subterm carries an (LNTerm, LNTerm) pair.  Their
                // free vars must shift too.  Split(SplitId) is an
                // opaque index — no vars to rename.
                crate::constraint::constraints::Goal::Disj(d) => {
                    let mapped: Vec<_> = d.0.into_iter()
                        .map(|alt| crate::guarded::map_lvars_in_guarded(&alt, &shift_vs))
                        .collect();
                    crate::constraint::constraints::Goal::Disj(
                        crate::constraint::constraints::Disj(mapped))
                }
                crate::constraint::constraints::Goal::Subterm((small, big)) =>
                    crate::constraint::constraints::Goal::Subterm((
                        small.map_free(&mut |v| shift_lvar(&v)),
                        big.map_free(&mut |v| shift_lvar(&v)))),
                other @ crate::constraint::constraints::Goal::Split(_) => other,
            };
            (g2, st)
        })
        .collect();
    if let Some(la) = out.last_atom.take() {
        out.last_atom = Some(shift_lvar(&la));
    }
    // Haskell-faithful: shift free LVars in `formulas`, `solved_formulas`,
    // and `lemmas`.  Haskell's `mapFrees` on System (System.hs:1863-1876)
    // traverses ALL 13 fields — without this, post-freshen formulas/
    // lemmas reference pre-freshen var idxs and collide with live
    // post-shift node/edge idxs.
    out.formulas = out.formulas.into_iter()
        .map(|g| crate::guarded::map_lvars_in_guarded(&g, &shift_vs))
        .collect();
    out.solved_formulas = out.solved_formulas.into_iter()
        .map(|g| crate::guarded::map_lvars_in_guarded(&g, &shift_vs))
        .collect();
    out.lemmas = out.lemmas.into_iter()
        .map(|g| crate::guarded::map_lvars_in_guarded(&g, &shift_vs))
        .collect();
    // Shift LNTerm vars inside subterm_store constraints.
    for c in &mut out.subterm_store.subterms {
        c.small = c.small.clone().map_free(&mut |v| shift_lvar(&v));
        c.big = c.big.clone().map_free(&mut |v| shift_lvar(&v));
    }
    for c in &mut out.subterm_store.solved_subterms {
        c.small = c.small.clone().map_free(&mut |v| shift_lvar(&v));
        c.big = c.big.clone().map_free(&mut |v| shift_lvar(&v));
    }
    // Eq-store subst: shift both var keys and term values.
    out.eq_store.subst = {
        let pairs: Vec<_> = out.eq_store.subst.to_list().into_iter()
            .map(|(v, t)| {
                let new_v = shift_lvar(&v);
                let new_t = t.map_free(&mut |w| shift_lvar(&w));
                (new_v, new_t)
            })
            .collect();
        tamarin_term::subst::Subst::from_list(pairs)
    };
    // Eq-store conj (SplitG disjunctions): shift both var keys and
    // term values in each variant subst.  Without this, the variant
    // SplitG's substs still reference pre-freshen var idxs while the
    // surrounding nodes/edges/goals carry post-freshen idxs — so when
    // a variant is picked via `solve_split_goal` and folded into the
    // free subst via `simp_singleton`, `subst_system` finds no
    // matching keys to substitute, leaving the rule nodes with bare
    // msg-vars (e.g. `pk1`) instead of the narrowed `pk(x)` form.
    // This causes the StatVerif `resolved1_contract_reachable`
    // premature-SOLVED bug.
    for disj in out.eq_store.conj.iter_mut() {
        for s in disj.substs.iter_mut() {
            let pairs: Vec<_> = s.to_list().into_iter()
                .map(|(v, t)| {
                    let new_v = shift_lvar(&v);
                    let new_t = t.clone().map_free(&mut |w| shift_lvar(&w));
                    (new_v, new_t)
                })
                .collect();
            *s = tamarin_term::subst_vfresh::SubstVFresh::from_list(pairs);
        }
    }
    out
}

/// Apply a precomputed source case to a live action goal — Haskell-
/// faithful port of `applySource` (Sources.hs:336-350):
///
/// ```haskell
/// applySource ctxt th0 goal = matchToGoal ctxt th0 goal >>= \th -> do
///   markGoalAsSolved goal
///   (names, sysTh0) <- disjunctionOfList $ get cdCases th
///   sysTh <- evalBindT (someInst sysTh0) keepVarBindings
///   conjoinSystem sysTh
///   return names
///   where keepVarBindings = M.fromList (map (\v -> (v,v)) (frees goal))
/// ```
///
/// And `matchToGoal` (Sources.hs:268-318):
///
/// ```haskell
/// matchToGoal ctxt th0 goalTerm =
///   case (goalTerm, get cdGoal th) of
///     (ActionG iTerm faTerm, ActionG iPat faPat) ->
///       case doMatch (faTerm `matchFact` faPat <> iTerm `matchLVar` iPat) of
///         []      -> Nothing
///         subst:_ -> Just $ snd $ refineSource ctxt
///                                   (refineSubst subst) (set cdGoal goalTerm th)
///   where
///     th = (`evalFresh` avoid goalTerm) . rename $ th0
///     refineSubst subst = solveSubstEqs SplitNow subst >> substSystem
/// ```
///
/// We pass the whole `src: &Source` so we can match the live goal
/// against the abstract `cdGoal` (`src.goal`) — NOT against a
/// case-specific action.  Matching against the abstract `cdGoal`
/// is what Haskell does and it is what avoids conflating the case's
/// rule-internal vars (e.g. C_1's `~nc:Fresh`) with the live goal's
/// fresh vars (e.g. `~ltkA:Fresh`).  The match-subst only binds
/// abstract pattern vars (`t:Fresh:1` and `i:Node:0` from precompute),
/// which after the case's precompute-time `subst_system` are no
/// longer present as free vars in `case_sys`.  Without case-internal
/// conflation, `someInst keepVarBindings` then freshens the
/// rule-internal vars to a globally-unique idx range so the grafted
/// Fresh-rule and live's Fresh-rule remain distinct producers.
///
/// Steps (one per Haskell line above):
///
/// A.1 (`rename th0` in `matchToGoal`):
///     Rename the source — both `src.goal` (the abstract `cdGoal`) and
///     `case_sys` — by shifting every var's idx by `avoid goalTerm`
///     = max(free var idx of (live_node, fa_live)) + 1.  This is a
///     LOCAL counter: it does NOT advance any global state.
///
/// A.2 (`doMatch ... <> ...` in `matchToGoal`):
///     One-way Maude match: pattern (renamed abstract `cdGoal`) →
///     subject (live `(iTerm, faTerm)`).  Returns substitution
///     binding renamed pattern vars to live values.  We use a
///     no-AC path first; on `NeedsAC`, fall back to Maude.
///
/// A.3 (`refineSubst subst` in `matchToGoal`):
///     `solveSubstEqs SplitNow subst >> substSystem` on the renamed
///     case.  Adds `t:Fresh:1 = ~ltkA` (and node-id eq) to the
///     case's eq-store, then propagates.  Since the abstract vars
///     are not free in the case_sys after precompute, this has
///     primarily an effect on the case's stored eq-store; node/edge
///     terms stay unchanged.
///
/// B (`markGoalAsSolved "precomputed" goal` in `_applySource`):
///     Mark the live goal as solved.  We do this on the LIVE
///     reduction state, just before conjoinSystem (Haskell does
///     mark-then-conjoin in `_applySource`).
///
/// D (`evalBindT (someInst sysTh0) keepVarBindings`):
///     Freshen every var in the case EXCEPT those in `frees goal`
///     (= `live_node` + free vars of `fa_live`).  This is the
///     step that draws from the OUTER `MonadFresh` counter — we
///     use the MaudeHandle's `Arc<AtomicU64>` global counter via
///     `reserve_idxs`, mirroring Haskell's `FreshT m` instance.
///
/// E (`conjoinSystem sysTh`):
///     Use `Reduction::conjoin_system` which mirrors Haskell's
///     `conjoinSystem` step-by-step (joinSets + insertLast +
///     insertLess + insertGoalStatus + insertFormula + setNodes +
///     addDisj + conjoinSubtermStores + solveSubstEqs +
///     substSystem).
fn apply_source_case_action(
    ctx: &crate::constraint::solver::context::ProofContext,
    live_sys: &System,
    src: &Source,
    case_sys: &System,
    live_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
) -> Option<(System, crate::fact::LNFact)> {
    use crate::constraint::solver::reduction::{
        Reduction, SolveOutcome, SplitStrategy, bounds_max,
    };
    use tamarin_term::lterm::HasFrees;

    // Task #166 diagnostic: structured drop-reason tracing.  Set
    // TAM_DBG_APPLY_SOURCE=1 to log every drop site with case name +
    // reason.  Use this to track WHICH source-case drops at WHICH
    // step (match-fail, refineSubst-fail, conjoin-fail, etc.).
    let dbg_apply = std::env::var("TAM_DBG_APPLY_SOURCE").is_ok();
    let case_label = src.cases.iter()
        .find_map(|(n, sys)|
            if std::ptr::eq(sys as *const _, case_sys as *const _) {
                Some(n.clone())
            } else { None })
        .unwrap_or_default();
    let dbg = |reason: &str| {
        if dbg_apply {
            eprintln!("[applySource] DROP case={} reason={} live_node={:?} fa_live.tag={:?}",
                case_label, reason, live_node, fa_live.tag);
        }
    };

    // Pull the abstract `cdGoal` (NodeId + LNFact) out of `src`.
    let (abstract_node_orig, abstract_action_orig) = match &src.goal {
        crate::constraint::constraints::Goal::Action(n, fa) => (n.clone(), fa.clone()),
        _ => { dbg("src-goal-not-Action"); return None; },
    };
    if fa_live.tag != abstract_action_orig.tag
        || fa_live.terms.len() != abstract_action_orig.terms.len()
    {
        dbg("tag/arity-mismatch");
        return None;
    }

    let live_goal_for_trace = crate::constraint::constraints::Goal::Action(
        live_node.clone(), fa_live.clone());
    crate::state_trace::emit("applySource_in", Some(&live_goal_for_trace), live_sys);

    // ---------------------------------------------------------------
    // A.1 — `rename th0` in matchToGoal.
    //
    // Shift = avoid goalTerm = max free-var idx of (live_node, fa_live)
    // + 1.  Local counter only.  Renames the WHOLE source coherently
    // (cdGoal + case_sys share the same shift base).
    // ---------------------------------------------------------------
    let mut goal_max: u64 = 0;
    {
        let mut visit = |v: &tamarin_term::lterm::LVar| {
            if v.idx > goal_max { goal_max = v.idx; }
        };
        live_node.for_each_free(&mut visit);
        fa_live.for_each_free(&mut visit);
    }
    let rename_shift = goal_max.saturating_add(1);
    let shift_lvar = |v: &tamarin_term::lterm::LVar| {
        let mut v2 = v.clone();
        v2.idx = v2.idx.saturating_add(rename_shift);
        v2
    };
    let renamed_abstract_node = shift_lvar(&abstract_node_orig);
    let renamed_abstract_action = abstract_action_orig
        .map_free(&mut |v| shift_lvar(&v));
    let empty_keep: std::collections::BTreeSet<tamarin_term::lterm::LVar>
        = std::collections::BTreeSet::new();
    let renamed_case = freshen_system_keep_with_shift(
        case_sys, rename_shift, &empty_keep);

    // ---------------------------------------------------------------
    // A.2 — `doMatch (faTerm `matchFact` faPat <> iTerm `matchLVar` iPat)`.
    //
    // DelayedMatches is `Vec<(term, pattern)>` (matching Haskell's
    // `matchFact t p` = subject t, pattern p).  We match the LIVE
    // goal's terms against the RENAMED ABSTRACT pattern.  Plus the
    // node-id pattern→subject pair `(live_node, renamed_abstract_node)`.
    // ---------------------------------------------------------------
    let mut pairs: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)>
        = Vec::with_capacity(fa_live.terms.len() + 1);
    for (lt, pt) in fa_live.terms.iter().zip(renamed_abstract_action.terms.iter()) {
        pairs.push((lt.clone(), pt.clone()));
    }
    pairs.push((
        tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(live_node.clone())),
        tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(renamed_abstract_node.clone())),
    ));

    // Try no-AC match first, fall back to Maude on NeedsAC.
    let match_pairs: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = {
        let problem = tamarin_term::rewriting::Match::DelayedMatches(pairs.clone());
        match tamarin_term::unification::solve_match_lterm_no_ac::<
            tamarin_term::lterm::Name, _>(
            &tamarin_term::lterm::sort_of_name, problem,
        ) {
            Some(s) => s.to_list(),
            None => {
                let match_eqs: Vec<_> = pairs.into_iter()
                    .map(|(t, p)| tamarin_term::rewriting::Equal { lhs: t, rhs: p })
                    .collect();
                let substs_res = ctx.maude.match_eqs(&match_eqs);
                let mut substs = match substs_res {
                    Ok(s) => s,
                    Err(_) => { dbg("maude-match-err"); return None; },
                };
                if substs.is_empty() { dbg("match-empty"); return None; }
                substs.swap_remove(0)
            }
        }
    };

    // ---------------------------------------------------------------
    // A.3 — `refineSubst subst = solveSubstEqs SplitNow subst >> substSystem`.
    //
    // Build `Equal (varTerm v) t` for each (v, t) in the match-subst,
    // then run them through the renamed case's Reduction.
    // ---------------------------------------------------------------
    let mut refined = Reduction::new(ctx, renamed_case);
    let term_eqs: Vec<_> = match_pairs.into_iter()
        .map(|(v, t)| tamarin_term::rewriting::Equal {
            lhs: tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(v)),
            rhs: t,
        })
        .collect();
    if !term_eqs.is_empty() {
        let r = refined.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs);
        if matches!(r, Err(_) | Ok(SolveOutcome::Contradictory)) {
            dbg("refineSubst-contradictory");
            return None;
        }
    }
    refined.subst_system();
    if refined.sys.eq_store.is_false() {
        dbg("post-subst-eq-store-false");
        return None;
    }
    // Mirror Haskell `refineSource ctxt (refineSubst subst) (set cdGoal goalTerm th)`
    // (Sources.hs:285,290): after refineSubst, restrict the case's
    // eq-store to `frees (cdGoal th) = frees goalTerm` — the LIVE
    // goal's free vars (since `set cdGoal goalTerm` was applied).
    // Drops any leftover abstract/rule-internal bindings introduced
    // during precompute and renamed via Step A.1.
    let runtime_stable: std::collections::BTreeSet<tamarin_term::lterm::LVar> = {
        let mut s = std::collections::BTreeSet::new();
        s.insert(live_node.clone());
        fa_live.for_each_free(&mut |v: &tamarin_term::lterm::LVar| {
            s.insert(v.clone());
        });
        s
    };
    restrict_eq_store_to_stable_vars(&mut refined.sys, &runtime_stable);
    crate::state_trace::emit(
        "applySource_refined", Some(&live_goal_for_trace), &refined.sys);
    let refined_case = refined.sys;

    // ---------------------------------------------------------------
    // D — `evalBindT (someInst sysTh0) keepVarBindings`.
    //
    // keepVarBindings = M.fromList (map (\v -> (v,v)) (frees goal)).
    // For `ActionG iTerm faTerm`, `frees goal = [iTerm] ++ frees faTerm`
    // = live_node + free vars of fa_live.  Vars in this set are kept;
    // all others are freshened.
    //
    // Haskell's `someInst` draws from the ambient `MonadFresh` (in
    // `_applySource` this is the live Reduction's `sNextVarIdx`).  We
    // use the MaudeHandle's global `Arc<AtomicU64>` counter via
    // `reserve_idxs(post_refine_max + 1)` so the freshen base is
    // unique across all applySource calls in this proof session.
    // Mirrors `freshIdents (succ (maxIdx - minIdx))` in `rename`.
    // ---------------------------------------------------------------
    let mut keep_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar>
        = std::collections::BTreeSet::new();
    keep_vars.insert(live_node.clone());
    fa_live.for_each_free(&mut |v: &tamarin_term::lterm::LVar| {
        keep_vars.insert(v.clone());
    });
    let post_refine_max = bounds_max(&refined_case);
    ctx.maude.ensure_above(post_refine_max);
    let shift_base = ctx.maude.reserve_idxs(post_refine_max.saturating_add(1));
    let freshened_case = freshen_system_keep_with_shift(
        &refined_case, shift_base, &keep_vars);

    // Recover the live action fact for return: it should be the KU
    // action at `live_node` in the freshened case (the abstract node
    // was substituted to live_node by Step A.3's subst_system).  If
    // not present (e.g. node-id subst didn't propagate), fall back to
    // any KU action in the case — `conjoin_system`'s setNodes will
    // merge it onto the right node.
    let live_action_opt = freshened_case.nodes.iter()
        .find(|(id, _)| id == live_node)
        .and_then(|(_, r)| r.actions.iter()
            .find(|a| a.tag == crate::fact::FactTag::Ku).cloned())
        .or_else(|| {
            freshened_case.nodes.iter().find_map(|(_, r)|
                r.actions.iter().find(|a| a.tag == crate::fact::FactTag::Ku).cloned())
        });
    let live_action = match live_action_opt {
        Some(la) => la,
        None => { dbg("no-KU-action-in-freshened-case"); return None; },
    };

    // ---------------------------------------------------------------
    // B — `markGoalAsSolved "precomputed" goal`.
    // E — `conjoinSystem sysTh`.
    // ---------------------------------------------------------------
    let mut r = Reduction::new(ctx, live_sys.clone());
    let live_goal = crate::constraint::constraints::Goal::Action(
        live_node.clone(), fa_live.clone());
    if let Some(slot) = r.sys.goals.iter_mut().find(|(g, _)| g == &live_goal) {
        slot.1.solved = true;
    }
    crate::state_trace::emit(
        "applySource_pre_conjoin", Some(&live_goal_for_trace), &freshened_case);
    let res = r.conjoin_system(&freshened_case);
    if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
        dbg(match res {
            Err(_) => "conjoin-err",
            Ok(SolveOutcome::Contradictory) => "conjoin-contradictory",
            _ => "conjoin-other",
        });
        crate::state_trace::emit(
            "applySource_drop", Some(&live_goal_for_trace), &r.sys);
        return None;
    }

    // ---------------------------------------------------------------
    // F — Close trivial chains via direct-edge unification.
    //
    // Haskell's precompute `solveAllSafeGoals` closes chains during
    // source-case saturation, so the case_sys merged here already has
    // chain edges (in `sEdges`) and their term equations (in
    // `sSubst`).  Our `close_chains_dfs` defers msg-var KD chains
    // (per the openGoals filter), so they remain as `Goal::Chain` in
    // the precomputed case.  After `refineSubst` substitutes the
    // abstract source pattern var with a concrete (e.g. Fresh-sorted)
    // live term, those chains become closeable via direct edge.  Run
    // that closure here so callers don't have to take an explicit
    // `case irecv` step (which Haskell never does).
    //
    // Conservative: only try Branch 1 (direct edge) — never extend
    // via destructor.  If Branch 1 fails or splits, leave the chain
    // as-is.
    close_trivial_chains_in_graft(&mut r);

    crate::state_trace::emit(
        "applySource_out", Some(&live_goal_for_trace), &r.sys);
    Some((r.sys, live_action))
}

/// Haskell-faithful `applySource` for Premise goals.  Mirrors
/// `apply_source_case_action` step-for-step, with the Premise-specific
/// edge rewire from `matchToGoal` (Sources.hs:283).
///
/// Includes a defensive edge-fact `chain_eqs` pass after `conjoinSystem`
/// (step G) to re-unify edge facts.  Rust saturate doesn't always emit
/// fully-edge-consistent `case_sys` (task #249); until that lands, this
/// pass compensates.
fn apply_source_case_premise(
    ctx: &crate::constraint::solver::context::ProofContext,
    live_sys: &System,
    src: &Source,
    case_sys: &System,
    live_node: &crate::constraint::constraints::NodeId,
    live_prem_idx: crate::rule::PremIdx,
    fa_live: &crate::fact::LNFact,
) -> Option<System> {
    use crate::constraint::solver::reduction::{
        Reduction, SolveOutcome, SplitStrategy, bounds_max,
    };
    use tamarin_term::lterm::HasFrees;

    let dbg_apply = std::env::var("TAM_DBG_APPLY_SOURCE").is_ok();
    let case_label = src.cases.iter()
        .find_map(|(n, sys)|
            if std::ptr::eq(sys as *const _, case_sys as *const _) {
                Some(n.clone())
            } else { None })
        .unwrap_or_default();
    let dbg = |reason: &str| {
        if dbg_apply {
            eprintln!("[applySource_prem] DROP case={} reason={} live_node={:?} fa_live.tag={:?}",
                case_label, reason, live_node, fa_live.tag);
        }
    };

    let (abstract_node_orig, abstract_prem_idx_orig, abstract_prem_fact_orig) =
        match &src.goal {
            crate::constraint::constraints::Goal::Premise((n, p), fa) =>
                (n.clone(), *p, fa.clone()),
            _ => { dbg("src-goal-not-Premise"); return None; },
        };
    if fa_live.tag != abstract_prem_fact_orig.tag
        || fa_live.terms.len() != abstract_prem_fact_orig.terms.len()
    {
        dbg("tag/arity-mismatch");
        return None;
    }

    let live_goal_for_trace = crate::constraint::constraints::Goal::Premise(
        (live_node.clone(), live_prem_idx), fa_live.clone());
    crate::state_trace::emit("applySource_prem_in", Some(&live_goal_for_trace), live_sys);

    // A.1 — rename th0 in matchToGoal.
    let mut goal_max: u64 = 0;
    {
        let mut visit = |v: &tamarin_term::lterm::LVar| {
            if v.idx > goal_max { goal_max = v.idx; }
        };
        live_node.for_each_free(&mut visit);
        fa_live.for_each_free(&mut visit);
    }
    let rename_shift = goal_max.saturating_add(1);
    let shift_lvar = |v: &tamarin_term::lterm::LVar| {
        let mut v2 = v.clone();
        v2.idx = v2.idx.saturating_add(rename_shift);
        v2
    };
    let renamed_abstract_node = shift_lvar(&abstract_node_orig);
    let renamed_abstract_fact = abstract_prem_fact_orig
        .map_free(&mut |v| shift_lvar(&v));
    let empty_keep: std::collections::BTreeSet<tamarin_term::lterm::LVar>
        = std::collections::BTreeSet::new();
    let renamed_case = freshen_system_keep_with_shift(
        case_sys, rename_shift, &empty_keep);

    // A.2 — match (faTerm matchFact faPat) <> (iTerm matchLVar iPat).
    let mut pairs: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)>
        = Vec::with_capacity(fa_live.terms.len() + 1);
    for (lt, pt) in fa_live.terms.iter().zip(renamed_abstract_fact.terms.iter()) {
        pairs.push((lt.clone(), pt.clone()));
    }
    pairs.push((
        tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(live_node.clone())),
        tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(renamed_abstract_node.clone())),
    ));
    let match_pairs: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = {
        let problem = tamarin_term::rewriting::Match::DelayedMatches(pairs.clone());
        match tamarin_term::unification::solve_match_lterm_no_ac::<
            tamarin_term::lterm::Name, _>(
            &tamarin_term::lterm::sort_of_name, problem,
        ) {
            Some(s) => s.to_list(),
            None => {
                let match_eqs: Vec<_> = pairs.into_iter()
                    .map(|(t, p)| tamarin_term::rewriting::Equal { lhs: t, rhs: p })
                    .collect();
                let substs_res = ctx.maude.match_eqs(&match_eqs);
                let mut substs = match substs_res {
                    Ok(s) => s,
                    Err(_) => { dbg("maude-match-err"); return None; },
                };
                if substs.is_empty() { dbg("match-empty"); return None; }
                substs.swap_remove(0)
            }
        }
    };

    // A.2.5 (Premise-specific) — substNodePrem pPat (iPat, premIdxTerm).
    // Rewrite edges in the case whose tgt is the renamed pattern
    // premise so they point at the LIVE premise idx.  Same for any
    // Premise goal at that position.
    let mut renamed_case = renamed_case;
    let pat_prem: (tamarin_term::lterm::LVar, crate::rule::PremIdx) =
        (renamed_abstract_node.clone(), abstract_prem_idx_orig);
    let new_prem: (tamarin_term::lterm::LVar, crate::rule::PremIdx) =
        (renamed_abstract_node.clone(), live_prem_idx);
    for e in renamed_case.edges.iter_mut() {
        if e.tgt == pat_prem {
            e.tgt = new_prem.clone();
        }
    }
    for (g, _) in renamed_case.goals.iter_mut() {
        if let crate::constraint::constraints::Goal::Premise(p, _) = g {
            if *p == pat_prem {
                *p = new_prem.clone();
            }
        }
    }

    // A.3 — refineSubst: solveSubstEqs SplitNow subst >> substSystem.
    let mut refined = Reduction::new(ctx, renamed_case);
    let term_eqs: Vec<_> = match_pairs.into_iter()
        .map(|(v, t)| tamarin_term::rewriting::Equal {
            lhs: tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(v)),
            rhs: t,
        })
        .collect();
    if !term_eqs.is_empty() {
        let r = refined.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs);
        if matches!(r, Err(_) | Ok(SolveOutcome::Contradictory)) {
            dbg("refineSubst-contradictory");
            return None;
        }
    }
    refined.subst_system();
    if refined.sys.eq_store.is_false() {
        dbg("post-subst-eq-store-false");
        return None;
    }
    let runtime_stable: std::collections::BTreeSet<tamarin_term::lterm::LVar> = {
        let mut s = std::collections::BTreeSet::new();
        s.insert(live_node.clone());
        fa_live.for_each_free(&mut |v: &tamarin_term::lterm::LVar| {
            s.insert(v.clone());
        });
        s
    };
    restrict_eq_store_to_stable_vars(&mut refined.sys, &runtime_stable);
    crate::state_trace::emit(
        "applySource_prem_refined", Some(&live_goal_for_trace), &refined.sys);
    let refined_case = refined.sys;

    // D — someInst keepVarBindings.
    let mut keep_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar>
        = std::collections::BTreeSet::new();
    keep_vars.insert(live_node.clone());
    fa_live.for_each_free(&mut |v: &tamarin_term::lterm::LVar| {
        keep_vars.insert(v.clone());
    });
    let post_refine_max = bounds_max(&refined_case);
    ctx.maude.ensure_above(post_refine_max);
    let shift_base = ctx.maude.reserve_idxs(post_refine_max.saturating_add(1));
    let freshened_case = freshen_system_keep_with_shift(
        &refined_case, shift_base, &keep_vars);

    // B+E — markGoalAsSolved + conjoinSystem.
    let mut r = Reduction::new(ctx, live_sys.clone());
    let live_goal = crate::constraint::constraints::Goal::Premise(
        (live_node.clone(), live_prem_idx), fa_live.clone());
    if let Some(slot) = r.sys.goals.iter_mut().find(|(g, _)| g == &live_goal) {
        slot.1.solved = true;
    }
    crate::state_trace::emit(
        "applySource_prem_pre_conjoin", Some(&live_goal_for_trace), &freshened_case);
    let res = r.conjoin_system(&freshened_case);
    if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
        dbg(match res {
            Err(_) => "conjoin-err",
            Ok(SolveOutcome::Contradictory) => "conjoin-contradictory",
            _ => "conjoin-other",
        });
        crate::state_trace::emit(
            "applySource_prem_drop", Some(&live_goal_for_trace), &r.sys);
        return None;
    }

    // F — close trivial chains.
    close_trivial_chains_in_graft(&mut r);

    // G — re-filter conjoined variant SplitGs against the now-extended
    // free subst.  Mirrors Haskell's `applyEqStore` semantics: when new
    // bindings enter eq_store.subst (here, via the conjoin's case_subst_eqs),
    // existing SplitG variants whose bindings conflict are dropped.
    //
    // Concrete TESLA::authentic example: Receiver0b's variant [0] has
    // `z → verify(...)` and variant [1] has `z → true`.  When the case is
    // grafted via apply_source_case_premise → conjoin_system, z gets
    // unified with `true` (from Receiver0b_check's literal `true` slot)
    // via the case's edges.  At that moment, applyEqStore should drop
    // variant [0] because `verify(...) ≠ true`.  Without this G step,
    // both variants survive, the search forks at the SplitG, picks
    // variant [0]'s untyped-signature path, and reaches a spurious Solved.
    if !r.sys.eq_store.conj.is_empty() && !r.sys.eq_store.subst.is_empty() {
        let empty_subst = tamarin_term::subst::Subst::empty();
        let _ = r.sys.eq_store.apply_eq_store(&ctx.maude, &empty_subst);
        let needs_fold = r.sys.eq_store.conj.iter().any(|d| d.substs.len() == 1);
        if needs_fold {
            use tamarin_term::lterm::HasFrees;
            let mut sys_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar>
                = std::collections::BTreeSet::new();
            let mut visit = |v: &tamarin_term::lterm::LVar| { sys_vars.insert(v.clone()); };
            for (id, rule) in &r.sys.nodes {
                id.for_each_free(&mut visit);
                rule.for_each_free(&mut visit);
            }
            for e in &r.sys.edges {
                e.src.0.for_each_free(&mut visit);
                e.tgt.0.for_each_free(&mut visit);
            }
            for l in &r.sys.less_atoms {
                l.smaller.for_each_free(&mut visit);
                l.larger.for_each_free(&mut visit);
            }
            if let Some(la) = &r.sys.last_atom { la.for_each_free(&mut visit); }
            let maude = ctx.maude.clone();
            let store = std::mem::take(&mut r.sys.eq_store);
            r.sys.eq_store = store.simp_with_fresh_avoiding(
                |_, _| false,
                |n| maude.reserve_idxs(n),
                &sys_vars,
            );
            r.subst_system();
        }
    }

    if src.incomplete { r.sys.used_incomplete_source = true; }
    crate::state_trace::emit(
        "applySource_prem_out", Some(&live_goal_for_trace), &r.sys);
    Some(r.sys)
}

/// True when `t` is a Msg-sorted free variable.  Used by
/// `close_trivial_chains_in_graft` to match Haskell's
/// `chainToEquality` filter on msg-var KD chains.
fn is_msg_var_for_chain_filter(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    matches!(t, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg)
}

/// Walk open `Goal::Chain` goals in `r.sys` and close each via the
/// direct-edge branch of `solve_chain_goal` when the endpoints' fact
/// tags + arity match (no destructor extension).  Mirrors the
/// post-saturate state Haskell's precompute produces for source cases.
/// Stops on the first chain where direct-edge unification fails or
/// is contradictory — the chain stays as a `Goal::Chain` and gets
/// handled at search time, exactly as before.
fn close_trivial_chains_in_graft(
    r: &mut crate::constraint::solver::reduction::Reduction,
) {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{SolveOutcome, SplitStrategy};

    loop {
        // Find one open Chain goal whose endpoints are tag+arity
        // compatible AND not a forbidden edge.  Snapshot the goal so
        // we can release the borrow on `r.sys` before mutating.
        let candidate: Option<(
            crate::constraint::constraints::NodeConc,
            crate::constraint::constraints::NodePrem,
            crate::fact::LNFact,
            crate::fact::LNFact,
        )> = r.sys.goals.iter().find_map(|(g, st)| {
            if st.solved || st.looping { return None; }
            let Goal::Chain(c, p) = g else { return None };
            let c_rule = r.sys.nodes.iter().find(|(id, _)| id == &c.0).map(|(_, ru)| ru)?;
            let p_rule = r.sys.nodes.iter().find(|(id, _)| id == &p.0).map(|(_, ru)| ru)?;
            let fa_conc = c_rule.conclusions.get(c.1.0)?.clone();
            let fa_prem = p_rule.premises.get(p.1.0)?.clone();
            if fa_conc.tag != fa_prem.tag
                || fa_conc.terms.len() != fa_prem.terms.len()
            {
                return None;
            }
            // Haskell-faithful: msg-var KD chains are auto-handled via
            // `chainToEquality` (Goals.hs:92-100) — they're filtered
            // OUT of `openGoals` and `solveAllSafeGoals` doesn't close
            // them.  Mirroring that here prevents over-eager closure
            // that breaks SplitG resolution downstream (NSPK3/NSLPK3
            // R_1 + I_2 case regressions).
            if fa_conc.tag == crate::fact::FactTag::Kd {
                if let Some(t) = fa_conc.terms.first() {
                    if is_msg_var_for_chain_filter(t) {
                        return None;
                    }
                }
            }
            Some((c.clone(), p.clone(), fa_conc, fa_prem))
        });
        let Some((c, p, fa_conc, fa_prem)) = candidate else { break };

        // Snapshot system; if direct-edge unification contradicts,
        // restore and stop trying.
        let snapshot = r.sys.clone();
        r.sys.add_edge(crate::constraint::constraints::Edge {
            src: c.clone(), tgt: p.clone(),
        });
        let res = r.solve_fact_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal { lhs: fa_conc, rhs: fa_prem }],
        );
        match res {
            Err(_) | Ok(SolveOutcome::Contradictory) => {
                // Direct-edge closure not possible.  Restore and bail
                // — the chain stays open for the search layer to
                // handle (Branch 2 destructor or Disj-case).
                r.sys = snapshot;
                break;
            }
            Ok(_) => {
                // Mark the chain solved.
                let chain_goal = Goal::Chain(c, p);
                if let Some(slot) = r.sys.goals.iter_mut()
                    .find(|(g, _)| g == &chain_goal)
                {
                    slot.1.solved = true;
                }
                // Continue — additional chains may now be closeable
                // after the eq-store propagation.
            }
        }
    }
}

/// Graft a precomputed Action-source case into `live_sys`, mapping
/// the case's `abstract_node` (which produces the KU action) to the
/// live goal's `live_node`.  Unlike `graft_case_into`, no premise
/// edge needs bridging — the action node *is* the consumer.
fn graft_case_into_action(
    live_sys: &System,
    case_sys: &System,
    abstract_node: &crate::constraint::constraints::NodeId,
    live_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
) -> Option<System> {
    let mut out = live_sys.clone();
    let rename_node = |n: &crate::constraint::constraints::NodeId| {
        if n == abstract_node { live_node.clone() } else { n.clone() }
    };
    for (id, rule) in &case_sys.nodes {
        let new_id = rename_node(id);
        if !out.nodes.iter().any(|(n, _)| n == &new_id) {
            out.add_node(new_id, rule.clone());
        }
    }
    for e in &case_sys.edges {
        let new_src_node = rename_node(&e.src.0);
        let new_tgt_node = rename_node(&e.tgt.0);
        out.add_edge(crate::constraint::constraints::Edge {
            src: (new_src_node, e.src.1),
            tgt: (new_tgt_node, e.tgt.1),
        });
    }
    for l in &case_sys.less_atoms {
        out.add_less(crate::constraint::constraints::LessAtom::new(
            rename_node(&l.smaller),
            rename_node(&l.larger),
            l.reason,
        ));
    }
    // Mirrors Haskell `conjoinSystem`: preserve goal status when merging.
    // See graft_case_into for full rationale — the case's pre-solved
    // goals must stay marked solved in the live system, or downstream
    // search re-picks them as `case Register_pk` for already-resolved
    // premises (the KAS2_eCK case_1.Resp_2 divergence).
    for (g, st) in &case_sys.goals {
        let renamed_goal = match g {
            crate::constraint::constraints::Goal::Action(n, _fa)
                if n == abstract_node => continue,
            crate::constraint::constraints::Goal::Action(n, fa) =>
                crate::constraint::constraints::Goal::Action(rename_node(n), fa.clone()),
            crate::constraint::constraints::Goal::Premise(p, fa) =>
                crate::constraint::constraints::Goal::Premise(
                    (rename_node(&p.0), p.1), fa.clone()),
            other => other.clone(),
        };
        if !out.goals.iter().any(|(existing, _)| existing == &renamed_goal) {
            out.goals.push((renamed_goal, st.clone()));
        }
    }
    let live_goal = crate::constraint::constraints::Goal::Action(
        live_node.clone(), fa_live.clone());
    if let Some(slot) = out.goals.iter_mut().find(|(g, _)| g == &live_goal) {
        slot.1.solved = true;
    }
    // Merge the case's eq-store substitutions into the live system.
    //
    // CRITICAL for typing refinement: the case carries precompute-
    // time bindings like `x#3 → senc(<chain_sec, chain_pub>, chain_k)`
    // that bind the abstract KU pattern var to the actual senc
    // structure built by the chain.  Without merging these, when
    // `solve_action_goal` later runs `solve_fact_eqs(case_action,
    // fa_live)` to unify the abstract action with the live goal,
    // the equation collapses to `x#3 → senc(<sec#4, ~mw#5>, ~mw#13)`
    // — but the case-INTERNAL chain vars (chain_sec etc.) never get
    // connected to the live vars.  Out_Initiator's terms still
    // reference chain_sec, so impl_formulas's match against
    // `Out_Initiator(senc(<sec#4, ~mw#5>, ~mw#13))` fails, the
    // typing universal doesn't fire, and the typing-violating case
    // survives → false counterexample.
    //
    // With the merge: both bindings are present.  When solve_fact_eqs
    // runs against fa_live, Maude composes them, yielding
    // `chain_sec → sec#4` etc.  subst_system then rewrites
    // Out_Initiator's terms, the universal fires, and the case is
    // pruned via contradiction.
    let mut merged_pairs: Vec<_> = out.eq_store.subst.to_list();
    let existing: std::collections::HashSet<_> = merged_pairs.iter()
        .map(|(v, _)| v.clone())
        .collect();
    for (lv, lt) in case_sys.eq_store.subst.to_list() {
        let new_lv = if &lv == abstract_node { live_node.clone() } else { lv };
        if !existing.contains(&new_lv) {
            merged_pairs.push((new_lv, lt));
        }
    }
    out.eq_store.subst = tamarin_term::subst::Subst::from_list(merged_pairs);
    Some(out)
}

/// Direct port of Haskell `removeRedundantCases` (Sources.hs:236-260)
/// for the **non-BP/MSet branch** — Haskell short-circuits:
///
/// ```haskell
/// removeRedundantCases ctxt stableVars getSys cases0 =
///     if enableBP msig || enableMSet msig then cases else cases0
/// ```
///
/// Without bilinear-pairing or multiset signatures, no AC-redundant
/// cases can arise from `runReduction`, so the function is the identity.
/// Our refineSource already dedups by canonical-system string and our
/// `SolveGoal` arm dedups by case-name suffix, which together cover
/// the BP/MSet branch's intent for the corpus we exercise.  No live
/// callers today; left as a hook for when BP/MSet protocols enter the
/// corpus and Haskell-equivalent system-normed dedup becomes needed.
pub fn remove_redundant_cases<T: Clone>(cases: Vec<T>) -> Vec<T> { cases }

/// Saturate-time variant of `fanout_variant_splits`: fan out the first
/// small (size ≤ SMALL) variant SplitG goal in a saturated source-case
/// into per-arm sub-cases.  Mirrors Haskell `someRuleACInst` whose
/// returned `RuleACConstrs` get resolved by `solveDisjunction` BEFORE
/// the saturated case is stored — so Haskell's saturate-output cases
/// have the variant-narrowed form (e.g.
/// `In(aenc(<'1', <$A, ~k>>, pk(~ltkS)))` where `~k:Fresh`), no
/// surviving SplitG, and downstream choices see the variant-narrowed
/// terms.
///
/// Variant narrowing matters for any case with downstream goal-ranking
/// choices:
///   - open Chain → destructor chains see Fresh-typed t_start at
///     destructor outputs (essential for `hasImpossibleChain`'s
///     `pcTrueSubterm` rootSym dispatch — Contradictions.hs:258).
///     Without this, t_start is `x_0:Msg` and `possibleRootSyms`
///     returns `Nothing`; JCS12::typing_assertion shows `solve`
///     where Haskell shows `by contradiction /* impossible chain */`.
///   - open KU action → variant subst changes the picked constructor
///     source at runtime (StatVerif Resolve1: pcsig2 narrowed to
///     pcs(...) flips c_pcs → c_sign).
///
/// Constraints:
///   - Variant SplitG must be ≤ SMALL (=6).  Larger SplitGs stay as
///     runtime goals (smartRanking only ranks small SplitGs).
///   - Canonical-system dedup collapses redundant arms.
///
/// Returns `None` when the case has no eligible small variant SplitG
/// (caller keeps the original case unchanged).  Returns `Some(cases)`
/// with one entry per surviving variant arm (empty Vec = all arms
/// contradicted, caller drops the case).
fn saturate_fanout_variant_splits(
    ctx: &crate::constraint::solver::context::ProofContext,
    sys: crate::constraint::system::System,
    case_label: &str,
) -> Option<Vec<(String, crate::constraint::system::System)>> {
    use crate::constraint::solver::reduction::{Reduction, GoalCases};
    use crate::constraint::constraints::Goal;
    const SMALL: usize = 6;
    // No saturate-time gate: Haskell's `someRuleACInst` always fans out
    // variants via `solveDisjunction` over `RuleACConstrs`. Variant
    // narrowing matters for any case with downstream goal-ranking choices —
    //   - open Chain → `pcTrueSubterm` rootSym dispatch (JCS12);
    //   - open KU action → constructor-source selection (StatVerif:
    //     pcsig2 narrowed to pcs(...) changes c_pcs → c_sign at runtime).
    // Canonical-system dedup collapses redundant arms.
    let small_split: Option<crate::tools::equation_store::SplitId> =
        sys.goals.iter().find_map(|(g, st)| {
            if st.solved || st.looping { return None; }
            let Goal::Split(id) = g else { return None };
            let sz = sys.eq_store.split_size(*id)?;
            if sz > 1 && sz <= SMALL { Some(*id) } else { None }
        });
    let split_id = small_split?;
    set_precompute_mode(true);
    let mut red = Reduction::new(ctx, sys);
    let outcome = red.solve_split_goal(split_id);
    let raw_cases: Vec<crate::constraint::system::System> = match outcome {
        GoalCases::Cases(cases) if !cases.is_empty() => {
            cases.into_iter().map(|(_, sub_sys)| sub_sys).collect()
        }
        GoalCases::Linear | GoalCases::LinearNamed(_) => {
            vec![red.sys]
        }
        GoalCases::Contradictory | GoalCases::Cases(_) => {
            set_precompute_mode(false);
            return Some(Vec::new());
        }
    };
    set_precompute_mode(false);
    // Dedup variant fanout by canonical-system structural form, same
    // approach as `fanout_variant_splits` (runtime apply).  Two arms
    // may differ only in eq_store witness names that don't affect
    // downstream proof.
    //
    // Haskell-faithful `removeRedundantCases` gate (Sources.hs:240):
    // BP/MSet only.  See site at refineSource.
    let dedup_enabled = {
        let s = ctx.maude.maude_sig();
        s.enable_bp || s.enable_mset
    };
    let mut seen_keys: std::collections::BTreeSet<String> =
        std::collections::BTreeSet::new();
    let mut out: Vec<(String, crate::constraint::system::System)> = Vec::new();
    for sub_sys in raw_cases {
        if dedup_enabled {
            let key = canonicalise_system(&sub_sys);
            if !seen_keys.insert(key) { continue; }
        }
        {
            out.push((case_label.to_string(), sub_sys));
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_parameters_match_haskell() {
        let p = IntegerParameters::default();
        assert_eq!(p.open_chains_limit, 10);
        assert_eq!(p.saturation_limit, 5);
        assert!(!p.show_saturation_steps);
    }

    #[test]
    fn empty_system_has_no_chains() {
        let s = System::empty();
        assert_eq!(unsolved_chain_constraints(&s), 0);
    }

    #[test]
    fn chain_goal_counted() {
        use crate::constraint::constraints::{Goal, NodeId};
        use crate::rule::{ConcIdx, PremIdx};
        use tamarin_term::lterm::{LSort, LVar};
        let mut s = System::empty();
        let n: NodeId = LVar::new("i", LSort::Node, 0);
        s.add_goal(Goal::Chain((n.clone(), ConcIdx(0)), (n, PremIdx(0))));
        assert_eq!(unsolved_chain_constraints(&s), 1);
    }

    // =========================================================================
    // precompute_sources: unique-source caching correctness
    // =========================================================================

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        for c in ["/home/linuxbrew/.linuxbrew/bin/maude", "/usr/local/bin/maude", "maude"] {
            if std::path::Path::new(c).exists() { return Some(c.to_string()); }
        }
        None
    }

    fn make_rule(name: &str, conc_tag: crate::fact::FactTag) -> crate::theory::OpenProtoRule {
        use crate::fact::Fact;
        use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
        let conc = Fact::new(conc_tag, vec![]);
        let r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard(name),
            vec![],
            vec![conc],
            vec![],
        );
        crate::theory::OpenProtoRule::new(r)
    }

    fn ctx_with_rules(rules: Vec<crate::theory::OpenProtoRule>) -> Option<crate::constraint::solver::context::ProofContext> {
        let path = maude_path()?;
        let h = tamarin_term::maude_proc::MaudeHandle::start(
            &path, tamarin_term::maude_sig::pair_maude_sig()).ok()?;
        Some(crate::constraint::solver::context::ProofContext::new(h, rules))
    }

    #[test]
    fn precompute_sources_picks_single_producer() {
        use crate::fact::{FactTag, Multiplicity};
        let tag = FactTag::Proto(Multiplicity::Linear, "Foo".into(), 0);
        let rules = vec![make_rule("MakeFoo", tag.clone())];
        let ctx = match ctx_with_rules(rules) { Some(c) => c, None => return };
        // Foo is produced by exactly one rule → unique-source entry.
        let entries: Vec<_> = ctx.unique_sources.iter()
            .filter(|s| s.fact_tag == tag)
            .collect();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].rule_name, "MakeFoo");
    }

    #[test]
    fn precompute_sources_drops_multi_producer() {
        use crate::fact::{FactTag, Multiplicity};
        let tag = FactTag::Proto(Multiplicity::Linear, "Bar".into(), 0);
        let rules = vec![
            make_rule("MakeBarA", tag.clone()),
            make_rule("MakeBarB", tag.clone()),
        ];
        let ctx = match ctx_with_rules(rules) { Some(c) => c, None => return };
        // Bar is produced by 2 rules → no unique-source entry.
        let entries: Vec<_> = ctx.unique_sources.iter()
            .filter(|s| s.fact_tag == tag)
            .collect();
        assert!(entries.is_empty(),
            "expected no entry for multi-producer tag, got {:?}", entries);
    }

    /// `precompute_full_sources` returns one `Source` entry per
    /// non-special protocol-fact tag.  For the Loop_Example shape
    /// (Init/Loop/Stop with linear `A(x)`), the tag `A` should have
    /// at least one case (Init) — the Loop case's open Loop-A premise
    /// is captured as a sub-goal pending saturation.
    /// `saturate_sources` should fold the Loop-pattern's recursive
    /// case (`Loop ← Loop ← …`) into a finite enumeration of
    /// self-contained cases — at the saturation limit, no remaining
    /// case carries an open protocol-fact premise.  Mirrors Haskell's
    /// `saturateSources`: after enough iterations each surviving case
    /// is fully grounded in a Fresh-supplied Init.
    #[test]
    fn saturate_loop_pattern_drops_open_premises() {
        use crate::fact::{Fact, FactTag, Multiplicity, fresh_fact};
        use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
        use tamarin_term::builtin::msg_var;

        let path = match maude_path() { Some(p) => p, None => return };
        let h = tamarin_term::maude_proc::MaudeHandle::start(
            &path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let a_tag = FactTag::Proto(Multiplicity::Linear, "A".to_string(), 1);
        let a_fact = Fact::new(a_tag.clone(), vec![msg_var("x", 0)]);
        let init: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Init"),
            vec![fresh_fact(msg_var("x", 0))],
            vec![a_fact.clone()], vec![]);
        let loop_r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Loop"),
            vec![a_fact.clone()], vec![a_fact.clone()], vec![]);
        let stop: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Stop"),
            vec![a_fact.clone()], vec![], vec![]);
        let rules = vec![
            crate::theory::OpenProtoRule::new(init),
            crate::theory::OpenProtoRule::new(loop_r),
            crate::theory::OpenProtoRule::new(stop),
        ];
        let ctx = crate::constraint::solver::context::ProofContext::new(h, rules);
        let a_src = ctx.full_sources.iter().find(|s| match &s.goal {
            crate::constraint::constraints::Goal::Premise(_, fa) => fa.tag == a_tag,
            _ => false,
        }).expect("source for A");
        // Every saturated case must be self-contained.
        for (name, sys) in &a_src.cases {
            assert!(first_open_proto_premise(sys).is_none(),
                "saturated case '{}' still has open proto premise:\n  goals={:?}",
                name, sys.goals);
        }
        assert!(!a_src.cases.is_empty(), "expected saturated cases, got none");
        // Each surviving case should describe a chain of N Loops + 1 Init,
        // with all internal A-fact terms unified to a single var.  Walk
        // every node's premise/conclusion fact in every case and verify
        // there's at most one msg-sort var used across all A facts.
        for (name, sys) in &a_src.cases {
            let mut x_vars: std::collections::BTreeSet<u64> = Default::default();
            let mut details: Vec<String> = Vec::new();
            for (id, ru) in &sys.nodes {
                for fa in ru.premises.iter().chain(ru.conclusions.iter()) {
                    if fa.tag != a_tag { continue; }
                    if let Some(t) = fa.terms.first() {
                        if let tamarin_term::term::Term::Lit(
                            tamarin_term::vterm::Lit::Var(v)) = t
                        {
                            if v.sort == tamarin_term::lterm::LSort::Msg {
                                x_vars.insert(v.idx);
                                details.push(format!("{:?}.A({:?})", id, v));
                            }
                        }
                    }
                }
            }
            assert!(x_vars.len() <= 1,
                "saturated case '{}' has multiple A-arg vars: {:?}\n  details: {:?}",
                name, x_vars, details);
        }
    }

    #[test]
    fn precompute_full_sources_emits_per_tag_entries() {
        use crate::fact::{Fact, FactTag, Multiplicity, fresh_fact};
        use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
        use tamarin_term::builtin::msg_var;

        let path = match maude_path() { Some(p) => p, None => return };
        let h = tamarin_term::maude_proc::MaudeHandle::start(
            &path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();

        let a_tag = FactTag::Proto(Multiplicity::Linear, "A".to_string(), 1);
        let a_fact = Fact::new(a_tag.clone(), vec![msg_var("x", 0)]);
        let init: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Init"),
            vec![fresh_fact(msg_var("x", 0))],
            vec![a_fact.clone()],
            vec![],
        );
        let loop_r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Loop"),
            vec![a_fact.clone()],
            vec![a_fact.clone()],
            vec![],
        );
        let stop: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Stop"),
            vec![a_fact.clone()],
            vec![],
            vec![],
        );
        let rules = vec![
            crate::theory::OpenProtoRule::new(init),
            crate::theory::OpenProtoRule::new(loop_r),
            crate::theory::OpenProtoRule::new(stop),
        ];
        let ctx = crate::constraint::solver::context::ProofContext::new(h, rules);
        // ctx.full_sources is computed at construction time.
        let a_src = ctx.full_sources.iter().find(|s| match &s.goal {
            crate::constraint::constraints::Goal::Premise(_, fa) => fa.tag == a_tag,
            _ => false,
        });
        assert!(a_src.is_some(),
            "expected a precomputed source for tag A; got: {:?}",
            ctx.full_sources.iter().map(|s| &s.goal).collect::<Vec<_>>());
        let a_src = a_src.unwrap();
        assert!(!a_src.cases.is_empty(),
            "source for A should have at least one case (Init / Loop)");
    }

    #[test]
    fn precompute_sources_handles_multiple_unique_tags() {
        use crate::fact::{FactTag, Multiplicity};
        let tag_a = FactTag::Proto(Multiplicity::Linear, "A".into(), 0);
        let tag_b = FactTag::Proto(Multiplicity::Linear, "B".into(), 0);
        let rules = vec![
            make_rule("MakeA", tag_a.clone()),
            make_rule("MakeB", tag_b.clone()),
        ];
        let ctx = match ctx_with_rules(rules) { Some(c) => c, None => return };
        // Both A and B should appear.
        let names: Vec<_> = ctx.unique_sources.iter()
            .filter(|s| s.fact_tag == tag_a || s.fact_tag == tag_b)
            .map(|s| &s.rule_name[..])
            .collect();
        assert!(names.contains(&"MakeA"));
        assert!(names.contains(&"MakeB"));
    }

    // =========================================================================
    // Haskell-faithfulness invariants for `restrict_eq_store_to_stable_vars`.
    //
    // This is the function that exhibited the chain-chase bug for ~6
    // wasted iterations.  These tests pin its contract: pure key-filter,
    // matching Haskell's `Subst.restrict = M.filterWithKey`.
    // =========================================================================

    /// `restrict_eq_store_to_stable_vars` is a pure key-filter — drops
    /// every binding whose KEY is not in stable_vars.  No chain-chase.
    ///
    /// Mirrors `Theory.Tools.EquationStore.restrict`
    /// (via `Term.Substitution.Subst.restrict`, SubstVFree.hs:160-161):
    /// ```haskell
    /// restrict vs (Subst smap) = Subst (M.filterWithKey (\v _ -> v `elem` vs) smap)
    /// ```
    #[test]
    fn restrict_eq_store_keeps_only_stable_keyed_bindings() {
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::subst::Subst;
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        use std::collections::BTreeSet;

        let t1 = LVar::new("t", LSort::Msg, 1);     // stable
        let t2 = LVar::new("t", LSort::Msg, 2);     // stable
        let m19 = LVar::new("m", LSort::Msg, 19);   // not stable
        let sk28 = LVar::new("sk", LSort::Msg, 28); // not stable

        let pub_a = LVar::new("a", LSort::Pub, 0);
        let pub_b = LVar::new("b", LSort::Pub, 0);
        let mut sys = System::empty();
        sys.eq_store.subst = Subst::from_list(vec![
            (t1.clone(),  Term::Lit(Lit::Var(pub_a))),
            (m19.clone(), Term::Lit(Lit::Var(pub_b))),
            (sk28.clone(), Term::Lit(Lit::Var(t2.clone()))),
        ]);

        let stable: BTreeSet<LVar> = [t1.clone(), t2.clone()].into_iter().collect();
        restrict_eq_store_to_stable_vars(&mut sys, &stable);

        // t1 binding kept; m19 + sk28 bindings dropped.
        assert!(sys.eq_store.subst.image_of(&t1).is_some(),
                "stable-keyed binding (t.1) is kept");
        assert!(sys.eq_store.subst.image_of(&m19).is_none(),
                "non-stable-keyed binding (m.19) is dropped");
        assert!(sys.eq_store.subst.image_of(&sk28).is_none(),
                "non-stable-keyed binding (sk.28) is dropped, EVEN THOUGH \
                 its VALUE mentions stable t.2 — restrict is key-only.");
    }

    /// `restrict_eq_store_to_stable_vars` does NOT chain-chase.
    ///
    /// This pins the bug we shipped for ~6 iterations.  If someone
    /// re-introduces chain-chase here, foo_eligibility-class divergences
    /// silently appear in the corpus.
    #[test]
    fn restrict_eq_store_does_not_chain_chase() {
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::subst::Subst;
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        use std::collections::BTreeSet;

        // Set up exactly the foo_eligibility shape: a chain
        // t.1 → e.10 → blind_arg.  Stable = {t.1}.  Haskell-faithful:
        // t.1 → e.10 stays (e.10 unbound after filter).  Rust must NOT
        // collapse to t.1 → blind_arg directly.
        let t1 = LVar::new("t", LSort::Msg, 1);
        let e10 = LVar::new("e", LSort::Msg, 10);
        let blind_arg = LVar::new("m", LSort::Msg, 28);

        let mut sys = System::empty();
        sys.eq_store.subst = Subst::from_list(vec![
            (t1.clone(),  Term::Lit(Lit::Var(e10.clone()))),
            (e10.clone(), Term::Lit(Lit::Var(blind_arg.clone()))),
        ]);

        let stable: BTreeSet<LVar> = [t1.clone()].into_iter().collect();
        restrict_eq_store_to_stable_vars(&mut sys, &stable);

        // t.1's binding must be exactly e.10 (the var), NOT chain-chased
        // to blind_arg.
        assert_eq!(sys.eq_store.subst.image_of(&t1),
                   Some(&Term::Lit(Lit::Var(e10))),
                   "restrict must NOT chain-chase t.1 → e.10 → blind_arg \
                    into t.1 → blind_arg.  This was the foo_eligibility \
                    root cause — see project_rust_foo_eligibility_saturate_overspec.md");
    }

    /// `restrict_eq_store_to_stable_vars` produces empty subst when no
    /// key is stable.  This is the foo_eligibility shape under
    /// Haskell-faithful unification orientation: keys are rule-internal
    /// vars (large idx), stableVars are lemma vars (small idx).
    #[test]
    fn restrict_eq_store_empties_subst_when_no_keys_are_stable() {
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::subst::Subst;
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        use std::collections::BTreeSet;

        let m19 = LVar::new("m", LSort::Msg, 19);
        let sk28 = LVar::new("sk", LSort::Msg, 28);
        let pub_a = LVar::new("a", LSort::Pub, 0);
        let pub_b = LVar::new("b", LSort::Pub, 0);
        let mut sys = System::empty();
        sys.eq_store.subst = Subst::from_list(vec![
            (m19, Term::Lit(Lit::Var(pub_a))),
            (sk28, Term::Lit(Lit::Var(pub_b))),
        ]);

        let stable: BTreeSet<LVar> = [
            LVar::new("t", LSort::Msg, 1),
            LVar::new("t", LSort::Msg, 2),
        ].into_iter().collect();
        restrict_eq_store_to_stable_vars(&mut sys, &stable);

        assert!(sys.eq_store.subst.is_empty(),
                "When no key is in stable set (Haskell shape: keys are \
                 rule-internal large-idx vars, stable are lemma small-idx \
                 vars), restrict produces empty subst.  This is what \
                 enables foo_eligibility's clean runtime applySource bind.");
    }

    // =========================================================================
    // Haskell-faithfulness invariants for `saturated_chain_root` —
    // the function whose `_case_N` mishandling caused 14+ corpus
    // divergences (Cluster B, task #209).
    //
    // Mirrors Haskell `refineSource.combine` (Sources.hs:135-137):
    // strip the "coerce" prefix, descend through chain prefixes, and
    // produce a stable per-chain root name.  Per-closure `_case_N`
    // suffixes are saturate-time artifacts that must not survive into
    // the rendered case name.
    // =========================================================================

    /// Trailing `_case_<N>` (saturate's per-closure suffix) must be
    /// stripped.  Bug regressed 14 lemmas in cluster B until task #209.
    ///
    /// Mirrors Haskell `combine` (Sources.hs:135-137): the per-closure
    /// suffix is a Rust saturate-time artifact; Haskell doesn't add it.
    /// Runtime `distinguish` (ProofMethod.hs:468) adds sibling-disambig
    /// suffixes only when needed.
    #[test]
    fn saturated_chain_root_strips_trailing_case_n() {
        assert_eq!(saturated_chain_root("Alice_case_1"), "Alice");
        assert_eq!(saturated_chain_root("Alice_case_42"), "Alice");
        assert_eq!(saturated_chain_root("Resp_2_case_3"), "Resp_2",
                   "only the FINAL _case_<N> is stripped, not internal _<digit>");
    }

    /// Middle `_case_<N>_` (legacy form: saturate used to produce
    /// `Rule_case_3_chain`) gets stripped from the LEFT.  This is the
    /// step-1 stripping logic that predates the trailing fix.
    #[test]
    fn saturated_chain_root_strips_middle_case_n_underscore() {
        // `Foo_case_3_bar` → strip `Foo_case_3_` → `bar`.
        assert_eq!(saturated_chain_root("Foo_case_3_bar"), "bar");
        // No `_case_N_` middle → keep as-is (modulo prefix stripping).
        assert_eq!(saturated_chain_root("Foo_bar"), "Foo_bar");
    }

    /// Intruder-rule prefixes (`coerce_`, `irecv_`, `ipub_`, `isend_`,
    /// `c_<sym>_`) get peeled iteratively.  Mirrors Haskell's `combine`
    /// behavior of blending out coerce/intruder noise.
    #[test]
    fn saturated_chain_root_strips_intruder_prefixes() {
        assert_eq!(saturated_chain_root("coerce_Alice"), "Alice");
        assert_eq!(saturated_chain_root("isend_Alice"), "Alice");
        assert_eq!(saturated_chain_root("irecv_Bob"), "Bob");
        assert_eq!(saturated_chain_root("ipub_Carol"), "Carol");
        // `c_<sym>_<rest>` strips both the `c_` and the `<sym>_`.
        assert_eq!(saturated_chain_root("c_pair_Alice"), "Alice");
    }

    /// Combination: intruder prefix + trailing `_case_N` both stripped.
    /// This is the actual shape that hit production: an inner rule that
    /// went through coerce got `coerce_Alice_case_1`, which must reduce
    /// to `Alice`.
    #[test]
    fn saturated_chain_root_handles_prefix_and_trailing_suffix() {
        assert_eq!(saturated_chain_root("coerce_Alice_case_1"), "Alice");
        assert_eq!(saturated_chain_root("isend_Resp_2_case_3"), "Resp_2");
    }

    /// Empty / no-match input is returned unchanged.
    #[test]
    fn saturated_chain_root_passes_through_unrecognized_name() {
        assert_eq!(saturated_chain_root("Alice"), "Alice");
        assert_eq!(saturated_chain_root("XYZ"), "XYZ");
    }
}
