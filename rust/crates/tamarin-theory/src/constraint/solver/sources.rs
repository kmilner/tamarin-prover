//! Port of `Theory.Constraint.Solver.Sources`.
//!
//! Sources represent the big-step proofs computing the possible
//! sources of a fact in a constraint system. This module implements:
//!
//! - Precomputing source distinctions for every protocol rule's
//!   premises (`precompute_full_sources`, mirroring `precomputeSources`).
//! - Saturating sources with respect to each other
//!   (`saturate_sources`, mirroring `saturateSources`).
//! - Refining sources with source-assumption lemmas
//!   (`refine_with_source_asms`, mirroring `refineWithSourceAsms`).
//! - Solving a goal by application of a precomputed source
//!   (`solve_with_source_cases*` / `apply_source_case_*`).
//! - Removing redundant cases (`remove_redundant_cases`).
//!
//! Alongside the full machinery it also exposes the public data shapes
//! and the `IntegerParameters` config used by the rest of the solver.

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
    // True while inside `initial_source_cases` (HS's `initialSource`'s
    // `runReduction instantiate`).  HS's initialSource uses `solveGoal`
    // from Goals.hs directly — bypassing `solveWithSource` —so initial
    // case computation never short-circuits via source-case dispatch.
    // Rust mirrors this by gating dispatch in `solve_premise_goal` on
    // `!in_initial_source_cases()`.  Saturate refinement
    // (`saturate_sources_with_simp_public`) does NOT set this flag, so
    // dispatch fires there exactly like HS's `solveAllSafeGoals`.
    static IN_INITIAL_SOURCE_CASES: std::cell::Cell<bool>
        = const { std::cell::Cell::new(false) };
}

/// The variables kept stable across a source-case graft: the live goal's node
/// id plus every free variable of its fact — HS's `frees goal = [iTerm] ++
/// frees faTerm`.  Both the `restrict_eq_store_to_stable_vars` (`stableVars`)
/// restriction and the `someInst` keep-var bindings use this exact set, in the
/// action and premise paths alike; the shared helper makes that invariant
/// explicit instead of leaving four separated copies to drift.
fn collect_node_and_fact_frees(
    live_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
) -> std::collections::BTreeSet<tamarin_term::lterm::LVar> {
    use tamarin_term::lterm::HasFrees;
    let mut s = std::collections::BTreeSet::new();
    s.insert(live_node.clone());
    fa_live.for_each_free(&mut |v: &tamarin_term::lterm::LVar| {
        s.insert(v.clone());
    });
    s
}

/// The set of every node id in `sys` — the membership set used to keep only
/// edges wholly within the live sub-system (E.5).  Loop-invariant across arms,
/// so built once per `apply_source_case_*` call.
fn collect_node_ids(
    sys: &System,
) -> std::collections::BTreeSet<crate::constraint::constraints::NodeId> {
    sys.nodes.iter().map(|(n, _)| n.clone()).collect()
}

/// Build a fresh per-arm `Reduction` for a source-case DisjT fan-out: install
/// `arm_eq` into a clone of `template` (invalidating the cached max-var idx) and
/// wrap it in a new `Reduction`.  Mirrors HS's `DisjT` replication of the
/// Reduction continuation (Reduction.hs:724-725 `disjunctionOfList
/// performSplit`); shared by the action/premise fan-outs so the
/// clone-then-install sequence lives in exactly one place.
fn fork_arm_reduction<'c>(
    ctx: &'c crate::constraint::solver::context::ProofContext,
    template: &System,
    arm_eq: crate::tools::equation_store::EquationStore,
) -> crate::constraint::solver::reduction::Reduction<'c> {
    use crate::constraint::solver::reduction::Reduction;
    let mut arm_sys = template.clone();
    arm_sys.invalidate_max_var_idx_cache();
    arm_sys.eq_store = std::sync::Arc::new(arm_eq);
    Reduction::new(ctx, arm_sys)
}

/// E.5 nested fan-out: for each arm eq-store, fork a `Reduction` off `template`
/// (see [`fork_arm_reduction`]), run `subst_system`, and collect the surviving
/// (non-`false`-eq-store) systems into `out`.  Shared verbatim by the action and
/// premise E.5 `Cases` arms.
fn subst_arms_into(
    ctx: &crate::constraint::solver::context::ProofContext,
    template: &System,
    arms: Vec<crate::tools::equation_store::EquationStore>,
    out: &mut Vec<System>,
) {
    for arm_eq in arms {
        let mut arm_red = fork_arm_reduction(ctx, template, arm_eq);
        arm_red.subst_system();
        if arm_red.sys.eq_store.is_false() { continue; }
        out.push(arm_red.sys);
    }
}

pub fn in_precompute_mode() -> bool {
    IN_PRECOMPUTE.with(|c| c.get())
}

fn set_precompute_mode(v: bool) {
    IN_PRECOMPUTE.with(|c| c.set(v));
}

pub fn in_initial_source_cases() -> bool {
    IN_INITIAL_SOURCE_CASES.with(|c| c.get())
}

fn set_initial_source_cases(v: bool) {
    IN_INITIAL_SOURCE_CASES.with(|c| c.set(v));
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
        // Defaults match Haskell's `defaultTheoryLoadOptions`
        // (TheoryLoader.hs:244-245): openChain=10, saturation=5.
        IntegerParameters {
            open_chains_limit: 10,
            saturation_limit: 5,
            show_saturation_steps: false,
        }
    }
}

/// Number of unsolved-chain constraints in the system. Mirrors
/// `length . unsolvedChains` (System.hs:1601), counting unsolved Chain
/// goals in one System. (Distinct from Haskell `unsolvedChainConstraints
/// :: Source -> [Int]` at Sources.hs:87-89, which maps over a Source's
/// cases.)
pub fn unsolved_chain_constraints(sys: &System) -> usize {
    use crate::constraint::constraints::Goal;
    sys.goals.iter()
        .filter(|(g, status)| !status.solved && matches!(g, Goal::Chain(_, _)))
        .count()
}

/// `Source` — one precomputed case distinction. The Haskell version
/// is `Source { _cdGoal :: Goal, _cdCases :: Disj (M.Map CaseName System) }`.
/// `cdCases` is a lazy thunk in HS; matched here by `cases_cell`, a
/// `OnceLock` that's filled on the first `cases(ctx)` call.  Trivial
/// protocols never force `KU(t:Fresh)`-style sources (HS's
/// `smartRanking.getMsgOneCase` pattern-matches on `FApp o _` before
/// touching `cdCases`, so Var-headed sources never trigger the thunk);
/// Rust matches by deferring `solve_action_goal` / `solve_premise_goal`
/// out of `precompute_full_sources` into the lazy initialiser.
pub struct Source {
    pub goal: crate::constraint::constraints::Goal,
    /// Lazy cases — wrapped in `Mutex<Option<…>>` for interior
    /// mutability.  `Mutex` (over `OnceLock`) lets `cases_set` /
    /// `cases_take` mutate the cell after initial materialisation,
    /// which `ProofContext::ensure_saturated`'s post-saturate writeback
    /// requires.
    /// Internally stores case names as `Vec<String>` — HS's
    /// `caseNames :: [String]` (the `caseNames` parameter of `solve` at
    /// Sources.hs:175; `[String]` type at Sources.hs:144).  The list
    /// representation is critical for `combine`'s truncation rule
    /// `combine (n:_) _ = [n]` (Sources.hs:139): without per-element
    /// boundaries, multi-step accumulated names can't be truncated
    /// to a single element across refineSource iters.  External
    /// callers using `cases_or_empty()` / `cases_get()` / etc. see
    /// the joined `String` (intercalated with "_") for backward
    /// compat; saturate-internal code uses the `_list` variants
    /// that preserve list structure.
    pub(crate) cases_cell: std::sync::Mutex<Option<Vec<(Vec<String>, System)>>>,
    /// `true` iff case enumeration was truncated.  Search must not return
    /// `Verified` for any proof tree that consumed an incomplete
    /// source — the dropped cases could contain attack witnesses.
    /// Used to prevent wrong-VERIFIED on user-equation files where the
    /// destructor-chain explosion forces truncation.
    pub incomplete: bool,
}

impl std::fmt::Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Source")
            .field("goal", &self.goal)
            .field("cases", &self.cases_cell.lock().ok().as_deref())
            .field("incomplete", &self.incomplete)
            .finish()
    }
}

impl Clone for Source {
    fn clone(&self) -> Self {
        let v = self.cases_cell.lock().unwrap().clone();
        Source {
            goal: self.goal.clone(),
            cases_cell: std::sync::Mutex::new(v),
            incomplete: self.incomplete,
        }
    }
}

impl PartialEq for Source {
    fn eq(&self, other: &Self) -> bool {
        let a = self.cases_cell.lock().unwrap().clone();
        let b = other.cases_cell.lock().unwrap().clone();
        self.goal == other.goal
            && self.incomplete == other.incomplete
            && a == b
    }
}

impl Source {
    /// Build a Source whose cases will be computed lazily via
    /// `initial_source_cases(goal, ctx)` on the first `cases(ctx)`
    /// call.  Matches HS's `initialSource` (Sources.hs:103) thunk.
    pub fn lazy(goal: crate::constraint::constraints::Goal) -> Self {
        Source { goal, cases_cell: std::sync::Mutex::new(None), incomplete: false }
    }

    /// Build a Source with cases already computed.  Used by saturate
    /// internals that produce already-materialised case sets, and by
    /// `Source::new` for back-compat with old `Source { goal, cases:
    /// Vec::new(), .. }`-style construction.
    ///
    /// Takes `Vec<(String, System)>` for backward compat: each `String`
    /// becomes a single-element `Vec<String>` in the internal list
    /// representation.  Use [`Source::eager_list`] to pass an actual
    /// `Vec<(Vec<String>, System)>`.
    pub fn eager(goal: crate::constraint::constraints::Goal,
                 cases: Vec<(String, System)>,
                 incomplete: bool) -> Self {
        let list: Vec<(Vec<String>, System)> = cases.into_iter()
            .map(|(n, s)| (string_to_name_list(&n), s))
            .collect();
        Source { goal, cases_cell: std::sync::Mutex::new(Some(list)), incomplete }
    }

    /// Build a Source with case-name LISTS already computed.  Used by
    /// saturate-internal code that preserves HS's `[String]` list
    /// structure across refineSource iters.
    pub fn eager_list(goal: crate::constraint::constraints::Goal,
                      cases: Vec<(Vec<String>, System)>,
                      incomplete: bool) -> Self {
        Source { goal, cases_cell: std::sync::Mutex::new(Some(cases)), incomplete }
    }

    /// Back-compat constructor: starts with empty (already-set) cases.
    /// Callers that want true HS-lazy behaviour should use
    /// [`Source::lazy`] instead.
    pub fn new(goal: crate::constraint::constraints::Goal) -> Self {
        Source::eager(goal, Vec::new(), false)
    }

    /// Materialise + return the cases.  `prove_lemma` runs
    /// `ProofContext::ensure_saturated` eagerly before any lemma proof
    /// starts, so the cached value is normally already populated.
    /// The defensive `ensure_saturated()` call below is idempotent
    /// (state machine returns immediately when Done) and handles
    /// odd code paths that bypass `prove_lemma` (tests, probes).
    ///
    /// Returns by-value (`Vec<…>`) rather than `&Vec<…>` because the
    /// cell is a `Mutex` and we can't hold the lock for the caller's
    /// lifetime.  Callers iterate the returned Vec normally.
    pub fn cases(&self, ctx: &crate::constraint::solver::context::ProofContext)
        -> Vec<(String, System)>
    {
        cases_list_to_string_list(self.cases_list(ctx))
    }

    /// HS-faithful: returns cases with name-LISTS preserved.  Use this
    /// when the per-element list structure matters for `combine`
    /// (`combine_case_names_list`) at refineSource boundaries.
    pub fn cases_list(&self, ctx: &crate::constraint::solver::context::ProofContext)
        -> Vec<(Vec<String>, System)>
    {
        ctx.ensure_saturated();
        let g = self.cases_cell.lock().unwrap();
        match &*g {
            Some(v) => v.clone(),
            None => {
                drop(g);
                let init = initial_source_cases(&self.goal, ctx);
                let init_list: Vec<(Vec<String>, System)> = init.into_iter()
                    .map(|(n, s)| (string_to_name_list(&n), s))
                    .collect();
                *self.cases_cell.lock().unwrap() = Some(init_list.clone());
                init_list
            }
        }
    }

    /// Return the cases iff already forced; do NOT trigger
    /// computation.  Use in consumers (e.g. `collect_one_case_syms`)
    /// that can short-circuit on the goal shape.
    pub fn cases_get(&self) -> Option<Vec<(String, System)>> {
        self.cases_cell.lock().unwrap().clone()
            .map(cases_list_to_string_list)
    }

    /// Same as `cases_get` but returns the HS-faithful list form.
    pub fn cases_get_list(&self) -> Option<Vec<(Vec<String>, System)>> {
        self.cases_cell.lock().unwrap().clone()
    }

    /// Read-only clone that returns `vec![]` when the cell hasn't
    /// been forced yet.  External-facing form (joined-String).
    pub fn cases_or_empty(&self) -> Vec<(String, System)> {
        cases_list_to_string_list(self.cases_or_empty_list())
    }

    /// HS-faithful: same as `cases_or_empty` but preserves the
    /// per-element list structure.
    pub fn cases_or_empty_list(&self) -> Vec<(Vec<String>, System)> {
        self.cases_cell.lock().unwrap().clone().unwrap_or_default()
    }

    /// `true` iff `cases_cell` already holds a value (whether empty
    /// or populated).  Cheap O(1).
    pub fn cases_is_materialized(&self) -> bool {
        self.cases_cell.lock().unwrap().is_some()
    }

    /// Number of materialised cases — equal to `cases_or_empty().len()`
    /// but WITHOUT deep-cloning every case `System` to count them.
    /// Returns 0 when the cell hasn't been forced yet.  O(1).
    pub fn cases_len(&self) -> usize {
        self.cases_cell.lock().unwrap().as_ref().map_or(0, Vec::len)
    }

    /// Drain the materialised cases out of the cell, leaving it as
    /// `None`.  Used by saturate internals that re-build the cases
    /// list per iteration.  External-facing form (joined-String).
    pub fn cases_take(&self) -> Vec<(String, System)> {
        cases_list_to_string_list(self.cases_take_list())
    }

    /// HS-faithful: same as `cases_take` but preserves list structure.
    pub fn cases_take_list(&self) -> Vec<(Vec<String>, System)> {
        self.cases_cell.lock().unwrap().take().unwrap_or_default()
    }

    /// Replace the cases cell with a new value.  Used by saturate to
    /// install a refined case set, AND by `ensure_saturated`'s post-
    /// saturate writeback.  Takes `&self` (not `&mut`) so it works
    /// through immutable `ctx.full_sources` borrows.
    /// External-facing form: each `String` name is wrapped as a
    /// single-element list.
    pub fn cases_set(&self, cases: Vec<(String, System)>) {
        let list: Vec<(Vec<String>, System)> = cases.into_iter()
            .map(|(n, s)| (string_to_name_list(&n), s))
            .collect();
        *self.cases_cell.lock().unwrap() = Some(list);
    }

    /// HS-faithful: same as `cases_set` but takes the list form
    /// directly, preserving per-element boundaries.
    pub fn cases_set_list(&self, cases: Vec<(Vec<String>, System)>) {
        *self.cases_cell.lock().unwrap() = Some(cases);
    }
}

/// Convert `(Vec<String>, System)` case-list to the external
/// `(String, System)` form via HS's `intercalate "_"` join.
fn cases_list_to_string_list(
    list: Vec<(Vec<String>, System)>,
) -> Vec<(String, System)> {
    list.into_iter()
        .map(|(n, s)| (case_name_list_to_string(&n), s))
        .collect()
}

/// HS-faithful port of `initialSource ctxt restrictions goal`
/// (Sources.hs:103).  Builds a fresh empty system with restrictions
/// injected, inserts `goal`, marks-as-solved (HS `solveGoal`-style),
/// then dispatches to the goal-specific solver.  The resulting cases
/// are normalised: subst applied, simplify run, contradictory cases
/// dropped, eq-store restricted to stable (= `frees (cdGoal th)`) vars.
/// Crate-internal exposure of [`initial_source_cases`] so
/// `ProofContext::ensure_saturated` can pre-populate each source's
/// cases before running saturate.
pub(crate) fn initial_source_cases_pub(
    goal: &crate::constraint::constraints::Goal,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<(String, System)> {
    initial_source_cases(goal, ctx)
}

fn initial_source_cases(
    goal: &crate::constraint::constraints::Goal,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<(String, System)> {
    // HS-faithful: `initialSource` calls `solveGoal` from Goals.hs
    // directly (NOT via `solveWithSource`), so initial case computation
    // never short-circuits through source-case dispatch.  Set the flag
    // so `solve_premise_goal`'s dispatch skips during this call.
    let prev_initial = in_initial_source_cases();
    set_initial_source_cases(true);
    let result = initial_source_cases_impl(goal, ctx);
    set_initial_source_cases(prev_initial);
    result
}

fn initial_source_cases_impl(
    goal: &crate::constraint::constraints::Goal,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<(String, System)> {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::reduction::{Reduction, GoalCases};

    let mut sys = System::empty();
    // HS-faithful (Rule.hs:152-156): source precomputation gets ONLY
    // safety restrictions.  Non-safety restrictions (e.g.
    // `Start_implies_Stop = All x #i. Start(x)@i ⇒ Ex #j. Stop(x)@j`)
    // would fire `insertImpliedFormulas` during saturate, spawning Stop
    // ActionG / node via `solveUniqueActions`, which would re-open B
    // premise → another Step → another A premise → another Start →
    // restriction fires again → Cyclic.  HS skips this entire chain by
    // filtering to safety formulas at `Rule.hs:152`.
    let safety_restrictions: Vec<_> = ctx.restrictions.iter()
        .filter(|r| crate::guarded::is_safety_formula(r))
        .cloned()
        .collect();
    sys.insert_lemmas(safety_restrictions);
    let mut red = Reduction::new(ctx, sys);
    red.insert_goal(goal.clone());
    // HS-faithful: `solveGoal goal` (Goals.hs:201-213) marks the goal
    // BEFORE invoking the solver, since unification inside the solver
    // can rewrite the goal's fact terms.
    red.mark_goal_as_solved(goal);
    // RS emits a solveGoal trace label here for diffing; HS's `solveGoal`
    // (Goals.hs:200-213) only does `markGoalAsSolved "directly" goal` and
    // dispatches — it has no trace emission (no traceExecM/goalKind exist
    // in HS).
    {
        use crate::constraint::solver::trace::trace_exec;
        let label = match goal {
            Goal::Action(_, fa)  => format!("solveGoal kind=Action fact={}({})",
                crate::constraint::solver::goals::fact_tag_haskell_pub(fa),
                crate::constraint::solver::goals::fact_term_head_pub(fa)),
            Goal::Premise(_, fa) => format!("solveGoal kind=Premise fact={}({})",
                crate::constraint::solver::goals::fact_tag_haskell_pub(fa),
                crate::constraint::solver::goals::fact_term_head_pub(fa)),
            Goal::Chain(_, _)    => "solveGoal kind=Chain".to_string(),
            Goal::Split(_)       => "solveGoal kind=Split".to_string(),
            Goal::Disj(_)        => "solveGoal kind=Disj".to_string(),
            Goal::Subterm(_)     => "solveGoal kind=Subterm".to_string(),
        };
        trace_exec(&label);
    }

    let outcome = match goal {
        Goal::Action(node, fa)  => red.solve_action_goal(node, fa),
        Goal::Premise(prem, fa) => red.solve_premise_goal(prem, fa),
        _ => return Vec::new(),
    };

    let stable_vars = stable_vars_for_goal(goal);
    // Same HS-faithful filter — safety only — for normalize_and_keep.
    let safety_only: Vec<_> = ctx.restrictions.iter()
        .filter(|r| crate::guarded::is_safety_formula(r))
        .cloned()
        .collect();
    let normalize_and_keep = |sys: System, _case_name: &str| -> Option<System> {
        let mut r = Reduction::new(ctx, sys);
        r.sys.insert_lemmas(safety_only.clone());
        r.subst_system();
        // HS-faithful: HS `initialSource`'s `runReduction instantiate`
        // does NOT call `simplifySystem` between the `solveGoal goal`
        // step and case readout — `simplifySystem` runs only when the
        // lemma proof's `runReduction` path invokes it (proof method
        // dispatch / `solveAllSafeGoals` saturate loop).  But our case
        // normalisation here *does* need simplify to settle subst /
        // contradiction markers, so we run it but trace separately to
        // match HS's per-call trace convention.
        crate::constraint::solver::trace::trace_exec("simplifySystem");
        crate::constraint::solver::simplify::simplify_system(&mut r);
        if r.sys.eq_store.is_false() { return None; }
        if !crate::constraint::solver::contradictions::contradictions(ctx, &r.sys)
            .is_empty()
        { return None; }
        let mut s = r.sys;
        restrict_eq_store_to_stable_vars(&mut s, &stable_vars);
        Some(s)
    };
    let result: Vec<(String, System)> = match outcome {
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
    if tamarin_utils::env_gate!("TAM_DBG_INIT_SRC") {
        use tamarin_term::pretty::pretty_lnterm;
        let goal_str = match goal {
            Goal::Action(_, fa) | Goal::Premise(_, fa) => {
                let ts: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
                format!("{:?}({})", fa.tag, ts.join(", "))
            }
            _ => format!("{:?}", goal),
        };
        let names: Vec<&str> = result.iter().map(|(n, _)| n.as_str()).collect();
        eprintln!("[init_src] {} → {} cases: {:?}",
            goal_str, result.len(), names);
    }
    result
}

/// Build the structural unique-source map. For every conclusion fact
/// tag across the proof context's rules, count how many rules produce
/// it; each tag with exactly one producer yields a `UniqueSource`
/// recording the fact tag and the sole producing rule's name. The
/// result is sorted and deduplicated by fact tag.
///
/// This is a lightweight one-rule-one-source mapping, distinct from the
/// full case-distinction enumeration in `precompute_full_sources`. It is
/// stored on the `ProofContext` as `unique_sources`.
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

/// One structural unique-source entry: a fact tag whose only producer
/// is the named rule.
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

    // Lazy precompute (matches HS): emit Source structs whose `goal`
    // is set but whose `cases` are uncomputed.  When a consumer asks
    // for `src.cases(ctx)`, `initial_source_cases` runs at THAT
    // point — same as HS forcing a `cdCases` thunk.  For trivial
    // protocols where no consumer asks (e.g. `KU(t:Fresh)` source on
    // an existence lemma that hits the Recv→isend direct-enumeration
    // path), zero `[EXEC] solveGoal kind=Action fact=KUFact(...)`
    // lines fire — matching HS's output line-for-line.
    //
    // Saturation (`saturate_sources_with_simp_public`) is a separate
    // concern: it iterates `cases` and would defeat the laziness if
    // run here.  ProofContext::new no longer calls it.  See
    // `context.rs` for the call-site change.
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
        // HS-faithful: defer `initialSource`'s `solve_premise_goal`
        // call to `Source::cases(ctx)`'s first invocation.  No work
        // done here, no `[EXEC] solveGoal kind=Premise ...` line
        // emitted.  The trace fires when (and only when) a consumer
        // forces `cases(ctx)`.
        out.push(Source::lazy(goal));
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
    // Per HS Sources.hs, `absMsgFacts` is `asum $ sortednub $ [..]`
    // i.e. the union of:
    //   (1) fresh-sorted singleton t.1
    //   (2) bilinear pairing em(t.1,t.2)  [if enableBP]
    //   (3) nat 1, nat t.1 %+ t.2          [if enableNat]
    //   (4) one fAppNoEq per non-implicit NoEq symbol of arity ≥ 1 OR Private
    // After `sortednub`, the list is sorted by `Ord LNTerm`.  Term Ord
    // tiebreaks first on the head FunSym; FunSym Ord is `NoEq < Ac < C`
    // (see FunctionSymbols.hs:113-117; mirrored in
    // `function_symbols.rs:62-69`).  So C(EMap)-headed em(...) sorts
    // AFTER every NoEq-headed term — i.e. em ends up LAST in HS's
    // SAT-FINAL output for Chen_Kudla / Joux / RYY / Scott / TAK1.
    //
    // Honour that ordering here so the runtime sees sources in the
    // same order HS does — `solve_with_source_cases` consults
    // `ctx.full_sources` in iteration order, and a divergent order
    // alone is enough to swing rule-case picks (see Chen_Kudla:
    // `case Resp_1` vs `case Init_1` regression when em was inserted
    // 2nd instead of last).
    //
    // Strategy: push fresh first (sorts before any App), then all
    // NoEq fAppNoEq's via the `msig.fun_syms` BTreeSet iter (already
    // alphabetical by name), then C / AC symbols at the tail.
    //
    // Mirrors HS Sources.hs:
    //     return $ varTerm (LVar "t" LSortFresh 1)
    ku_patterns.push(tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
        tamarin_term::lterm::LVar::new(
            "t", tamarin_term::lterm::LSort::Fresh, 1))));
    let msig = ctx.maude.maude_sig();
    // Per-function-symbol applications.  Use Msg-sorted arg vars.
    // Mirrors Haskell `absMsgFacts` (Sources.hs):
    //     [ fAppNoEq o $ nMsgVars k
    //     | o@(_,(k,priv,_)) <- S.toList . noEqFunSyms $ msig
    //     , NoEq o `S.notMember` implicitFunSig
    //     , k > 0 || priv == Private ]
    // i.e. all NoEq symbols whose arity is ≥ 1 OR which are
    // Private, excluding the implicit `pair`/`inv`/`Mult`/`Union`
    // symbols (FunctionSymbols.hs:228).  Includes both constructors
    // AND destructors (e.g. `adec`, `fst`, `snd`).
    //
    // HS uses `noEqFunSyms msig` which is the full NoEq set, including
    // reducible symbols (`adec`, `fst`, `snd`, ...).  Rust's
    // `irreducible_fun_syms` filters these out, so use `fun_syms`
    // instead to mirror HS.
    for sym in &msig.fun_syms {
        if let tamarin_term::function_symbols::FunSym::NoEq(noeq) = sym {
            // Skip HS `implicitFunSig` symbols: pair, inv.  (Mult and
            // Union are AC, not NoEq, so they're naturally excluded.)
            // Previously also excluded fst/snd/1 — but HS includes
            // those, so dropping the exclusion to match.
            let name = String::from_utf8_lossy(&noeq.name);
            if matches!(name.as_ref(), "pair" | "inv") { continue; }
            // HS arity gate: `k > 0 || priv == Private` —
            // include arity-≥1 symbols (regardless of priv/cons)
            // and arity-0 Private symbols.  Drop the
            // Constructor-only filter that Rust used previously.
            let private = matches!(noeq.privacy,
                tamarin_term::function_symbols::Privacy::Private);
            if noeq.arity == 0 && !private { continue; }
            let args: Vec<tamarin_term::lterm::LNTerm> = (0..noeq.arity)
                .map(|i| tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
                    tamarin_term::lterm::LVar::new(
                        "t", tamarin_term::lterm::LSort::Msg, (i + 1) as u64))))
                .collect();
            ku_patterns.push(tamarin_term::term::Term::App(
                tamarin_term::function_symbols::FunSym::NoEq(noeq.clone()),
                args.into()));
        }
    }
    // Natural-numbers branch.  Mirrors HS Sources.hs:
    //     if enableNat msig then
    //       [ fAppNoEq natOneSym []
    //       , fAppAC NatPlus [varTerm (LVar "t" LSortNat 1), varTerm (LVar "t" LSortNat 2)] ]
    //       else []
    // AC-headed; sorts BEFORE C-headed em per FunSym Ord NoEq<Ac<C.
    if msig.enable_nat {
        ku_patterns.push(tamarin_term::term::f_app_no_eq(
            tamarin_term::function_symbols::nat_one_sym(), vec![]));
        let nat_args: Vec<tamarin_term::lterm::LNTerm> = (1..=2u64)
            .map(|i| tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
                tamarin_term::lterm::LVar::new(
                    "t", tamarin_term::lterm::LSort::Nat, i))))
            .collect();
        ku_patterns.push(tamarin_term::term::f_app_ac(
            tamarin_term::function_symbols::AcSym::NatPlus, nat_args));
    }
    // Bilinear pairing branch.  Mirrors HS Sources.hs:
    //     if enableBP msig then return $ fAppC EMap $ nMsgVars (2::Int) else []
    // C-headed; sortednub puts this LAST (after every NoEq + Ac term).
    // Without this, BP-theory targets (Chen_Kudla, TAK1, Joux, RYY,
    // Scott) miss the `KU(em(t.1,t.2))` source.  HS emitted 9 KU
    // sources for Chen_Kudla; pre-fix RS emitted 8 — exactly the
    // `em` source was missing.
    if msig.enable_bp {
        let args: Vec<tamarin_term::lterm::LNTerm> = (1..=2u64)
            .map(|i| tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(
                tamarin_term::lterm::LVar::new(
                    "t", tamarin_term::lterm::LSort::Msg, i))))
            .collect();
        ku_patterns.push(tamarin_term::term::f_app_c(
            tamarin_term::function_symbols::CSym::EMap, args));
    }
    // TAM_DBG_SRC_PRECOMP=1: dump every ku_pattern + every fun_sym
    // considered, so we can verify that precompute generated sources
    // for the expected function symbols.
    if tamarin_utils::env_gate!("TAM_DBG_SRC_PRECOMP") {
        eprintln!("[src_precomp] msig.fun_syms ({} entries):", msig.fun_syms.len());
        for sym in &msig.fun_syms {
            eprintln!("  fun_sym: {:?}", sym);
        }
        eprintln!("[src_precomp] generated {} ku_patterns:", ku_patterns.len());
        for (i, pat) in ku_patterns.iter().enumerate() {
            let s = format!("{:?}", pat).chars().take(160).collect::<String>();
            eprintln!("  ku[{}]: {}", i, s);
        }
    }
    for pat in ku_patterns {
        let ku_fact = crate::fact::ku_fact(pat.clone());
        let goal = Goal::Action(goal_node.clone(), ku_fact.clone());
        // HS-faithful lazy: defer `solve_action_goal` + normalisation
        // to `Source::cases(ctx)`.  No work done here.
        out.push(Source::lazy(goal));
    }

    set_precompute_mode(false);
    if tamarin_utils::env_gate!("TAM_DBG_SRC_LIST") {
        eprintln!("[src_list] precompute_full_sources emitted {} sources:", out.len());
        for (i, src) in out.iter().enumerate() {
            let s = format!("{:?}", src.goal).chars().take(200).collect::<String>();
            eprintln!("  src[{}] = {}", i, s);
        }
    }
    // TAM_DBG_SRC_CASES=1: force materialization of every source's
    // cases and dump per-source case name list + count.  Mirrors HS
    // SAT-FINAL output for byte-level comparison.
    if tamarin_utils::env_gate!("TAM_DBG_SRC_CASES") {
        eprintln!("[src_cases] forcing materialization of {} sources:", out.len());
        for (i, src) in out.iter().enumerate() {
            let cases = src.cases(ctx);
            let names: Vec<String> = cases.iter().map(|(n, _)| n.clone()).collect();
            let g_str = format!("{:?}", src.goal).chars().take(120).collect::<String>();
            eprintln!("  src[{}] cases={} names={:?} goal={}",
                i, cases.len(), names, g_str);
        }
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

/// Compute the source label that would identify a KU-action source
/// matching the given live `fa` (a KU fact with a single term).
/// Mirrors `source_label`'s KU arm — used at the runtime filterCases
/// step where we have the live fa (not the source).  Equivalent to
/// Haskell's full-`Source` equality (Sources.hs:217-218, signature 217,
/// body 218: `filterCases usedCase cds = filter (\x -> usedCase /= x) cds`)
/// under the precompute invariant: `precompute_full_sources` emits
/// at most one Source per distinct KU root symbol (mirroring
/// Haskell's `sortednub absMsgFacts`), and `refineSource` preserves
/// `cdGoal` through saturation — so label-equality identifies the
/// same Source that Haskell's structural `Eq` would.
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

fn system_max_idx(sys: &System) -> u64 {
    use std::cell::Cell;
    use tamarin_term::lterm::HasFrees;
    use crate::constraint::constraints::Goal;
    let max = Cell::new(0u64);
    let mut visit = |v: &tamarin_term::lterm::LVar| {
        let cur = max.get();
        if v.idx > cur { max.set(v.idx); }
    };
    for (id, ru) in sys.nodes.iter() {
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
    for (g, _) in sys.goals.iter() {
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
    // Subterm-store: HS `instance HasFrees System` (System.hs:1833-1847)
    // folds over the subterm store too, so vars living only here must be
    // covered or a later freshen/reserve can collide with them.
    for sc in sys.subterm_store.subterms.iter()
        .chain(sys.subterm_store.solved_subterms.iter())
    {
        sc.small.for_each_free(&mut visit);
        sc.big.for_each_free(&mut visit);
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
        for (name, mut sys) in src.cases_take() {
            for a in assumptions {
                if !sys.formulas.contains(a) && !sys.solved_formulas.contains(a) {
                    sys.formulas.push(a.clone());
                }
            }
            // Mirror Haskell `set sSourceKind RefinedSource`.
            sys.source_kind = Some(crate::constraint::system::SourceKind::RefinedSources);
            new_cases.push((name, sys));
        }
        if !new_cases.is_empty() {
            intermediate.push(Source::eager(src.goal, new_cases, src.incomplete));
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
    // growth.
    let limit: usize = 5;
    let saturated = saturate_sources_with_simp(intermediate, limit, ctx);

    // Step 3 (Haskell `removeFormulas`): strip formulas + solved
    // formulas after saturation, and drop disjunction goals derived
    // from the assumptions.
    let mut out: Vec<Source> = Vec::new();
    for src in saturated {
        let mut new_cases: Vec<(String, System)> = Vec::new();
        for (name, mut sys) in src.cases_take().into_iter() {
            sys.formulas.clear();
            sys.solved_formulas.clear();
            sys.invalidate_max_var_idx_cache();
            sys.goals_mut().retain(|(g, _)|
                !matches!(g, crate::constraint::constraints::Goal::Disj(_)));
            new_cases.push((name, sys));
        }
        if !new_cases.is_empty() {
            out.push(Source::eager(src.goal, new_cases, src.incomplete));
        }
    }
    out
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

/// `pub` re-export of [`saturate_sources_with_simp`] for
/// `ProofContext::ensure_saturated`.
pub fn saturate_sources_with_simp_public(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
) -> Vec<Source> {
    saturate_sources_with_simp(sources, limit, ctx)
}

/// Per-source body of `saturate_sources_with_simp_opt`'s inner loop —
/// extracted so it can run in parallel via rayon (mirroring HS's
/// `changes \`using\` parList rdeepseq` at Sources.hs).
///
/// Returns:
///   - `new_cases` (the source's refined case list, post-restrict+dedup);
///   - `changed` (HS's `not (null names)` change signal — i.e. did any
///     case in this source advance via solveAllSafeGoals or get
///     dropped via contradiction?);
///   - `new_case_count` (count of surviving cases, == new_cases.len()).
///
/// Pure with respect to the caller's mutable state — does not touch
/// `next`, `changed`, or `current` from the outer loop.  Reads `ctx`
/// (shared, immutable), `ths_snapshot` (shared, immutable), and other
/// scalar params.  Maude IPC inside is serialised via the handle's
/// Mutex; `set_precompute_mode` is `thread_local!` so the per-worker
/// flag toggle is independent.
fn refine_one_source(
    ctx: &crate::constraint::solver::context::ProofContext,
    src: Source,
    ths_snapshot: &[Source],
    branch_cap: usize,
    aggressive_drop: bool,
    dbg: bool,
) -> (Vec<(Vec<String>, System)>, bool, usize) {
    use crate::constraint::solver::contradictions::contradictions;
    let mut new_cases: Vec<(Vec<String>, System)> = Vec::new();
    let mut changed = false;
    // HS-faithful `refineSource` (Sources.hs:131-148): the Reduction
    // monad flattens all `getDisj cdCases th` into a single Disj of
    // post-refine branches; `removeRedundantCases` deduplicates that
    // flat list ONCE at the end.  Previously RS applied dedup PER
    // input case (input=1 — a no-op for single-branch cases), so
    // alpha-equivalent branches arising from DIFFERENT input cases
    // were never compared.  Accumulate to a deferred list and
    // dedup in a single pass after the loop.
    let mut deferred_filtered: Vec<(Vec<String>, crate::constraint::system::System)>
        = Vec::new();
    // `stable_vars` (frees of the source's `cdGoal`) is invariant across
    // the whole function — `src.goal` is never mutated by the loop — so
    // compute it ONCE here and reuse it both inside the branch loop and
    // for the post-loop removeRedundantCases.
    let mut stable_vars: std::collections::BTreeSet<
        tamarin_term::lterm::LVar> = std::collections::BTreeSet::new();
    goal_free_vars(&src.goal, &mut |v| {
        stable_vars.insert(v.clone());
    });
    for (name_list, sys) in src.cases_take_list() {
        // === Multi-branch refineSource (Haskell-faithful) ===
        set_precompute_mode(true);
        // HS-faithful: NO per-branch step cap.  HS `solveAllSafeGoals`
        // (Sources.hs:201-211) recurses until no safe goal and no
        // source-pick remains; the ONLY exploration bounds are the
        // open-chains limit (`chainsLeft`, paramOpenChainsLimit,
        // Sources.hs:151-153/383) and the outer saturation limit
        // (paramSaturationLimit, Sources.hs:362/368).  A finite default
        // here PARKED branches mid-flight as emitted cases — states
        // with open chain/KD goals HS would have solved or
        // contradicted — ballooning Chen_Kudla's KU(exp) source from
        // HS's 29 cases to 276 and flipping the no_WPFS verdict.  HS has
        // no such cap (only chainsLeft + paramSaturationLimit), so this
        // is unconditionally unbounded.
        let outer_cap: i64 = i64::MAX;
        // Only build the debug case-name join when actually debugging;
        // `name_list` is moved into the solver call below, so capture it
        // here under the `dbg` guard.  The non-dbg path skips the join.
        let case_name_for_dbg = if dbg {
            Some(case_name_list_to_string(&name_list))
        } else {
            None
        };
        let (branches, branch_took_step) = run_solve_all_safe_goals_disj_with_progress(
            ctx, sys, ths_snapshot, /*chains_limit*/ 10,
            outer_cap, branch_cap, name_list);
        if branch_took_step {
            // HS-faithful `not (null names)` change signal —
            // solveAllSafeGoals took at least one step (safe-goal
            // solve or source-pick) on this case.  Drives outer
            // saturate re-iteration even when case count doesn't
            // grow, so multi-iter convergence patterns like
            // chaum's KU(~x:Fresh)→1-case work.  See
            // [[project-chaum-case-fresh-divergence]].
            changed = true;
        }
        set_precompute_mode(false);
        if dbg {
            eprintln!("  case {:?}: refineSource produced {} branches",
                case_name_for_dbg, branches.len());
        }
        // HS-faithful `refineSource` (Sources.hs:123):
        //   map (second (modify sSubst (restrict stableVars)))
        // restricts each branch's eq-store subst to the STABLE vars
        // (frees of the source's `cdGoal`) before dedup.  This
        // narrows the subst to bindings the runtime case-matcher
        // cares about; internal fresh bindings are dropped so
        // equivalent branches dedupe.  Dedup itself is applied ONCE
        // across the flat preDedup list (after the loop, see below).
        // `stable_vars` was computed once before the loop above.
        for (mut branch_sys, branch_name_list) in branches {
            if aggressive_drop && !contradictions(ctx, &branch_sys).is_empty() {
                changed = true;
                continue;
            }
            // Apply `restrict stableVars` to the branch's subst.
            let restricted_pairs: Vec<_> = branch_sys.eq_store.subst.to_list()
                .into_iter()
                .filter(|(v, _)| stable_vars.contains(v))
                .collect();
            branch_sys.invalidate_max_var_idx_cache();
            branch_sys.eq_store_mut().subst =
                tamarin_term::subst::Subst::from_list(restricted_pairs);
            deferred_filtered.push((branch_name_list, branch_sys));
        }
    }
    // HS-faithful `removeRedundantCases` (Sources.hs): applies
    // ONCE to the flat list of post-refine branches across all input
    // cases.  Gated on BP/MSet per HS short-circuit (`removeRedundantCases`
    // in Sources.hs returns the input unchanged outside BP/MSet).
    let msig = ctx.maude.maude_sig();
    // `stable_vars` was computed once before the branch loop above; reuse it.
    if tamarin_utils::env_gate!("TAM_RS_DBG_REMOVE_REDUNDANT") {
        eprintln!("[RRC] === refine source goal={:?} input={} cases ===",
            src.goal, deferred_filtered.len());
    }
    let deduped = remove_redundant_cases(
        msig.enable_bp,
        msig.enable_mset,
        &stable_vars,
        |c| &c.1,
        deferred_filtered,
    );
    new_cases.extend(deduped);
    let count = new_cases.len();
    (new_cases, changed, count)
}

fn saturate_sources_with_simp_opt(
    sources: Vec<Source>,
    limit: usize,
    ctx: &crate::constraint::solver::context::ProofContext,
    aggressive_drop: bool,
) -> Vec<Source> {
    use rayon::prelude::*;
    let mut current = sources;
    let dbg = tamarin_utils::env_gate!("TAM_DBG_REFINE");
    if dbg {
        eprintln!("[refine] starting saturate_sources_with_simp over {} sources",
            current.len());
        for (i, src) in current.iter().enumerate() {
            eprintln!("  source[{}] goal={:?}", i, src.goal);
            for (n, sys) in src.cases_or_empty() {
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
                    for (nid, rule) in sys.nodes.iter() {
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
                    for (g, st) in sys.goals.iter() {
                        eprintln!("      goal solved={} {:?}", st.solved, g);
                    }
                }
            }
        }
    }
    // HS-faithful: ONE pass per saturate iter via `refineSource solver`
    // where `solver = solveAllSafeGoals` (`Sources.hs`).  The
    // `run_solve_all_safe_goals_disj_with_progress` port is the single
    // saturation mechanism, matching HS architecturally — there is no
    // separate chain-fold pre-step (which would materialise branched
    // cases HS only explores lazily inside the Disj monad).
    //
    // ITERATION COUNT — HS applies `refineSource` up to `limit + 1` times
    // when changes persist (Sources.hs:479-498).  HS's `go ths n` computes
    // `ths' = refineSource ths` in its `where` at EVERY call, then:
    //   - guard1 `any changes && n <= limit` → recurse `go ths' (n+1)`;
    //   - guard2 `n > limit`                 → return `ths'` (the final
    //     refinement computed at the n = limit+1 call).
    // So with the default limit=5 and never-converging sources, the
    // recursion runs n=1..5 (5 refinements) THEN makes one more `go` call
    // at n=6 whose `where` computes a 6th `refineSource` and returns it via
    // guard2.  Net: 6 = limit+1 refinements.  Our loop must therefore run
    // `limit + 1` iterations (the early `break` on `!changed` below already
    // mirrors HS's `otherwise` branch returning `ths'` on convergence, so
    // the extra pass only fires when changes never stop — exactly HS's
    // behaviour).  Looping only `limit` times left chaum_offline_anonymity's
    // Ku(sign) source one refinement short (29 vs HS's 33 cases), dropping
    // the deepest nested-blind C_2 source cases.
    for _iter_n in 0..=limit {
        // Haskell-faithful `goodTh` filter (Sources.hs:380-381):
        //
        //   goodTh th = length (getDisj (get cdCases th)) <= 1
        //   solver = solveAllSafeGoals (filter goodTh ths) ...
        //
        // Haskell passes ONLY single-case sources to `solveAllSafeGoals`
        // during refine/saturate.  This is what bounds Haskell's
        // multi-branch refineSource case-set growth.  Without it,
        // multi-branch explodes to 234+ cases for NSPK3 Pre/Secret
        // (vs Haskell's handful), losing the Lowe attack case.  HS always
        // pairs the multi-branch refineSource with this `goodTh` filter.
        let ths_snapshot: Vec<Source> = current.iter()
            .filter(|s| s.cases_len() <= 1)
            .cloned()
            .collect();
        if tamarin_utils::env_gate!("TAM_DBG_TS_SNAP") {
            eprintln!("[ts_snap] iter={} saturated.len={} snapshot.len={}",
                _iter_n, current.len(), ths_snapshot.len());
            for (i, s) in current.iter().enumerate() {
                eprintln!("  saturated[{}] cases={} goal_head={}",
                    i, s.cases_len(),
                    {
                        match &s.goal {
                            crate::constraint::constraints::Goal::Action(_, gfa) =>
                                gfa.terms.first().map(|t| format!("{:?}", t).chars().take(50).collect::<String>()).unwrap_or_default(),
                            crate::constraint::constraints::Goal::Premise(_, gfa) =>
                                format!("Premise({:?})", gfa.tag),
                            _ => "Other".to_string(),
                        }
                    });
            }
        }
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
        // HS-faithful: NO branch cap.  HS `refineSource` collects
        // every Disj-monad branch `runReduction proofStep` yields
        // (Sources.hs:118-133) — there is no bound on the number of
        // output cases.  The old default (50) parked branches as
        // half-refined cases once 50 finished, which is a non-HS
        // mechanism (see TAM_DISJ_OUTER_CAP comment in
        // refine_one_source).  Unconditionally unbounded to match HS.
        let branch_cap: usize = usize::MAX;
        // Haskell-faithful: multi-branch refineSource.
        // Sources.hs's `saturateSources` runs `solveAllSafeGoals`
        // through the `Reduction` monad which is `Disj`-shaped — every
        // branch survives or dies independently via `mzero`.  The
        // surviving branches become separate output cases.
        //
        // Combined with the `goodTh` filter (Sources.hs:380-381),
        // case-set growth is bounded so attack-class lemmas (NSPK3)
        // remain findable via runtime case enumeration.
        // HS-parallel: `lib/theory/src/Theory/Constraint/Solver/Sources.hs`
        //   `any or (changes \`using\` parList rdeepseq)`
        // HS evaluates each source's `refineSource` in parallel and
        // unzips the result into `(changes, ths')`.  We mirror via
        // rayon `par_iter().map(...).collect()` on the per-source body
        // — index-preserved by `collect`, so subsequent code sees the
        // same source ordering as the sequential version.
        //
        // Determinism: the per-source body has no shared mutable state.
        // `set_precompute_mode` is `thread_local!`, so each worker's
        // flag is independent.  `ctx`, `ths_snapshot`, `branch_cap`,
        // `aggressive_drop` are read-only.
        // `run_solve_all_safe_goals_disj_with_progress` builds its own
        // Reduction over an owned System, no aliasing.  Maude IPC
        // serialises via `MaudeHandle::inner` (Arc<Mutex>) — workers
        // queue but don't race.
        // Snapshot the per-source metadata that the post-par-iter loop
        // reads (goal / incomplete / prior case-count) BEFORE moving the
        // sources into the workers.  `collect` preserves index order, so
        // `src_meta[i]` lines up with `per_source[i]`.  This lets us move
        // `current`'s Systems into `refine_one_source` (which consumes
        // them) instead of deep-cloning every source first.
        let src_meta: Vec<(crate::constraint::constraints::Goal, bool, usize)> =
            current.iter()
                .map(|s| (s.goal.clone(), s.incomplete, s.cases_len()))
                .collect();
        let saturated_indexed: Vec<(usize, Source)> =
            std::mem::take(&mut current).into_iter().enumerate().collect();
        // Per-worker MaudePool acquire: if a pool is set on the ctx, each
        // par_iter task borrows its own Maude subprocess for the
        // duration of `refine_one_source`, so workers don't serialise
        // on the single shared `ctx.maude`'s IPC mutex.  Without a
        // pool, every worker shares `ctx.maude` (the pre-pool
        // behaviour; correct but contended).
        //
        // We build a per-task context with the pooled handle swapped
        // in via `ctx.with_swapped_maude(...)`.  The PooledMaude guard
        // releases back to the pool on drop at end of the closure.
        let per_source: Vec<(Vec<(Vec<String>, System)>, bool, usize)> =
            saturated_indexed.into_par_iter().map(|(_i, src)| {
                if let Some(pool) = &ctx.maude_pool {
                    let pooled = pool.acquire();
                    // Give the worker a FRESH counter (not the pooled handle's
                    // accumulating one) so `refine_one_source`'s internal
                    // `ensure_above(avoid_max)` reseeds it to the source's OWN
                    // structural `avoid_max` — producing CANONICAL, source-
                    // local case var idxs (HS `evalFresh (avoid goalTerm)`,
                    // Sources.hs:409).  Without this the case idxs depend on
                    // the pooled handle's reuse history, so the refined-source
                    // cache content (shared across lemmas) becomes
                    // order-dependent and breaks under parallel lemma proving.
                    let task_ctx = ctx.with_swapped_maude(
                        pooled.handle().with_fresh_counter_from(0));
                    refine_one_source(
                        &task_ctx, src, &ths_snapshot, branch_cap,
                        aggressive_drop, dbg,
                    )
                } else {
                    refine_one_source(
                        ctx, src, &ths_snapshot, branch_cap,
                        aggressive_drop, dbg,
                    )
                }
            }).collect();
        for ((new_cases, per_changed, _), meta) in
            per_source.into_iter().zip(src_meta)
        {
            let src_goal_and_incomplete = (meta.0, meta.1);
            let prev_case_count = meta.2;
            if per_changed { changed = true; }
            // Determine if the case count changed for this source.
            let new_case_count = new_cases.len();
            if dbg {
                eprintln!("[refine] source goal={:?} -> {} output cases:",
                    src_goal_and_incomplete.0, new_case_count);
                let mut name_counts: std::collections::BTreeMap<String, usize>
                    = std::collections::BTreeMap::new();
                for (n, _) in &new_cases {
                    *name_counts.entry(case_name_list_to_string(n)).or_insert(0) += 1;
                }
                for (n, c) in &name_counts {
                    eprintln!("[refine]   {}: {}", n, c);
                }
                // Per-case node/edge counts for diagnostic.
                for (n, sys) in &new_cases {
                    eprintln!("[refine]   case {:?}: {} nodes, {} edges, {} goals",
                        n, sys.nodes.len(), sys.edges.len(), sys.goals.len());
                    if tamarin_utils::env_gate!("TAM_DBG_REFINE_VERBOSE") {
                        let nm = case_name_list_to_string(n);
                        if nm.starts_with("Resolve1") || nm.starts_with("Resolve2") {
                            eprintln!("[refine]     nodes:");
                            for (id, rule) in sys.nodes.iter() {
                                let rname = match &rule.info {
                                    crate::rule::RuleInfo::Proto(p) =>
                                        format!("Proto({:?})", p.name),
                                    crate::rule::RuleInfo::Intr(i) =>
                                        format!("Intr({:?})", i),
                                };
                                eprintln!("[refine]       {}_{}: {}", id.name, id.idx, rname);
                            }
                            eprintln!("[refine]     edges:");
                            for e in &sys.edges {
                                eprintln!("[refine]       {}_{} ConcIdx({}) -> {}_{} PremIdx({})",
                                    e.src.0.name, e.src.0.idx, e.src.1.0,
                                    e.tgt.0.name, e.tgt.0.idx, e.tgt.1.0);
                            }
                            eprintln!("[refine]     unsolved goals:");
                            for (g, st) in sys.goals.iter() {
                                if !st.solved {
                                    let gs = format!("{:?}", g).chars().take(500).collect::<String>();
                                    eprintln!("[refine]       {}", gs);
                                }
                            }
                            eprintln!("[refine]     i_0 node detail:");
                            for (id, rule) in sys.nodes.iter() {
                                if &*id.name == "i" {
                                    eprintln!("[refine]       i_{} acts: {:?}", id.idx,
                                        rule.actions);
                                }
                            }
                            eprintln!("[refine]     eq_store conj:");
                            for (i, d) in sys.eq_store.conj.iter().enumerate() {
                                eprintln!("[refine]       disj[{}] split_id={:?} substs={}",
                                    i, d.split_id, d.substs.len());
                            }
                            eprintln!("[refine]     eq_store subst (LVar → term):");
                            for (v, t) in sys.eq_store.subst.to_list() {
                                let ts = format!("{:?}", t).chars().take(100).collect::<String>();
                                eprintln!("[refine]       {}_{}:{:?} → {}",
                                    v.name, v.idx, v.sort, ts);
                            }
                            eprintln!("[refine]     less_atoms:");
                            for la in &sys.less_atoms {
                                eprintln!("[refine]       {}_{} < {}_{} ({:?})",
                                    la.smaller.name, la.smaller.idx,
                                    la.larger.name, la.larger.idx,
                                    la.reason);
                            }
                        }
                    }
                }
            }
            // HS-faithful `refineSource` (Sources.hs:131-133):
            //   refineSource ctxt proofStep th = (..., set cdCases newCases th)
            // and `saturateSources` (Sources.hs:498):
            //   (changes, ths') = unzip $ map (refineSource ctxt solver) ths
            // ALWAYS returns one source per input — `set cdCases newCases th`
            // REPLACES the case list, even when it is EMPTY (every branch
            // mzero'd).  Sources are NEVER dropped; the count is constant
            // (`[SAT-FINAL] sources=N` stays fixed) and only `cdCases` shrinks.
            //
            // Previously RS DROPPED a source whose refine produced 0 cases
            // (the `else` only set `changed`, never pushing to `next`).  That
            // left the source absent from `current`/`refined`, so
            // `ensure_saturated`'s match-by-goal (context.rs) found nothing
            // and LEFT THE STALE *INITIAL* CASES in the cell.  For a builtin
            // destructor like `check_rep`/`get_rep` (locations-report) the
            // initial `coerce` case carries an unsolvable `KD(check_rep(..))`
            // premise; HS solves that KD-premise during saturation, finds no
            // source (nothing outputs `check_rep`), contradicts the branch,
            // and ends with `cdCases = []`.  RS instead kept the coerce case,
            // so during the lemma proof `KU(check_rep(..))` opened the
            // coerce → KD → chain subtree HS prunes — inflating the
            // locations-report SAPiC theories' proofs (AKE can_run_v: 9 HS
            // steps vs 21 RS; SOC/OTP/AC likewise).  Keep the empty-case
            // source so the cell is overwritten to empty, matching HS's
            // `by solve( !KU( check_rep(..) ) )` (zero open cases).
            let new_cases_empty = new_cases.is_empty();
            next.push(Source::eager_list(src_goal_and_incomplete.0, new_cases, src_goal_and_incomplete.1));
            if new_cases_empty {
                changed = true;
            }
            if new_case_count > prev_case_count {
                changed = true;
            }
            // HS-faithful fixpoint: if case_count went DOWN or stayed,
            // this source is at fixpoint (HS's `change = not (null
            // names)` would be False here — solveAllSafeGoals reached
            // a state where no more steps progress).  Don't trigger
            // another iter because of a count drop — that was the
            // saturate over-iteration that killed PRF's C_2/S_2 chain
            // cases at iter 3 in TLS_Handshake.  See [project_prf_source_cache_undercount].
        }
        current = next;
        if !changed { break; }
    }
    // HS-faithful final-truncate pass: applies `combine` one more
    // time per case with empty `new_names`, which (per Sources.hs:139
    // `combine (n:_) _ = [n]`) truncates any multi-element name list
    // to its first non-coerce element.  HS's saturate normally
    // achieves this via iter-2's `combine names names'` on iter-1's
    // multi-element output, but Rust's change-detection skips iter-2
    // when only safe-goal steps fired (avoiding PRF over-refinement —
    // see [[project-prf-source-cache-undercount]]).  Applying the
    // truncate as a name-only pass matches HS's final case-name
    // display without re-running solveAllSafeGoals.
    for src in current.iter_mut() {
        if let Some(cases) = src.cases_cell.lock().unwrap().as_mut() {
            for (name_list, _) in cases.iter_mut() {
                if name_list.len() > 1 {
                    let truncated = combine_case_names_list(name_list, &[]);
                    *name_list = truncated;
                }
            }
        }
    }
    current
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
/// - `outer_cap` bounds the per-branch saturate iterations.
/// - `branch_cap` caps total output branches.  When exceeded, alive
///   branches are pushed to finished with their accumulated state.
///
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
    let init = string_to_name_list(&initial_name);
    run_solve_all_safe_goals_disj(ctx, initial_sys, &[],
        chains_limit, outer_cap, branch_cap, init)
        .into_iter()
        .map(|(sys, n)| (sys, case_name_list_to_string(&n)))
        .collect()
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
    let init = string_to_name_list(&initial_name);
    run_solve_all_safe_goals_disj(ctx, initial_sys, ths,
        chains_limit, outer_cap, branch_cap, init)
        .into_iter()
        .map(|(sys, n)| (sys, case_name_list_to_string(&n)))
        .collect()
}

/// Read the K(U|D) conclusion term of `c` from `sys` — mirrors HS
/// `kConcTerm` (Sources.hs:220-225): returns Some only when the
/// node's conclusion fact at `c.1` is a KU or KD fact.  Module-level
/// helper used by `run_solve_all_safe_goals_disj_with_progress`'s
/// `lastChainTerm` filter.
fn k_conc_term_for_chain(
    sys: &crate::constraint::system::System,
    c: &crate::constraint::constraints::NodeConc,
) -> Option<tamarin_term::lterm::LNTerm> {
    use crate::fact::FactTag;
    let (id, idx) = (&c.0, &c.1);
    let rule = sys.nodes.iter().find(|(n, _)| n == id).map(|(_, r)| r)?;
    let fact = rule.conclusions.get(idx.0)?;
    if !matches!(fact.tag, FactTag::Ku | FactTag::Kd) { return None; }
    fact.terms.first().cloned()
}

/// Structural equality modulo fresh variable renaming.  Mirrors HS
/// `eqModuloFreshnessNoAC` (LTerm.hs:632).  Two terms are equal iff
/// they're structurally identical after renaming every free var to a
/// fresh canonical name preserving ONLY sort.
fn eq_modulo_freshness_no_ac(
    a: &tamarin_term::lterm::LNTerm,
    b: &tamarin_term::lterm::LNTerm,
) -> bool {
    use tamarin_term::lterm::LVar;
    use std::collections::HashMap;
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
                    && xs.iter().zip(ys.iter()).all(|(x, y)| go(x, y, ma, mb, next)),
            _ => false,
        }
    }
    let mut ma = HashMap::new();
    let mut mb = HashMap::new();
    let mut next = 0;
    go(a, b, &mut ma, &mut mb, &mut next)
}

fn run_solve_all_safe_goals_disj(
    ctx: &crate::constraint::solver::context::ProofContext,
    initial_sys: System,
    ths: &[Source],
    chains_limit: i64,
    outer_cap: i64,
    branch_cap: usize,
    initial_name: Vec<String>,
) -> Vec<(System, Vec<String>)> {
    run_solve_all_safe_goals_disj_with_progress(
        ctx, initial_sys, ths, chains_limit, outer_cap, branch_cap, initial_name).0
}

// --- Cached kill-switch / debug env flags for the saturation worklist ---
// `run_solve_all_safe_goals_disj_with_progress`'s `while let` loop is the
// core saturation explorer (up to `branch_cap*50` ~ 2000+ iterations per
// call, once per source per saturate iter).  These env vars are constant
// for the process, so cache each behind a `OnceLock<bool>` (mirroring
// `trace::flag()`) instead of re-reading the environment per branch.
#[inline]
fn sas_dbg_branch_state() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("TAM_RS_DBG_BRANCH_STATE").is_ok())
}
#[inline]
fn sas_dbg_branch_drop() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("TAM_DBG_BRANCH_DROP").is_ok())
}
#[inline]
fn sas_iter_trace() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("TAM_RS_SAS_ITER").is_ok())
}
#[inline]
fn disj_refine_trace() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("TAM_DISJ_REFINE_TRACE").is_ok())
}
#[inline]
fn dbg_useful_kus() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("TAM_DBG_USEFUL_KUS").is_ok())
}
/// Variant that also returns a flag indicating whether ANY branch took
/// at least one solve step (safe-goal solve or source-pick).  This is
/// HS-faithful `not (null names)` from `solveAllSafeGoals`'s `caseNames`
/// accumulator — the signal that drives `saturateSources`'s outer-iter
/// "changes" detection.  Without this signal Rust's saturate exits too
/// early on cases like chaum's St_S_1 where a single source-pick on a
/// later iter is needed to converge KU(~x:Fresh-Var) source-cache to
/// 1 case (HS-faithful) rather than 2.
/// See [[project-chaum-case-fresh-divergence]].
fn run_solve_all_safe_goals_disj_with_progress(
    ctx: &crate::constraint::solver::context::ProofContext,
    initial_sys: System,
    ths: &[Source],
    chains_limit: i64,
    outer_cap: i64,
    branch_cap: usize,
    initial_name: Vec<String>,
) -> (Vec<(System, Vec<String>)>, bool) {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::contradictions::contradictions;
    use crate::constraint::solver::goals::dispatch_solve_goal;
    use crate::constraint::solver::reduction::{
        GoalCases, Reduction, SolveOutcome, SplitStrategy};
    use crate::constraint::solver::simplify::simplify_system_with_fanout;
    use crate::fact::FactTag;

    // HS-faithful: track step names as a Vec<String> — HS's
    // `caseNames` (the `solve` parameter at Sources.hs:175) is `[String]`
    // (type at Sources.hs:144).  At finish we
    // apply HS's `combine` (Sources.hs:135-139) to merge with the
    // existing case-name list from `initial_name`:
    //
    //   refineSource ctxt proofStep th =
    //     refinement = do
    //       (names, se)        <- get cdCases th
    //       ((x, names'), se') <- fst <$> runReduction proofStep ctxt se fs
    //       return (x, (combine names names', se'))
    //
    // The `Vec<String>` representation lets `combine` truncate to the
    // first non-coerce element exactly as HS does — preserving the
    // list boundary `(n:_)` pattern instead of losing it via
    // concatenation.  Without this, `combine` can't tell where one
    // step name ends and the next begins, so Rust accumulated
    // multi-step names ("Step1sencSetup_Key") that HS truncated to
    // single element ("Step1") at the refineSource boundary.
    // `last_chain_term`: tracks the most recently solved Chain's
    // conclusion term.  Mirrors HS `solveAllSafeGoals.solve`'s
    // `lastChainTerm :: Maybe LNTerm` parameter (Sources.hs:175-211).
    // Used to filter out chain goals whose conclusion is equal modulo
    // freshness to the last solved one — loop-breaker that prevents
    // user-equation destructor explosions.  Lead A from agent #35.
    // The trailing `bool` is the per-branch `took_step` flag: True iff
    // this branch (or an ancestor) dispatched a solve-step.  Mirrors
    // HS's per-Disj-branch `names` accumulator — a branch's step-taken
    // flag is only observed if the branch SURVIVES to a leaf, since
    // HS's `changes = map fst (getDisj refinement)` collects `x = not
    // (null names)` ONLY from surviving Disj branches (Sources.hs:118-
    // 133).  A branch that takes a step then mzero's contributes
    // nothing.  (Previously RS used a single mutable `any_step_taken`
    // set on ANY step incl. branches that later die — an over-count
    // that drove an EXTRA saturate iteration vs HS, collapsing e.g.
    // TLS_Handshake's PRF C_2/S_2 deconstruction cases that HS keeps.)
    type Entry = (System, Vec<String> /* step_names accumulator */,
                  std::collections::BTreeSet<String>, i64, i64,
                  Option<tamarin_term::lterm::LNTerm> /* last_chain_term */,
                  bool /* took_step */);
    let mut worklist: Vec<Entry> = vec![
        (initial_sys, Vec::new() /* fresh accumulator for steps */,
         std::collections::BTreeSet::new(),
         chains_limit, outer_cap, None /* last_chain_term */, false)
    ];
    // `finished` holds (System, accumulated_step_names_list).
    // `combine` runs with `initial_name` after the loop terminates.
    let mut finished: Vec<(System, Vec<String>)> = Vec::new();
    // HS-faithful `not (null names)` progress flag: True iff some
    // SURVIVING branch dispatched a solve-step.  Accumulated only at
    // `finished.push` (a branch reaching a leaf) — see the per-branch
    // `took_step` field on `Entry`.  This drives the outer saturate's
    // "changes" detection (Sources.hs:362-384; `not (null names)` from
    // solveAllSafeGoals returning caseNames, 213-215).
    let mut any_step_taken: bool = false;
    // outer_cap / branch_cap are hardcoded to MAX (the HS-faithful
    // unbounded default; the env knobs were removed), so the two guards
    // below are inert — the real bounds are chains_left (HS chainsLeft=10)
    // and the outer saturation limit (paramSaturationLimit=5).
    let mut total_steps: usize = 0;
    let total_step_cap: usize = branch_cap.saturating_mul(50).max(2000);

    while let Some((sys, name, used, chains_left, iters_left, last_chain_term, took_step)) = worklist.pop() {
        total_steps += 1;
        if total_steps > total_step_cap {
            any_step_taken |= took_step;
            finished.push((sys, name));
            continue;
        }
        if finished.len() + 1 > branch_cap || iters_left <= 0 {
            any_step_taken |= took_step;
            finished.push((sys, name));
            continue;
        }

        // HS-faithful `simplifySystem` in DisjT (Sources.hs:222):
        //   simplifySystem
        //   ctxt <- ask
        //   isContra <- gets (contradictorySystem ctxt)
        //   contradictoryIf isContra
        //
        // HS's `Reduction = StateT (DisjT ...)` means any Disj-monad
        // fan-out inside `simplifySystem` (e.g. internal `solveAction`
        // on KU/KD goals, or `solveTermEqs SplitNow` AC-arms in
        // `enforce_*_uniqueness`) SPLITS the current state into
        // sibling branches BEFORE the contradictoryIf check.  Each
        // sibling proceeds independently through the rest of
        // `solveAllSafeGoals.solve`.
        //
        // Previously RS called `simplify_system(&mut red)` (in-place)
        // here, dropping any Disj fan-out on the floor.  That collapsed
        // N HS-siblings into 1 RS branch — exact same pattern as the
        // 2026-06-07 `simplify_system_with_fanout` landing in
        // `exec_proof_method` (memory entry `a0ae5655`).  We need the
        // SAME fan-out propagation here in `solveAllSafeGoals.solve`.
        //
        // Strategy: split into N sibling systems, push the tail back
        // onto worklist with same (name, used, chains_left, iters_left,
        // last_chain_term), and process the head.  Empty result drops
        // the branch (HS mzero-equivalent).
        // HS-faithful: propagate the DisjT fan-out from simplifySystem
        // (unconditional).
        let post_simp: Vec<System> = simplify_system_with_fanout(ctx, sys);
        // Pop one sibling to continue with; push the rest back for
        // later processing.  Match HS's Disj-monad insertion order:
        // first sibling processed first (LIFO worklist → push tail
        // reversed so the head pops next).
        let sys = match post_simp.len() {
            0 => continue, // all siblings contradictory / dropped
            1 => post_simp.into_iter().next().unwrap(),
            _ => {
                let mut iter = post_simp.into_iter();
                let head = iter.next().unwrap();
                let tail: Vec<System> = iter.collect();
                for sib in tail.into_iter().rev() {
                    worklist.push((sib, name.clone(), used.clone(),
                        chains_left, iters_left, last_chain_term.clone(), took_step));
                }
                head
            }
        };
        let mut red = Reduction::new(ctx, sys);
        let contras = contradictions(red.ctx, &red.sys);
        // TAM_RS_DBG_BRANCH_STATE=1 dumps state for ALL branches (not just dropped).
        // Use it to find why a chain-based sub-case isn't dropping when HS would.
        if sas_dbg_branch_state()
            && name.iter().any(|s| s.contains("Resolve2") || s.contains("Resolve1"))
        {
            let chains: Vec<_> = red.sys.goals.iter().filter_map(|(g, st)|
                if !st.solved {
                    if let Goal::Chain(c, p) = g {
                        let cf = red.sys.nodes.iter().find(|(id, _)| id == &c.0)
                            .and_then(|(_, r)| r.conclusions.get(c.1.0));
                        let pf = red.sys.nodes.iter().find(|(id, _)| id == &p.0)
                            .and_then(|(_, r)| r.premises.get(p.1.0));
                        Some(format!("Chain({:?}.{:?} → {:?}.{:?}): {:?} → {:?}",
                            c.0.name, c.0.idx, p.0.name, p.0.idx, cf, pf))
                    } else { None }
                } else { None }).collect();
            let ku_acts: Vec<_> = red.sys.goals.iter().filter_map(|(g, st)|
                if !st.solved {
                    if let Goal::Action(id, fa) = g {
                        if matches!(fa.tag, FactTag::Ku) {
                            Some(format!("KU@{:?}.{:?}: {:?}", id.name, id.idx, fa.terms.first()))
                        } else { None }
                    } else { None }
                } else { None }).collect();
            let subst: Vec<_> = red.sys.eq_store.subst.to_list().iter()
                .map(|(v, t)| format!("{:?}_{} → {:?}",
                    v.name, v.idx, format!("{:?}", t).chars().take(100).collect::<String>()))
                .collect();
            let conj: Vec<_> = red.sys.eq_store.conj.iter().enumerate()
                .map(|(i, d)| {
                    let s_list: Vec<String> = d.substs.iter().enumerate()
                        .map(|(j, s)| {
                            let l: Vec<String> = s.to_list().iter()
                                .map(|(v, t)| format!("{}.{}:{:?} → {}",
                                    v.name, v.idx, v.sort,
                                    format!("{:?}", t).chars().take(300).collect::<String>()))
                                .collect();
                            format!("subst[{}]: {:#?}", j, l)
                        }).collect();
                    format!("disj[{}] sid={:?}: {:#?}", i, d.split_id, s_list)
                }).collect();
            eprintln!("[RS-SAT-STATE] name={:?} contras={:?}\n  subst={:#?}\n  conj={:#?}\n  chains={:#?}\n  ku_acts={:#?}",
                name, contras, subst, conj, chains, ku_acts);
        }
        if !contras.is_empty() {
            if sas_dbg_branch_drop() {
                eprintln!("[branch_drop] name={:?} dropped by contras: {:?}",
                    name, contras.iter().map(|c| format!("{:?}", c).chars().take(40).collect::<String>()).collect::<Vec<_>>());
            }
            // Haskell mzero — drop branch (don't push to finished).
            continue;
        }

        // Pick a goal — mirrors the saturate goal-pick logic.
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
        // HS-faithful `lastChainTerm` filter (Sources.hs:182-186):
        //   filterM (\(g,_) -> case g of
        //     (ChainG c _) -> (\x -> return $ Just True /=
        //                       liftM2 eqModuloFreshnessNoAC lastChainTerm x)
        //                     =<< kConcTerm c
        //     _            -> return True) goals
        //
        // Drops chain goals whose K-conclusion term is equal modulo
        // freshness to the previously solved chain's conclusion — the
        // loop-breaker that prevents user-equation destructor
        // explosions.  Without this `lastChainTerm` filter here,
        // MTI_C0 saturate iter 0 exhausts chains that HS leaves
        // open (after lastChainTerm filter) — adding the filter
        // restores the open Chain/Split goals HS picks up at iter 1
        // and drops via solveChain's forbiddenEdge / illegalCoerce /
        // isMsgVar plus solveSplit's eqsIsFalse.
        // HS-faithful `lastChainTerm` chain-goal filter (Sources.hs:182-186),
        // applied unconditionally.
        let filtered_goals: Vec<(Goal, bool)> = goals.iter().filter(|(g, _)| {
                match g {
                    Goal::Chain(c, _) => {
                        let this_t = k_conc_term_for_chain(&red.sys, c);
                        // HS: `Just True /= liftM2 eqModuloFreshnessNoAC last this`
                        // Drop iff `last` is Some AND `this` is Some AND
                        // they're equal-mod-freshness.  Keep otherwise.
                        match (last_chain_term.as_ref(), this_t.as_ref()) {
                            (Some(lt), Some(tt)) => !eq_modulo_freshness_no_ac(lt, tt),
                            _ => true,
                        }
                    }
                    _ => true,
                }
            }).cloned().collect();
        // Unfiltered chains view — Haskell's `unsolvedChains`.
        let any_unsolved_chain = red.sys.goals.iter().any(|(g, st)|
            !st.solved && matches!(g, Goal::Chain(_, _)));
        let any_chain_goal = goals.iter()
            .any(|(g, _)| matches!(g, Goal::Chain(_, _)));
        // TAM_RS_SAS_ITER=1: per-solve-step trace mirroring HS's
        // [HS_SAS_ITER] (Sources.hs:175-215).  Lets the PRF/senc
        // deconstruction-chain trajectories be diffed HS↔RS.
        if sas_iter_trace() {
            let n_chains = red.sys.goals.iter().filter(|(g, st)|
                !st.solved && matches!(g, Goal::Chain(_, _))).count();
            let kinds: Vec<String> = goals.iter().map(|(g, _)| match g {
                Goal::Action(_, fa) => format!("Act-{:?}", fa.tag),
                Goal::Premise(_, fa) => format!("Prem-{:?}", fa.tag),
                Goal::Chain(_, _) => "Chain".to_string(),
                Goal::Disj(_) => "Disj".to_string(),
                Goal::Split(_) => "Split".to_string(),
                Goal::Subterm(_) => "Subterm".to_string(),
            }).collect();
            eprintln!("[RS_SAS_ITER] cn={:?} goals={} chains={} chainsLeft={} goalKinds={:?}",
                name, goals.len(), n_chains, chains_left, kinds);
        }
        let split_allowed = !any_chain_goal && any_unsolved_chain;
        // Haskell parity (Sources.hs:169-170, 159).
        let is_kd_prem = |g: &Goal| -> bool {
            matches!(g, Goal::Premise(_, fa)
                if fa.tag == FactTag::Kd && !crate::fact::is_kd_xor_fact(fa))
        };
        let is_chain_prem1 = |g: &Goal| -> bool {
            matches!(g, Goal::Chain(_, (_, pi)) if pi.0 == 1)
        };
        // HS-faithful: HS's `safeGoal` predicate (Sources.hs:175-188)
        // marks Split/Disj/Subterm safe when `splitAllowed`.  Split is
        // allowed during saturate when `splitAllowed` (HS's
        // `safeGoal SplitG = doSplit`, Sources.hs:162/194), regardless
        // of precompute/runtime.  In practice split_allowed is rarely
        // true during saturate (chain goals stay open), so this is a
        // no-op for most cases — but it is the HS-faithful behaviour.
        let is_safe = |g: &Goal| -> bool {
            match g {
                Goal::Chain(_, _) => chains_left > 0,
                Goal::Action(_, fa) => !matches!(fa.tag, FactTag::Ku),
                Goal::Premise(_, fa) => {
                    !matches!(fa.tag, FactTag::Ku)
                        && !crate::fact::is_kd_xor_fact(fa)
                        && !fa.is_no_sources()
                }
                Goal::Disj(_) | Goal::Subterm(_) => split_allowed,
                // HS-faithful: `safeGoal SplitG = doSplit = splitAllowed`
                // (Sources.hs:162/194).
                Goal::Split(_) => split_allowed,
            }
        };
        // HS-faithful: kdPremGoals uses UNFILTERED goals (Sources.hs:200),
        // safeGoals uses FILTERED (line 195).  Match HS by deriving each
        // candidate from the correct source.
        let pick = goals.iter()
            .find(|(g, _)| is_kd_prem(g) || is_chain_prem1(g))
            .or_else(|| filtered_goals.iter().find(|(g, _)| is_safe(g)));
        // HS-faithful update of `lastChainTerm'` (Sources.hs:209-211):
        //   case (kdPremGoals, safeGoals) of
        //     ([], ((ChainG c _):_)) -> ... (t <|> lastChainTerm) =<< kConcTerm c
        //     _                      -> return lastChainTerm
        // Update when no kd-prem goals exist AND first safe goal is a
        // Chain.  HS: `t <|> lastChainTerm` keeps the existing value if
        // the new chain has no K-term (`kConcTerm` returns Nothing).
        let kd_prem_empty = !goals.iter().any(|(g, _)| is_kd_prem(g) || is_chain_prem1(g));
        let first_safe = filtered_goals.iter().find(|(g, _)| is_safe(g));
        let new_last_chain_term = if kd_prem_empty {
            if let Some((Goal::Chain(c, _), _)) = first_safe {
                let t = k_conc_term_for_chain(&red.sys, c);
                // `t <|> lastChainTerm`: prefer new t, else keep old.
                t.or(last_chain_term.clone())
            } else {
                last_chain_term.clone()
            }
        } else {
            last_chain_term.clone()
        };

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
                    // HS-faithful change flag: a safe-goal step IS a step
                    // (`names` grows via `caseNames ++ x`, so `not (null
                    // names)` is True — Sources.hs:214-215).  The
                    // outer `saturateSources` re-iterates on ANY step, not
                    // just source-picks.  (The prior `any_step_taken`-only-
                    // on-source-pick behaviour was a non-HS workaround that
                    // converged refined saturation prematurely, leaving
                    // deconstruction cases — e.g. chaum's pk C_2 cases —
                    // un-collapsed because they never got driven to their
                    // typing-contradiction mzero.)
                    // HS-faithful: mark THIS branch as having taken a step;
                    // it only counts if the branch survives to a leaf.
                    worklist.push((red.sys, name, used,
                        new_chains_left, iters_left - 1, new_last_chain_term.clone(), true));
                }
                GoalCases::LinearNamed(sub_name) => {
                    // HS-faithful: INSIDE `solveAllSafeGoals.solve`
                    // (Sources.hs:214-215), step names are APPENDED
                    // via `caseNames ++ x` — not combined via the
                    // coerce-skipping `combine`.  `combine` runs at
                    // `refineSource` level once per saturate-outer
                    // iter (between calls to solveAllSafeGoals), not
                    // per step within solveAllSafeGoals.
                    // HS-faithful change flag: a named safe-goal step is a
                    // step → `not (null names)` True → outer saturate
                    // re-iterates (Sources.hs:214-215).  The prior
                    // "only source-pick steps mark progress" was a non-HS
                    // workaround introduced to suppress a TLS_Handshake/PRF
                    // C_2/S_2 over-refinement; that masked, rather than
                    // fixed, the over-refinement AND broke refined-source
                    // convergence (deconstruction cases like chaum's pk
                    // C_2 never reached their typing-contradiction mzero,
                    // so pk stayed non-goodTh and c_pk was never grafted).
                    // Restoring HS faithfulness here; any TLS/PRF fallout
                    // is a SEPARATE faithfulness bug to fix on its own.
                    let mut new_name = name.clone();
                    append_step_name_list(&mut new_name, &sub_name);
                    worklist.push((red.sys, new_name, used,
                        new_chains_left, iters_left - 1, new_last_chain_term.clone(), true));
                }
                GoalCases::Cases(cases) => {
                    // Multi-output — fork.  Each case's System
                    // becomes a new alive branch.
                    //
                    // HS-faithful insertion-order processing:
                    // worklist is Vec-as-stack (LIFO), so naive
                    // push pops branches in REVERSE order.  HS's
                    // Disj-monad is depth-first INSERTION order.
                    // Reverse the cases when pushing so subsequent
                    // `worklist.pop()` calls fire them in the
                    // original [direct, destructor1, destructor2, ...]
                    // order from `solveChain` (Goals.hs:316-380),
                    // matching HS's case ordering at NSPK3/NSLPK3
                    // types and similar source-saturated lemmas.
                    //
                    // HS-faithful change flag: a forking safe-goal step is a
                    // step → each forked branch inherits took_step=true; it
                    // only counts toward `changes` if that branch survives.
                    let case_vec: Vec<_> = cases.into_iter().collect();
                    for (sub_name, case_sys) in case_vec.into_iter().rev() {
                        let mut new_name = name.clone();
                        append_step_name_list(&mut new_name, &sub_name);
                        worklist.push((case_sys, new_name, used.clone(),
                            new_chains_left, iters_left - 1, new_last_chain_term.clone(), true));
                    }
                }
            }
            continue;
        }

        // No safe goal — try source-pick (Haskell's third disjunct
        // of `nextStep`, line 205).
        if ths.is_empty() {
            any_step_taken |= took_step;
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
        // HS-faithful `usefulGoal` filter (Goals.hs:115-123 + Sources.hs:212-213):
        // HS only source-picks KU goals tagged `Useful`.  KU goals tagged
        // `CurrentlyDeducible` / `ProbablyConstructible` / `LoopBreaker`
        // are NOT in `usefulGoals` → source-pick skips them, leaving
        // them as open goals.  Bare-Msg-var KU goals (e.g. `KU(x.13)`
        // from a destructor's KU(x) premise) get `ProbablyConstructible`,
        // NOT `Useful`, so HS does NOT source-pick on them.  Without this
        // filter, RS recursively source-picks on these abstract vars,
        // fanning Chen_Kudla's KU(pmult) into 21+ over-saturated cases
        // (vs HS's 9).  See agent #31 diagnosis.
        //
        // Haskell-faithful `filterCases` (Sources.hs:218-219):
        // skip useful_kus whose source LABEL is already in `used` —
        // picking a case from Source S consumes S entirely, not just
        // the picked case-name.  See `ku_source_label_for_fa`.
        use crate::constraint::solver::annotated_goals::Usefulness;
        let useful_kus: Vec<(crate::constraint::constraints::NodeId,
                              crate::fact::LNFact)> =
            goals.iter().filter_map(|(g, looping)| match g {
                Goal::Action(i, fa) if matches!(fa.tag, FactTag::Ku) => {
                    // HS-faithful: only `Useful`-tagged KU goals.
                    if crate::constraint::solver::goals::goal_usefulness(
                        g, *looping, &red.sys) != Usefulness::Useful
                    {
                        return None;
                    }
                    if let Some(label) = ku_source_label_for_fa(fa) {
                        if used.contains(&label) { return None; }
                    }
                    Some((i.clone(), fa.clone()))
                }
                _ => None,
            }).collect();
        if useful_kus.is_empty() {
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        }
        let avoid_max = system_max_idx(&red.sys);
        let trace = disj_refine_trace();
        // Iterate useful goals in order; first one with a matching
        // source wins (Haskell `asum`).
        let mut picked: Option<(crate::constraint::constraints::NodeId,
                                crate::fact::LNFact,
                                Vec<(String,
                                     crate::constraint::system::System,
                                     crate::fact::LNFact)>)> = None;
        // TAM_DBG_USEFUL_KUS=1: dumps useful_kus + ths content + source-pick results
        // per branch.  Used to diagnose source-availability divergences vs HS.
        // See [[project-h17-2-resolve1-narrowing-mechanism]].
        let dbg_useful = dbg_useful_kus();
        if dbg_useful {
            eprintln!("[useful_kus] name={:?} n={} used={:?} ths_count={}",
                name, useful_kus.len(), used, ths.len());
            for (idx, src) in ths.iter().enumerate() {
                let kind = match &src.goal {
                    Goal::Action(_, gfa) => format!("Action({:?})", gfa.tag),
                    Goal::Premise(_, gfa) => format!("Premise({:?})", gfa.tag),
                    Goal::Chain(_, _) => "Chain".to_string(),
                    Goal::Disj(_) => "Disj".to_string(),
                    Goal::Subterm(_) => "Subterm".to_string(),
                    Goal::Split(_) => "Split".to_string(),
                };
                let pat = match &src.goal {
                    Goal::Action(_, gfa) | Goal::Premise(_, gfa) => {
                        gfa.terms.first().map(|t| format!("{:?}",t).chars().take(60).collect::<String>()).unwrap_or_default()
                    }
                    _ => String::new(),
                };
                eprintln!("  ths[{}] kind={} pat={}", idx, kind, pat);
            }
            for (i, fa) in &useful_kus {
                let head = fa.terms.first().map(|t| format!("{:?}",t).chars().take(80).collect::<String>()).unwrap_or_default();
                eprintln!("  candidate i={:?} fa_head={}", i, head);
            }
        }
        for (i_cand, fa_cand) in useful_kus {
            let case_pairs_opt = solve_with_source_cases_action(
                ths, &red.sys, &i_cand, &fa_cand, avoid_max);
            if dbg_useful {
                let n = case_pairs_opt.as_ref().map(|cp| cp.len()).unwrap_or(usize::MAX);
                let head = fa_cand.terms.first().map(|t| format!("{:?}",t).chars().take(80).collect::<String>()).unwrap_or_default();
                eprintln!("  tried fa_head={} result={}", head,
                    if n == usize::MAX { "None".to_string() } else { format!("Some({})", n) });
            }
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
                eprintln!("[disj-refine] name={:?} -- no goal had matching source", name);
            }
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        };
        if trace {
            let names: Vec<&str> = case_pairs.iter().map(|(n, _, _)| n.as_str()).collect();
            eprintln!("[disj-refine] name={:?} i={:?} -- {} cases: {:?}",
                name, i, case_pairs.len(), names);
        }
        // Source-label-based filter (Haskell-faithful): the picked
        // useful_ku's source label was verified NOT in `used` above,
        // so all case_pairs from this single source are available.
        // No per-case-name filter needed.
        if case_pairs.is_empty() {
            // No candidates returned by solve_with_source_cases_action
            // — surface as survivor (Haskell's asum returns [] here).
            if trace {
                eprintln!("[disj-refine] name={:?} -- ALL USED", name);
            }
            any_step_taken |= took_step;
            finished.push((red.sys, name));
            continue;
        }

        // Fork: try each viable candidate as a separate branch.
        // Mirrors Haskell `asum [solveWithSourceAndReturn ctxt ths g
        // | g <- usefulGoals]` — collects all branches that survive.
        let mut any_branched = false;
        for (case_name, sys_cand, case_action) in case_pairs {
            // Graft path: caller runs solve_fact_eqs(action) +
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

            // HS-faithful (Sources.hs): `_applySource` calls
            // `markGoalAsSolved "precomputed" goal` BEFORE conjoining
            // the case body.  The legacy graft path above does the
            // conjoin via `solve_with_source_cases_action` (which
            // produces `sys_cand`) but never marks the LIVE KU action
            // goal solved in the resulting system.  Without this, the
            // outer saturate packages this system into a source case
            // carrying an OPEN `KU(~x:Fresh)` entry — which at runtime
            // becomes a top-ranked goal (slot 7 FreshKnows) before the
            // sign-KU (slot 10 Signature), causing chaum's
            // unforgeability proof to take an extra `case fresh` step
            // HS never takes.  Mirror HS by marking the goal solved
            // after the case body is merged in.
            //
            // NARROWING: only mark when the KU term contains a Fresh
            // variable.  HS-empirically: pure-public KU terms
            // (`KU(S(myzero))`, `KU(S(S(myzero)))` in Yubi
            // Login_reachable) end up dispatched at runtime as
            // `case c_S` proof steps — HS's saturate-time mark-solved
            // for these doesn't propagate across the conjoin boundary
            // (saturate-abstract-node and live-runtime-node never
            // collide for pure-public terms).  Mark-solved-and-
            // propagate happens for KU terms carrying a Fresh var
            // (`KU(~x:Fresh)` in chaum, `KU(pcs(~k))` in StatVerif)
            // because the substGoals-narrowing path or pair-decomp
            // path that put them into the live system also reused the
            // saturate-abstract node-id.  The Fresh-bearing check
            // approximates this collision pattern faithfully:
            // pure-public KU terms (where this fix would over-mark)
            // are exactly those whose runtime node-id doesn't collide.
            let has_fresh_var = {
                use tamarin_term::lterm::{LSort, HasFrees};
                let mut found = false;
                fa.for_each_free(&mut |v| {
                    if v.sort == LSort::Fresh { found = true; }
                });
                found
            };
            if has_fresh_var {
                let live_goal_action = crate::constraint::constraints::Goal::Action(
                    i.clone(), fa.clone());
                for (g, st) in sub.sys.goals_mut().iter_mut() {
                    if g == &live_goal_action { st.solved = true; break; }
                }
            }

            // This candidate is viable — push as a new alive branch.
            let mut new_used = used.clone();
            // Haskell-faithful: track SOURCE LABEL.
            if let Some(label) = ku_source_label_for_fa(&fa) {
                new_used.insert(label);
            } else {
                new_used.insert(case_name.clone());
            }
            // HS-faithful: source-pick step APPENDS its name to `caseNames`
            // (Sources.hs:232 `(caseNames ++ x)`); `combine` runs only at the
            // refineSource boundary, not per-step inside solveAllSafeGoals.
            let mut new_name = name.clone();
            append_step_name_list(&mut new_name, &case_name);
            if trace {
                eprintln!("[disj-refine] commit legacy case={} -> {:?}",
                    case_name, new_name);
            }
            worklist.push((sub.sys, new_name, new_used,
                chains_left, iters_left - 1, new_last_chain_term.clone(), true));
            any_branched = true;
        }

        if !any_branched {
            // No candidate was viable — Haskell `asum [mzero, ...] =
            // mzero` → `nextStep = Nothing` → `solve` returns
            // `caseNames` (keep current state).  This branch survives,
            // so its `took_step` flag now counts toward `changes`.
            any_step_taken |= took_step;
            finished.push((red.sys, name));
        }
    }

    // HS-faithful: apply `refineSource`'s `combine(existing, step_names)`
    // now that solveAllSafeGoals has finished accumulating.  `combine`
    // strips leading "coerce" entries from `initial_name`; if anything
    // non-coerce remains it's the only segment we keep (the rest of
    // the chain is discarded), otherwise the accumulated step_names
    // take over.  Mirrors Sources.hs:135-139 exactly.
    let branches: Vec<(System, Vec<String>)> = finished.into_iter()
        .map(|(sys, step_names_list)| {
            let combined = combine_case_names_list(&initial_name, &step_names_list);
            (sys, combined)
        })
        .collect();
    (branches, any_step_taken)
}

/// Convert a stored case-name `String` to a step-name list.  Used
/// when crossing the legacy `String`-based API into the HS-faithful
/// `Vec<String>` representation.  Empty string → empty Vec;
/// otherwise treat the whole String as a single list element.
/// (Multi-element strings from saturate's internal list-aware path
/// reach this function only via the `cases_set`/`cases_take` legacy
/// wrappers, which join with `_` first.)
fn string_to_name_list(name: &str) -> Vec<String> {
    if name.is_empty() { Vec::new() } else { vec![name.to_string()] }
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

    // HS's `filterCases` (Sources.hs:217-218) operates only inside
    // `solveAllSafeGoals` (saturate), not at runtime.  HS's runtime
    // `solveWithSource` (ProofMethod.hs:319-320, the
    // `(intercalate "_" <$>) (solveWithSource ctxt ths goal)` call site)
    // passes the FULL source
    // list every call: `solveWithSource ctxt ths goal` where `ths =
    // pcSources ctxt`.  Re-applying the same source at multiple proof
    // positions is normal HS behaviour: each saturated case has its
    // internal premise goals pre-marked solved (verified via
    // `TAM_HS_TRACE_APPLY_SRC` dump), so `conjoinSystem` +
    // `simplifySystem`'s DG4-Fresh-uniqueness → DG3 cascade collapses
    // the grafted case onto existing nodes.  A runtime `used_sources`
    // filter forces fall-through to fresh rule enumeration, creating
    // unmerged Step/Start/Fresh nodes (NoStep_with_induction
    // divergence: extra `solve case Start` after the inner `case
    // Step`).  Removing the filter eliminates that divergence and
    // also closes a similar gap on KAS1.

    let src = sources.iter().find(|s| match &s.goal {
        Goal::Premise(_, fa) => fa.tag == fa_prem.tag,
        _ => false,
    })?;

    // HS-faithful: `solveWithSource` (ProofMethod.hs:319-320) accesses
    // `cdCases` via `(names, sysTh0) <- disjunctionOfList $ getDisj $
    // get cdCases th` — forcing the lazy thunk.  We must force via
    // `src.cases(ctx)` to trigger `ensure_saturated` here at the
    // FIRST source-case dispatch; using `cases_or_empty()` would see
    // empty cells and silently fall through to direct rule enumeration,
    // emitting an extra `[EXEC] solveGoal kind=Premise ...` trace
    // line that HS skips because its `solveWithSource` succeeded.
    // HS `matchToGoal` (Sources.hs:268-317; `maybeMatcher` 298-305) decides Just/Nothing for the
    // WHOLE source based ONLY on `maybeMatcher` (tag match, already
    // guaranteed by the `find` above) AND `doMatch (faTerm matchFact
    // faPat <> iTerm matchLVar iPat)` against the source's ABSTRACT goal
    // (`cdGoal th`, all-fresh-var terms from `precomputeSources`).  It is
    // independent of whether the individual `cdCases` survive conjoin:
    // per-case contradictions are dropped later in `_applySource`
    // (`disjunctionOfList ... >>= conjoinSystem`) WITHOUT causing
    // fall-through to runtime `solveGoal`.  Concretely, if every case is
    // contradictory, `solveWithSource` still returns `Just (empty
    // reduction)` → the proof node renders `by` with ZERO children
    // (Proof.hs:1084), NOT a runtime bare-rule graft.
    //
    // The abstract premise pattern is all-fresh-vars, so `matchFact`
    // always succeeds for a same-tag/same-arity live fact — mirror that
    // here with an explicit probe so we return `Some` (possibly empty)
    // whenever HS's `matchToGoal` would return `Just`, instead of
    // falling back to runtime `solve_premise_goal` and re-introducing a
    // shallow producer case that HS never explores (the keylessssl
    // `injectivity` `St_C ▶₀ #j` extra-`solve case C_2` divergence:
    // every St_C source-case is `refineSubst`-contradictory at runtime,
    // but HS emits `by`).
    let abstract_match_ok = match &src.goal {
        Goal::Premise(_, fa_pat) => {
            // The precomputed source goal (`cdGoal`) is built by
            // `precomputeSources` with all-fresh-variable terms, so HS's
            // `faTerm matchFact faPat` always succeeds for a same-tag,
            // same-arity live fact.  Require the pattern to be all-var to
            // mirror that exactly (so a hypothetical non-var pattern still
            // falls through to runtime if it genuinely can't match).
            fa_pat.tag == fa_prem.tag
                && fa_pat.terms.len() == fa_prem.terms.len()
                && fa_pat.terms.iter().all(|t| matches!(
                    t, tamarin_term::term::Term::Lit(tamarin_term::vterm::Lit::Var(_))))
        }
        _ => false,
    };

    let dbg = std::env::var("TAM_RS_DBG_RUNTIME_CASES").as_deref() == Ok("1");
    let mut out: Vec<(String, System)> = Vec::new();
    let mut all_attempted: Vec<(String, bool)> = Vec::new();
    for (name, case_sys) in src.cases(ctx) {
        // HS-faithful: use the stored (already-`combine`d, `_`-joined) case name
        // verbatim — never re-split on `_` (would corrupt funsyms containing `_`).
        let case_label = name.clone();
        let applied_arms = apply_source_case_premise(
            ctx, sys, src, &case_sys,
            goal_node, goal_prem_idx, fa_prem,
        );
        let kept = !applied_arms.is_empty();
        if dbg { all_attempted.push((case_label.clone(), kept)); }
        // HS-faithful: refineSubst's multi-arm fanout (Reduction.hs:724-725
        // `disjunctionOfList performSplit`) produces one System per AC
        // unifier arm with the SAME case name.  Push each as a separate
        // (case_label, sys) entry.  Sibling cases sharing the same
        // case_label get `_case_N` suffixes via `distinguish`
        // (ProofMethod.hs:335, applied by `uniqueListBy ... distinguish
        // cases` at ProofMethod.hs:308; `uniqueListBy` at ProofMethod.hs:91).
        for final_sys in applied_arms {
            out.push((case_label.clone(), final_sys));
        }
    }
    if dbg {
        eprintln!("[RUNTIME_CASES] prem_tag={:?} n_total={} n_kept={}",
            fa_prem.tag, all_attempted.len(), out.len());
        for (n, k) in &all_attempted {
            eprintln!("  case: {} kept={}", n, k);
        }
    }
    // HS-faithful: an empty `out` (all cases contradictory) still counts
    // as a successful `solveWithSource` when the abstract `matchToGoal`
    // would have matched — return `Some(empty)` so the dispatcher emits
    // `by` (no children) rather than falling through to runtime.
    if out.is_empty() && !abstract_match_ok { return None; }
    Some(out)
}

// `solve_with_source_cases` (premise non-ctx variant) was removed: it
// had zero callers — production premise solving routes through
// `solve_with_source_cases_ctx` — and it dragged the collision-prone
// `freshen_system(.., None)` legacy freshen path (see the freshen doc
// below).  Use the `_ctx` variant, which threads the global fresh
// counter via `Some(&ctx.maude)`.

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
        // Reserve enough idxs to cover EVERY var-bearing field that this
        // function shifts below (nodes/edges/less/goals/last/eq-store/
        // formulas/subterm-store).  Use `system_max_idx`, which walks all
        // of them (matching HS `instance HasFrees System`); the prior
        // hand-rolled walk omitted formulas/eq-conj/subterm-store, so a
        // var living only in one of those could shift past the reserved
        // range and collide.
        let sys_max = system_max_idx(sys);
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
    // HS `matchToGoal` (Sources.hs:307): `th = (evalFresh avoid goalTerm) . rename`.
    // `rename` (LTerm.hs:607-612) is Monotone — the uniform `shift_lvar` index
    // bump preserves AC arg order (`unsafefApp`), so use `map_free_monotone`
    // throughout this freshening.
    let mut out = sys.clone();
    out.nodes = std::sync::Arc::new(std::sync::Arc::unwrap_or_clone(out.nodes).into_iter()
        .map(|(id, ru)| {
            (shift_lvar(&id),
             ru.map_free_monotone(&mut |v| shift_lvar(&v))) })
        .collect());
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
    out.goals = std::sync::Arc::new(std::sync::Arc::unwrap_or_clone(out.goals).into_iter()
        .map(|(g, st)| {
            let g2 = match g {
                crate::constraint::constraints::Goal::Action(n, fa) =>
                    crate::constraint::constraints::Goal::Action(
                        shift_lvar(&n),
                        fa.map_free_monotone(&mut |v| shift_lvar(&v))),
                crate::constraint::constraints::Goal::Premise(p, fa) =>
                    crate::constraint::constraints::Goal::Premise(
                        (shift_lvar(&p.0), p.1),
                        fa.map_free_monotone(&mut |v| shift_lvar(&v))),
                crate::constraint::constraints::Goal::Chain(c, p) =>
                    crate::constraint::constraints::Goal::Chain(
                        (shift_lvar(&c.0), c.1),
                        (shift_lvar(&p.0), p.1)),
                other => other,
            };
            (g2, st)
        })
        .collect());
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
    // With DeBruijn bindings, only `BVar::Free` leaves carry idxs that
    // need shifting; `Bound` and `GBinding` are positional and unaffected.
    // `map_lvars_in_guarded` walks every Free leaf in the GAtoms.
    let shift_g = |g: &crate::guarded::Guarded| {
        crate::guarded::map_lvars_in_guarded(g, shift_parser_var)
    };
    out.formulas = out.formulas.iter().map(shift_g).collect();
    out.solved_formulas = out.solved_formulas.iter().map(shift_g).collect();
    out.lemmas = out.lemmas.iter().map(shift_g).collect();
    // Eq-store: shift both domain LVars and range terms.  This whole
    // freshening is HS `rename` (Monotone), so range-term shifts preserve
    // AC arg order — `map_free_monotone`.
    {
        let shifted_subst: Vec<_> = out.eq_store.subst.to_list().iter()
            .map(|(v, t)| {
                let v2 = shift_lvar(v);
                let t2 = (*t).clone().map_free_monotone(&mut |w| shift_lvar(&w));
                (v2, t2)
            })
            .collect();
        out.eq_store_mut().subst = tamarin_term::subst::Subst::from_list(shifted_subst);
        for d in out.eq_store_mut().conj.iter_mut() {
            for s in d.substs.iter_mut() {
                let shifted: Vec<_> = s.to_list().iter()
                    .map(|(v, t)| {
                        let v2 = shift_lvar(v);
                        let t2 = (*t).clone().map_free_monotone(&mut |w| shift_lvar(&w));
                        (v2, t2)
                    })
                    .collect();
                *s = tamarin_term::subst_vfresh::SubstVFresh::from_list(shifted);
            }
        }
    }
    // Subterm-store: shift the LNTerm pairs (small/big).  Part of the same
    // Monotone `rename` — preserve AC arg order.
    {
        let shift_st = |s: &crate::tools::subterm_store::SubtermConstraint|
            -> crate::tools::subterm_store::SubtermConstraint {
            crate::tools::subterm_store::SubtermConstraint {
                small: s.small.clone().map_free_monotone(&mut |w| shift_lvar(&w)),
                big: s.big.clone().map_free_monotone(&mut |w| shift_lvar(&w)),
                propagated: s.propagated,
            }
        };
        out.subterm_store_mut().subterms = out.subterm_store.subterms.iter()
            .map(shift_st).collect();
        out.subterm_store_mut().solved_subterms = out.subterm_store.solved_subterms.iter()
            .map(shift_st).collect();
    }
    out
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
/// Haskell-faithful `applySource` path (`refine_source_case_action`).
/// When `ctx_opt = Some(ctx)`, uses one-way Maude matching +
/// `someInst keepVarBindings` + `conjoinSystem` setNodes-collision
/// rule-eqs. When `None`, falls back to the legacy graft (preserves
/// older behaviour for callers that don't have a context — e.g.
/// saturate-time helpers).
#[track_caller]
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
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Only KU-tagged Action goals consult action sources.
    if fa_live.tag != FactTag::Ku || fa_live.terms.len() != 1 {
        return None;
    }
    let m_live = &fa_live.terms[0];
    if tamarin_utils::env_gate!("TAM_DBG_SRC_CASE") {
        let live_str = format!("{:?}", fa_live).chars().take(120).collect::<String>();
        eprintln!("[src_case] solve_with_source_cases CALLED for live={}", live_str);
    }

    // TAM_DBG_SRC_MATCH=1: dump each source pattern + match decision
    // for HS↔Rust diffing of source-case selection.
    let dbg_match = tamarin_utils::env_gate!("TAM_DBG_SRC_MATCH");
    if dbg_match {
        let live_str = format!("{:?}", m_live).chars().take(160).collect::<String>();
        let caller = std::panic::Location::caller();
        eprintln!("[src_match] looking for source matching live={} from {}:{}",
                  live_str, caller.file(), caller.line());
        for (i, s) in sources.iter().enumerate() {
            if let Goal::Action(_, gfa) = &s.goal {
                let pat_str = format!("{:?}", gfa).chars().take(160).collect::<String>();
                eprintln!("  src[{}] tag={:?}.{} pat={}",
                    i, gfa.tag, gfa.terms.len(), pat_str);
            } else {
                eprintln!("  src[{}] non-Action goal: {:?}", i, s.goal);
            }
        }
    }
    // Find a source whose abstract pattern matches `m_live`.
    let src = sources.iter().find(|s| match &s.goal {
        Goal::Action(_, gfa) => {
            if gfa.tag != FactTag::Ku || gfa.terms.len() != 1 {
                if dbg_match {
                    eprintln!("  → reject (tag/arity): tag={:?} arity={}",
                              gfa.tag, gfa.terms.len());
                }
                return false;
            }
            let pat = &gfa.terms[0];
            let result = match (pat, m_live) {
                (Term::Lit(Lit::Var(pv)), _) => {
                    let live_sort = sort_of_lnterm(m_live);
                    let ok = sort_ge(pv.sort, live_sort);
                    if dbg_match {
                        eprintln!("  → var-pat: pat_sort={:?} live_sort={:?} sort_ge={}",
                                  pv.sort, live_sort, ok);
                    }
                    ok
                }
                (Term::App(pf, pargs), Term::App(lf, largs)) => {
                    let ok = pf == lf && pargs.len() == largs.len();
                    if dbg_match {
                        eprintln!("  → app-app: pf==lf={} args_match={}",
                                  pf == lf, pargs.len() == largs.len());
                    }
                    ok
                }
                // App pattern + Var live — HS's `maybeMatcher`
                // (Sources.hs:299-305) falls into the `_ -> True`
                // catch-all for this case, allowing the source-pick on
                // bare-var live terms.  The unification then binds the
                // live var to the pattern's structure (e.g.
                // `x.3 → sign(t.1, t.2)`).
                (Term::App(_, _), Term::Lit(Lit::Var(_))) => true,
                _ => {
                    if dbg_match {
                        eprintln!("  → reject: pat is Lit/App mismatch with live");
                    }
                    false
                }
            };
            result
        }
        _ => false,
    })?;

    let abstract_orig = match &src.goal {
        Goal::Action(n, _) => n.clone(),
        _ => return None,
    };

    if tamarin_utils::env_gate!("TAM_RS_TRACE_APPLY_SRC") {
        let goal_str = format!("{:?}", fa_live).chars().take(200).collect::<String>();
        let _cases_for_print = src.cases_or_empty();
        let case_names: Vec<&String> = _cases_for_print.iter().map(|(n, _)| n).collect();
        eprintln!("[RS_APPLY_SRC_PRE] live_goal={} cases={:?}", goal_str, case_names);
    }
    if tamarin_utils::env_gate!("TAM_DBG_SRC_CASE") {
        let goal_str = format!("{:?}", fa_live).chars().take(120).collect::<String>();
        eprintln!("[src_case] LIVE goal={}", goal_str);
        for (n, c) in src.cases_or_empty() {
            eprintln!("[src_case] name={} nodes={} edges={} goals={} last_atom={:?}",
                n, c.nodes.len(), c.edges.len(), c.goals.len(), c.last_atom);
            for (id, ru) in c.nodes.iter() {
                let nm = crate::constraint::solver::reduction::rule_case_name(ru);
                let fact_dump = |fs: &[crate::fact::LNFact]| -> Vec<String> {
                    fs.iter().map(|a| format!("{}({:?})", crate::fact::fact_tag_name(&a.tag),
                        a.terms.iter().map(|t| format!("{:?}", t).chars().take(80).collect::<String>())
                            .collect::<Vec<_>>())).collect::<Vec<_>>()
                };
                eprintln!("[src_case]   node {:?} → {} | prems={:?} concs={:?} acts={:?}", id, nm,
                    fact_dump(&ru.premises), fact_dump(&ru.conclusions), fact_dump(&ru.actions));
            }
            for e in &c.edges {
                eprintln!("[src_case]   edge {:?}.c{} → {:?}.p{}",
                    e.src.0, e.src.1.0, e.tgt.0, e.tgt.1.0);
            }
            for (g, _) in c.goals.iter() {
                eprintln!("[src_case]   goal {:?}", g);
            }
            for (v, t) in c.eq_store.subst.to_list().iter() {
                eprintln!("[src_case]   eq {}.{}/{:?} → {:?}", v.name, v.idx, v.sort,
                    format!("{:?}", t).chars().take(80).collect::<String>());
            }
        }
    }

    // HS-faithful: force the source's `cdCases` thunk via
    // `src.cases(ctx)` when we have a `ProofContext` available.
    // This triggers `ensure_saturated` on first call per ctx, then
    // returns the saturated case set.  For protocols where this
    // function isn't called (e.g. a Var-headed `KU(t:Fresh)` source
    // pattern on an existence-only lemma whose live goal is `KU(x:Msg)`
    // — sort mismatch, no match) the saturate work is never triggered,
    // matching HS's lazy-thunk behaviour.
    let cases_iter: Vec<(String, System)> = if let Some(c) = ctx_opt {
        src.cases(c)
    } else {
        src.cases_or_empty()
    };
    // HS-faithful `applySource`/`solveWithSource` (Sources.hs:427,438-442):
    // once a source's abstract pattern MATCHES the live goal (the `src`
    // find above succeeded), `applySource` returns `Just _` and its
    // reduction runs `disjunctionOfList (getDisj cdCases)`.  When `cdCases`
    // is EMPTY, that `disjunctionOfList []` is `mzero` → ZERO branches, but
    // the OUTER `solveWithSource` still returned `Just` — so `ProofMethod`'s
    // `maybe (solveGoal goal) ... ws` does NOT fall back to `solveGoal`; the
    // goal node closes with zero open cases (rendered `by`).  RS must mirror
    // this: a matched source with ZERO precomputed cases is `Some(vec![])`,
    // NOT `None`.  Returning `None` (the `out.is_empty()` path below) would
    // conflate "matched, empty" (HS `Just []`) with "no match" (HS
    // `Nothing`), letting the caller fall through to runtime rule
    // enumeration — re-opening the `coerce` → `KD` → chain subtree HS prunes
    // for builtin destructors like `check_rep`/`get_rep` (locations-report).
    // This is the runtime half of the saturate-time fix (refineSource keeps
    // 0-case sources); both are needed for the locations-report SAPiC
    // theories' (AKE/SOC/OTP/AC) parity.
    if cases_iter.is_empty() {
        return Some(Vec::new());
    }
    let dbg_rt = std::env::var("TAM_RS_DBG_RUNTIME_CASES").as_deref() == Ok("1");
    let total_n = cases_iter.len();
    let mut out: Vec<(String, System, crate::fact::LNFact)> = Vec::new();
    let mut kept_names: Vec<String> = Vec::new();
    let mut all_names: Vec<String> = Vec::new();

    if let Some(ctx) = ctx_opt {
        // ----------------------------------------------------------------
        // HS-faithful `refineSource` order (Sources.hs:131,376-419):
        //   refineSubst (per case) → removeRedundantCases (BEFORE conjoin)
        //   → _applySource (someInst + conjoinSystem) per SURVIVOR only.
        //
        // Step 1: run the REFINE half (match + refineSubst + someInst) for
        // EVERY case, collecting one `RefineArm` per refineSubst AC arm.
        // No conjoin yet.  refineSubst fan-out (HS `disjunctionOfList
        // performSplit`, Reduction.hs:724-725) yields multiple arms per
        // case; all arms share the case's `case_label`.
        // ----------------------------------------------------------------
        let mut refine_arms: Vec<(String, RefineArm)> = Vec::new();
        for (name, case_sys) in cases_iter {
            // HS-faithful: the stored case name is ALREADY the final display
            // name — `refineSource` applied `combine` (Sources.hs:135-139) and
            // the list was joined via `intercalate "_"` (ProofMethod.hs:511).
            // HS NEVER re-splits a name on `_`, so use it verbatim.
            let case_label = name.clone();
            if dbg_rt { all_names.push(case_label.clone()); }
            // Haskell-faithful `applySource` path: matches the live goal
            // against the source's ABSTRACT `cdGoal` (`src.goal`) — NOT a
            // case-specific action — mirroring `matchToGoal` (Sources.hs:268).
            let arms = refine_source_case_action(
                ctx, sys, src, &case_sys, goal_node, fa_live);
            for arm in arms {
                refine_arms.push((case_label.clone(), arm));
            }
        }

        // ----------------------------------------------------------------
        // Step 2: `removeRedundantCases ctxt stableVars` (Sources.hs:236-260)
        // — run the dedup BEFORE conjoin, on the pre-conjoin case
        // sub-system (`refined_case_for_dedup`), so the expensive bilinear
        // `conjoinSystem` re-narrow is paid only for survivors HS keeps.
        // Gated on BP/MSet per HS's `removeRedundantCases` short-circuit;
        // for non-BP/non-MSet theories the dedup is a no-op (no two arms
        // ever alpha-coincide) so every arm survives — identical to before.
        // ----------------------------------------------------------------
        let survivors: std::collections::BTreeSet<usize> = {
            let msig = ctx.maude.maude_sig();
            if msig.enable_bp || msig.enable_mset {
                use tamarin_term::lterm::HasFrees;
                let stable_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar> = {
                    let mut s = std::collections::BTreeSet::new();
                    s.insert(goal_node.clone());
                    fa_live.for_each_free(&mut |v: &tamarin_term::lterm::LVar| {
                        s.insert(v.clone());
                    });
                    s
                };
                // Mirror `removeRedundantCases` survivor selection exactly:
                // `sortednubBy compareSystemsUpToNewVars` keeps the LAST
                // element of an EQ-run, then `sortOn fst` restores
                // original-index order (last-wins per EQ-run).
                let keyed: Vec<(usize, String)> = refine_arms.iter().enumerate()
                    .map(|(idx, (_label, arm))| {
                        (idx, compute_compare_systems_key(
                            &arm.refined_case_for_dedup, &stable_vars))
                    })
                    .collect();
                let deduped = sortednub_by(
                    &|a: &(usize, String), b: &(usize, String)| a.1.cmp(&b.1),
                    keyed,
                );
                deduped.into_iter().map(|(idx, _)| idx).collect()
            } else {
                // No dedup: every arm survives.
                (0..refine_arms.len()).collect()
            }
        };

        // ----------------------------------------------------------------
        // Step 3: `_applySource` (someInst already done; conjoinSystem +
        // conjoin-fanout + E.5 + output) for SURVIVOR arms only.  Same
        // `case_label` for all of a case's arms; proof_method.rs handles
        // `_case_N` disambiguation (HS `uniqueListBy ... distinguish cases`
        // ProofMethod.hs:308).
        // ----------------------------------------------------------------
        for (idx, (case_label, arm)) in refine_arms.into_iter().enumerate() {
            if !survivors.contains(&idx) { continue; }
            let result = conjoin_refine_arm(ctx, sys, goal_node, fa_live, arm);
            for (grafted_sys, live_action, _refined_case) in result {
                if dbg_rt { kept_names.push(case_label.clone()); }
                out.push((case_label.clone(), grafted_sys, live_action));
            }
        }
    } else {
        // Legacy path: freshen + graft + caller-runs-solve_fact_eqs.
        // Used at saturate time (no ProofContext).  No conjoin-time dedup
        // (the saturate-time `saturate_out_premise` path's own
        // `refine_one_source` already deduplicates).
        for (name, case_sys) in cases_iter {
            // HS-faithful: stored case name is already final; use verbatim
            // (no `_`-splitting).  See note at the action-goal call site.
            let case_label = name.clone();
            if dbg_rt { all_names.push(case_label.clone()); }
            let renamed = freshen_system(&case_sys, avoid_max, ctx_opt.map(|c| &c.maude));
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
            let Some(grafted) = graft_case_into_action(
                sys, &renamed, &abstract_renamed, goal_node, fa_live,
            ) else { continue };
            if dbg_rt { kept_names.push(case_label.clone()); }
            out.push((case_label, grafted, action_fact));
        }
    }
    if dbg_rt {
        let head = match &fa_live.terms[0] {
            tamarin_term::term::Term::App(n, args) => format!("App({:?},{})", n, args.len()),
            tamarin_term::term::Term::Lit(_) => "Lit".to_string(),
        };
        eprintln!("[RUNTIME_CASES_ACT] head={} total={} kept={} all={:?} kept_names={:?}",
            head, total_n, out.len(), all_names, kept_names);
    }
    if out.is_empty() { return None; }
    Some(out)
}


/// HS-faithful `caseNames ++ x` (Sources.hs) — append the step name as
/// a NEW list element.  HS's `caseNames` is `[String]`; we model it as
/// `Vec<String>` here.  Empty step names are skipped.  The
/// refineSource-boundary truncation (HS `combine`) lives in
/// `combine_case_names_list`, not here.
fn append_step_name_list(names: &mut Vec<String>, sub_name: &str) {
    if !sub_name.is_empty() {
        names.push(sub_name.to_string());
    }
}

/// Render a step-name list as a single user-facing case-name string,
/// matching HS's `intercalate "_" names'` (ProofMethod.hs:319).
pub(crate) fn case_name_list_to_string(names: &[String]) -> String {
    names.join("_")
}

/// HS-faithful `combine` (Sources.hs:135-139):
///
/// ```haskell
/// combine []            ns' = ns'
/// combine ("coerce":ns) ns' = combine ns ns'
/// combine (n       :_)  _   = [n]
/// ```
///
/// Strips leading `"coerce"` elements from `existing`, then:
/// - if everything stripped → return `new_names` (HS uses `ns'`)
/// - else return ONLY the first non-coerce element as a singleton,
///   dropping the rest of `existing` AND `new_names` entirely.
///
/// This is the refineSource-boundary collapse that keeps HS's case
/// names short across saturate iters.  Mirrors Sources.hs exactly —
/// no underscore-prefix legacy: each `Vec<String>` element is a
/// single step name from `solveGoal`'s return.
fn combine_case_names_list(existing: &[String], new_names: &[String]) -> Vec<String> {
    let mut i = 0;
    while i < existing.len() && existing[i] == "coerce" {
        i += 1;
    }
    if i >= existing.len() {
        // All stripped (or empty existing) — use new names.
        new_names.to_vec()
    } else {
        // First non-coerce; discard rest of existing AND new_names.
        vec![existing[i].clone()]
    }
}

// A source-case name reaching the runtime is already the final, `combine`d
// display name (HS `combine`, Sources.hs:135-139, ported in
// `combine_case_names_list`; joined with `intercalate "_"`, ProofMethod.hs:511).
// Use it verbatim — never re-split on `_`, which would corrupt function symbols
// whose names contain `_` (e.g. `c_KDF_SKc` → `SKc`).

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
/// `conjoin_refine_arm` adds the match-subst `t:Fresh:1
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
///   for runtime applySource to see a clean precomputed case.
fn restrict_eq_store_to_stable_vars(
    sys: &mut System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) {
    // Haskell's `restrict` (SubstVFree.hs:160-161; call site
    // Sources.hs:122-124 `modify sSubst (restrict stableVars)`) is a
    // simple key-filter using FULL LVar equality:
    //   `Subst (M.filterWithKey (\v _ -> v `elem` vs) smap)`
    // - No chain-chase.
    // - No flipping of non-stable→stable bindings.
    // - No sort-blind (name, idx) matching.
    // Keys not in `vars` are dropped; values that referenced dropped
    // keys become dangling — fine because Haskell's substitution lookup
    // falls back to identity for unbound vars.
    //
    // The prior Rust-specific workarounds (flip_to_stable_keys + sort-
    // blind (name, idx) matching) were attempting to preserve bindings
    // that the May 20 LVar-Ord change put on the wrong side of the
    // key-filter.  Per "Haskell logic is the source of truth", those
    // workarounds are removed — any divergence they were masking is a
    // bug elsewhere (in unification orientation or narrowing) and must
    // be fixed at that level instead.
    let kept: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)>
        = sys.eq_store.subst.to_list().into_iter()
            .filter(|(v, _)| stable_vars.contains(v))
            .collect();
    sys.invalidate_max_var_idx_cache();
    sys.eq_store_mut().subst = tamarin_term::subst::Subst::from_list(kept);
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

/// Freshen all vars in `sys` EXCEPT those in `keep`, shifting every
/// other var's idx by `shift_amount`. Mirrors Haskell's
/// `someInst sysTh0 keepVarBindings` (Sources.hs:348). Vars in `keep`
/// are preserved (they correspond to live-system vars introduced by
/// the match-subst); other vars get shifted (callers derive
/// `shift_amount` from the MaudeHandle's global counter via
/// `reserve_idxs`) so they don't collide with live-system vars OR with
/// vars from prior applySource grafts.  Without a globally-unique
/// shift, two applySource calls against the same live system at the
/// same step would shift to identical idxs, creating spurious cycles
/// in the joined system (TLS_Handshake::session_key_setup_possible root
/// cause).
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
        .map(|v| (v.name.to_string(), v.idx))
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
    out.nodes = std::sync::Arc::new(std::sync::Arc::unwrap_or_clone(out.nodes).into_iter()
        .map(|(id, ru)| (shift_lvar(&id), ru.map_free(&mut |v| shift_lvar(&v))))
        .collect());
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
    out.goals = std::sync::Arc::new(std::sync::Arc::unwrap_or_clone(out.goals).into_iter()
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
        .collect());
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
    for c in &mut out.subterm_store_mut().subterms {
        c.small = c.small.clone().map_free(&mut |v| shift_lvar(&v));
        c.big = c.big.clone().map_free(&mut |v| shift_lvar(&v));
    }
    for c in &mut out.subterm_store_mut().solved_subterms {
        c.small = c.small.clone().map_free(&mut |v| shift_lvar(&v));
        c.big = c.big.clone().map_free(&mut |v| shift_lvar(&v));
    }
    // Eq-store subst: shift both var keys and term values.
    out.eq_store_mut().subst = {
        let pairs: Vec<_> = out.eq_store.subst.to_list().into_iter()
            .map(|(v, t)| {
                let new_v = shift_lvar(&v);
                let new_t = t.map_free(&mut |w| shift_lvar(&w));
                (new_v, new_t)
            })
            .collect();
        tamarin_term::subst::Subst::from_list(pairs)
    };
    // Eq-store conj (SplitG disjunctions).  HS-faithful `mapFrees
    // (SubstVFresh n LVar)` (SubstVFresh.hs:200-202): `rename`/`mapFrees`
    // rewrite ONLY the DOMAIN keys; the range (existentially-bound
    // witnesses) is left UNTOUCHED.  Shifting the range here (as the old
    // code did) re-based the variant-disj witnesses on every matchToGoal
    // rename, contributing to the cumulative inflation that rotates
    // Responder_secrecy's 3-way split.  Match `freshen_system_some_inst`
    // and `rename_precise.rs:98-109`: shift keys only.
    //
    // NOTE: a uniform shift of the domain keys keeps the variant SplitG's
    // keys consistent with the surrounding (also-shifted) nodes/edges/goals
    // so `subst_system` still finds matching keys after a variant is
    // picked (the resolved1_contract_reachable concern); the witnesses in
    // the range are local and need no shift.
    for disj in out.eq_store_mut().conj.iter_mut() {
        for s in disj.substs.iter_mut() {
            let pairs: Vec<_> = s.to_list().into_iter()
                .map(|(v, t)| (shift_lvar(&v), t))
                .collect();
            *s = tamarin_term::subst_vfresh::SubstVFresh::from_list(pairs);
        }
    }
    out
}

/// HS-faithful `someInst`: per-var fresh allocation in HS's `mapFrees`
/// traversal order.  Mirrors `someInst` (LTerm.hs:601-602) +
/// `importBinding` (Bind.hs:128-140) under FastFresh:
///
/// ```haskell
/// someInst = mapFrees (Arbitrary $ \x ->
///              importBinding (`LVar` lvarSort x) x (lvarName x))
/// importBinding mkR k _ = lookupBinding k >>= \case
///   Nothing -> do v <- mkR _ <$> freshIdent _; insert k v; return v
///   Just v  -> return v
/// ```
///
/// Each unique LVar in HS-traversal-order gets the NEXT idx from the
/// global counter (FastFresh).  Vars in `keep` are bound identically
/// (keepVarBindings).  Differs from `freshen_system_keep_with_shift`
/// which uniformly shifts all non-keep vars by a fixed amount —
/// `someInst` instead assigns distinct sequential idxs in traversal
/// order, mirroring HS exactly.
fn freshen_system_some_inst(
    sys: &System,
    keep: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
    maude: &tamarin_term::maude_proc::MaudeHandle,
) -> System {
    use tamarin_term::lterm::HasFrees;
    use std::collections::BTreeMap;

    // Step 1: walk the system in HS-faithful order, building bindings.
    //
    // HS `mapFrees System` (System.hs:1863-1876) iterates fields in
    // declaration order: sNodes, sEdges, sLessAtoms, sLastAtom,
    // sSubtermStore, sEqStore, sFormulas, sSolvedFormulas, sLemmas,
    // sGoals (skipping sNextGoalNr, sSourceKind, sDiffSystem which
    // have no LVars).  Within each container, HS's HasFrees instances
    // walk in container order (M.Map by key, Set by element Ord).
    let mut bindings: BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>
        = BTreeMap::new();
    for v in keep {
        bindings.insert(v.clone(), v.clone());
    }
    let import_var = |v: &tamarin_term::lterm::LVar,
                      bindings: &mut BTreeMap<
                        tamarin_term::lterm::LVar,
                        tamarin_term::lterm::LVar>| {
        if bindings.contains_key(v) { return; }
        let new_idx = maude.reserve_idxs(1);
        let new_v = tamarin_term::lterm::LVar {
            name: v.name,
            sort: v.sort,
            idx: new_idx,
        };
        bindings.insert(v.clone(), new_v);
    };

    // sNodes: BTreeMap-equivalent iteration by NodeId order.  Rust's
    // sys.nodes is Vec<(NodeId, RuleACInst)> insertion-ordered, so
    // sort by NodeId to mimic HS's M.Map iteration.
    let mut sorted_nodes: Vec<&(crate::constraint::constraints::NodeId, crate::rule::RuleACInst)>
        = sys.nodes.iter().collect();
    sorted_nodes.sort_by(|a, b| a.0.cmp(&b.0));
    for (id, rule) in &sorted_nodes {
        import_var(id, &mut bindings);
        // HS Rule HasFrees order: info, premises, conclusions, actions,
        // new_vars.  Rust's `info` (ProtoRuleACInstInfo) typically has
        // no LVars (rule name + case info), so skipping is harmless;
        // walk premises/conclusions/actions/new_vars explicitly to
        // match HS exactly.
        for p in &rule.premises {
            p.for_each_free(&mut |v| import_var(v, &mut bindings));
        }
        for c in &rule.conclusions {
            c.for_each_free(&mut |v| import_var(v, &mut bindings));
        }
        for a in &rule.actions {
            a.for_each_free(&mut |v| import_var(v, &mut bindings));
        }
        for nv in &rule.new_vars {
            nv.for_each_free(&mut |v| import_var(v, &mut bindings));
        }
    }
    // sEdges: Set Edge → sort by Edge Ord
    let mut sorted_edges: Vec<&crate::constraint::constraints::Edge>
        = sys.edges.iter().collect();
    sorted_edges.sort();
    for e in &sorted_edges {
        import_var(&e.src.0, &mut bindings);
        import_var(&e.tgt.0, &mut bindings);
    }
    // sLessAtoms: Set LessAtom → sort
    let mut sorted_less: Vec<&crate::constraint::constraints::LessAtom>
        = sys.less_atoms.iter().collect();
    sorted_less.sort();
    for l in &sorted_less {
        import_var(&l.smaller, &mut bindings);
        import_var(&l.larger, &mut bindings);
    }
    // sLastAtom
    if let Some(la) = &sys.last_atom {
        import_var(la, &mut bindings);
    }
    // sSubtermStore — HS-faithful Set walk in Ord order
    // (SubtermStore.hs `Set SubtermD` for both pos and neg + S.Set Set).
    // Mirror `rename_precise.rs:129-142` Set-sorted walk so per-name
    // PreciseFresh counters / global FastFresh allocations land at the
    // same idxs HS does.
    let mut sub_sorted: Vec<&crate::tools::subterm_store::SubtermConstraint>
        = sys.subterm_store.subterms.iter().collect();
    sub_sorted.sort_by(|a, b| (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    for c in sub_sorted {
        c.small.for_each_free(&mut |v| import_var(v, &mut bindings));
        c.big.for_each_free(&mut |v| import_var(v, &mut bindings));
    }
    let mut solved_sub_sorted: Vec<&crate::tools::subterm_store::SubtermConstraint>
        = sys.subterm_store.solved_subterms.iter().collect();
    solved_sub_sorted.sort_by(|a, b| (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    for c in solved_sub_sorted {
        c.small.for_each_free(&mut |v| import_var(v, &mut bindings));
        c.big.for_each_free(&mut |v| import_var(v, &mut bindings));
    }
    // sEqStore: subst keys/values, then conj substs.
    for (k, t) in sys.eq_store.subst.to_list() {
        import_var(&k, &mut bindings);
        t.for_each_free(&mut |v| import_var(v, &mut bindings));
    }
    // HS-faithful `mapFrees (SubstVFresh n LVar)` (SubstVFresh.hs:196-202):
    // `foldFrees f = foldFrees f . M.keys` and `mapDomain (v,t) = (,t) <$>
    // mapFrees f v` — so `someInst`/`rename` over a variant disj touch ONLY
    // the DOMAIN keys; the range (witnesses) is left UNTOUCHED.  Walking the
    // range here (as the old code did) re-freshened the variant-disj
    // witnesses on every someInst, inflating them across saturate/conjoin
    // iterations (e.g. Responder_secrecy: ~k.6 → ~k.31) and rotating the
    // 3-way split via `Ord LNSubstVFresh`.  Match `rename_precise.rs:98-109`
    // and import keys only.
    // HS-faithful: inner `S.Set LNSubstVFresh` walks Ord-ascending
    // (`mapFrees (Set a) = fmap S.fromList . mapFrees f . S.toList`,
    // LTerm.hs:866).  RS's `Vec` is in insertion order — sort to match
    // (mirroring `rename_precise.rs:144-153`).
    for d in sys.eq_store.conj.iter() {
        let mut substs_sorted: Vec<&tamarin_term::subst_vfresh::SubstVFresh<
            tamarin_term::lterm::Name, tamarin_term::lterm::LVar>>
            = d.substs.iter().collect();
        substs_sorted.sort();
        for s in substs_sorted {
            for (k, _t) in s.to_list() {
                import_var(&k, &mut bindings);
                // Range vars NOT imported (HS-faithful).
            }
        }
    }
    // sFormulas, sSolvedFormulas, sLemmas — walk frees in each Guarded.
    // We reuse `map_lvars_in_guarded` as a side-effect walker: the
    // callback receives every free VarSpec; we convert to LVar (using
    // SortHint→LSort projection) and import.  The mapped output is
    // discarded — we only care about the visit side effect.
    let walk_guarded = |g: &crate::guarded::Guarded,
                        bindings: &mut BTreeMap<
                            tamarin_term::lterm::LVar,
                            tamarin_term::lterm::LVar>| {
        let _ = crate::guarded::map_lvars_in_guarded(g, |v: &tamarin_parser::ast::VarSpec| {
            if let Some(lv) = vspec_to_lvar(v) {
                if !bindings.contains_key(&lv) {
                    let new_idx = maude.reserve_idxs(1);
                    bindings.insert(lv.clone(), tamarin_term::lterm::LVar {
                        name: lv.name, sort: lv.sort, idx: new_idx,
                    });
                }
            }
            v.clone()
        });
    };
    // HS-faithful: `_sFormulas` / `_sSolvedFormulas` / `_sLemmas` are
    // `S.Set LNGuarded`; HS walks them in Ord-ascending (Term/LTerm.hs:866
    // `foldMap (foldFrees f)`).  RS's `Vec<Guarded>` is in insertion order.
    // Sort copies (mirroring `rename_precise.rs:178-189`) so per-name
    // counter assignment matches HS exactly.
    let mut formulas_sorted: Vec<&crate::guarded::Guarded>
        = sys.formulas.iter().collect();
    formulas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for g in formulas_sorted { walk_guarded(g, &mut bindings); }
    let mut solved_formulas_sorted: Vec<&crate::guarded::Guarded>
        = sys.solved_formulas.iter().collect();
    solved_formulas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for g in solved_formulas_sorted { walk_guarded(g, &mut bindings); }
    let mut lemmas_sorted: Vec<&crate::guarded::Guarded>
        = sys.lemmas.iter().collect();
    lemmas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for g in lemmas_sorted { walk_guarded(g, &mut bindings); }
    // sGoals: M.Map Goal GoalStatus → sort by Goal (using goal_cmp).
    let mut sorted_goals: Vec<&(crate::constraint::constraints::Goal,
                                crate::constraint::system::GoalStatus)>
        = sys.goals.iter().collect();
    sorted_goals.sort_by(|a, b| crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
    for (g, _) in &sorted_goals {
        match g {
            crate::constraint::constraints::Goal::Action(n, fa) => {
                import_var(n, &mut bindings);
                fa.for_each_free(&mut |v| import_var(v, &mut bindings));
            }
            crate::constraint::constraints::Goal::Premise(p, fa) => {
                import_var(&p.0, &mut bindings);
                fa.for_each_free(&mut |v| import_var(v, &mut bindings));
            }
            crate::constraint::constraints::Goal::Chain(c, p) => {
                import_var(&c.0, &mut bindings);
                import_var(&p.0, &mut bindings);
            }
            crate::constraint::constraints::Goal::Disj(d) => {
                for alt in &d.0 {
                    walk_guarded(alt, &mut bindings);
                }
            }
            crate::constraint::constraints::Goal::Subterm((small, big)) => {
                small.for_each_free(&mut |v| import_var(v, &mut bindings));
                big.for_each_free(&mut |v| import_var(v, &mut bindings));
            }
            crate::constraint::constraints::Goal::Split(_) => {}
        }
    }

    // Step 2: apply bindings to produce the freshened system.
    let lookup = |v: &tamarin_term::lterm::LVar| -> tamarin_term::lterm::LVar {
        bindings.get(v).cloned().unwrap_or_else(|| v.clone())
    };
    // For Guarded formulas (VarSpec-based), build a (name, idx) → new (name, idx) map.
    // VarSpec sort hints are preserved unchanged.
    let vs_map: std::collections::BTreeMap<(String, u64), (String, u64)> =
        bindings.iter()
            .map(|(orig, new)| ((orig.name.to_string(), orig.idx),
                                (new.name.to_string(), new.idx)))
            .collect();
    let lookup_vs = |v: &tamarin_parser::ast::VarSpec| -> tamarin_parser::ast::VarSpec {
        if let Some((new_name, new_idx)) = vs_map.get(&(v.name.clone(), v.idx)) {
            tamarin_parser::ast::VarSpec {
                name: new_name.clone(),
                idx: *new_idx,
                sort: v.sort,
                typ: v.typ.clone(),
            }
        } else {
            v.clone()
        }
    };

    let mut out = sys.clone();
    out.nodes = std::sync::Arc::new(std::sync::Arc::unwrap_or_clone(out.nodes).into_iter()
        .map(|(id, ru)| (lookup(&id), ru.map_free(&mut |v| lookup(&v))))
        .collect());
    out.edges = out.edges.into_iter()
        .map(|e| crate::constraint::constraints::Edge {
            src: (lookup(&e.src.0), e.src.1),
            tgt: (lookup(&e.tgt.0), e.tgt.1),
        })
        .collect();
    out.less_atoms = out.less_atoms.into_iter()
        .map(|l| crate::constraint::constraints::LessAtom::new(
            lookup(&l.smaller),
            lookup(&l.larger),
            l.reason,
        ))
        .collect();
    out.goals = std::sync::Arc::new(std::sync::Arc::unwrap_or_clone(out.goals).into_iter()
        .map(|(g, st)| {
            let g2 = match g {
                crate::constraint::constraints::Goal::Action(n, fa) =>
                    crate::constraint::constraints::Goal::Action(
                        lookup(&n),
                        fa.map_free(&mut |v| lookup(&v))),
                crate::constraint::constraints::Goal::Premise(p, fa) =>
                    crate::constraint::constraints::Goal::Premise(
                        (lookup(&p.0), p.1),
                        fa.map_free(&mut |v| lookup(&v))),
                crate::constraint::constraints::Goal::Chain(c, p) =>
                    crate::constraint::constraints::Goal::Chain(
                        (lookup(&c.0), c.1),
                        (lookup(&p.0), p.1)),
                crate::constraint::constraints::Goal::Disj(d) => {
                    let mapped: Vec<_> = d.0.into_iter()
                        .map(|alt| crate::guarded::map_lvars_in_guarded(&alt, &lookup_vs))
                        .collect();
                    crate::constraint::constraints::Goal::Disj(
                        crate::constraint::constraints::Disj(mapped))
                }
                crate::constraint::constraints::Goal::Subterm((small, big)) =>
                    crate::constraint::constraints::Goal::Subterm((
                        small.map_free(&mut |v| lookup(&v)),
                        big.map_free(&mut |v| lookup(&v)))),
                other @ crate::constraint::constraints::Goal::Split(_) => other,
            };
            (g2, st)
        })
        .collect());
    if let Some(la) = out.last_atom.take() {
        out.last_atom = Some(lookup(&la));
    }
    out.formulas = out.formulas.into_iter()
        .map(|g| crate::guarded::map_lvars_in_guarded(&g, &lookup_vs))
        .collect();
    out.solved_formulas = out.solved_formulas.into_iter()
        .map(|g| crate::guarded::map_lvars_in_guarded(&g, &lookup_vs))
        .collect();
    out.lemmas = out.lemmas.into_iter()
        .map(|g| crate::guarded::map_lvars_in_guarded(&g, &lookup_vs))
        .collect();
    for c in &mut out.subterm_store_mut().subterms {
        c.small = c.small.clone().map_free(&mut |v| lookup(&v));
        c.big = c.big.clone().map_free(&mut |v| lookup(&v));
    }
    for c in &mut out.subterm_store_mut().solved_subterms {
        c.small = c.small.clone().map_free(&mut |v| lookup(&v));
        c.big = c.big.clone().map_free(&mut |v| lookup(&v));
    }
    out.eq_store_mut().subst = {
        let pairs: Vec<_> = out.eq_store.subst.to_list().into_iter()
            .map(|(v, t)| (lookup(&v), t.map_free(&mut |w| lookup(&w))))
            .collect();
        tamarin_term::subst::Subst::from_list(pairs)
    };
    // HS-faithful `mapFrees (SubstVFresh)` (SubstVFresh.hs:200-202):
    // rewrite ONLY the domain keys; leave the range (witnesses) UNTOUCHED.
    for disj in out.eq_store_mut().conj.iter_mut() {
        for s in disj.substs.iter_mut() {
            let pairs: Vec<_> = s.to_list().into_iter()
                .map(|(v, t)| (lookup(&v), t))
                .collect();
            *s = tamarin_term::subst_vfresh::SubstVFresh::from_list(pairs);
        }
    }
    out
}

/// Project a `VarSpec` to an `LVar` for `someInst` import tracking.
/// Returns None if SortHint is `Untagged` (cannot determine LSort).
fn vspec_to_lvar(v: &tamarin_parser::ast::VarSpec) -> Option<tamarin_term::lterm::LVar> {
    use tamarin_parser::ast::{SortHint, SuffixSort};
    use tamarin_term::lterm::LSort;
    let sort = match v.sort {
        SortHint::Msg => LSort::Msg,
        SortHint::Pub => LSort::Pub,
        SortHint::Fresh => LSort::Fresh,
        SortHint::Node => LSort::Node,
        SortHint::Nat => LSort::Nat,
        SortHint::Suffix(SuffixSort::Msg) => LSort::Msg,
        SortHint::Suffix(SuffixSort::Pub) => LSort::Pub,
        SortHint::Suffix(SuffixSort::Fresh) => LSort::Fresh,
        SortHint::Suffix(SuffixSort::Node) => LSort::Node,
        SortHint::Suffix(SuffixSort::Nat) => LSort::Nat,
        SortHint::Untagged => return None,
    };
    Some(tamarin_term::lterm::LVar {
        name: tamarin_term::intern::intern_str(v.name.as_str()), sort, idx: v.idx,
    })
}

/// One refineSubst arm produced by `refine_source_case_action` — the
/// per-arm state at the conjoin boundary of HS's `_applySource`
/// (Sources.hs:447-468), BEFORE `conjoinSystem`.  HS runs
/// `removeRedundantCases` (Sources.hs:236-260) on these (keyed by
/// `refined_case_for_dedup`) BEFORE conjoining only the survivors.
/// `conjoin_refine_arm` performs the `markGoalAsSolved` + `conjoinSystem`
/// + conjoin-fanout + E.5 + close-trivial-chains + output for one arm.
struct RefineArm {
    /// someInst result — the freshened case sub-system to conjoin.
    freshened_case: System,
    /// The recovered live KU action fact returned per output entry.
    live_action: crate::fact::LNFact,
    /// Post-refineSubst+restrict case sub-system (BEFORE someInst/conjoin)
    /// — the dedup key (HS `removeRedundantCases` `compareSystemsUpToNewVars`).
    refined_case_for_dedup: System,
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
///
/// ## Return shape
///
/// `Vec` because `refineSubst` (`solve_term_eqs SplitNow` here) can fan
/// out into multiple AC-unification arms — each arm is a distinct
/// disjunctive sub-case in HS's `refineSource` (Sources.hs:114-138)
/// because `solveTermEqs SplitNow` calls `disjunctionOfList performSplit`
/// (Reduction.hs:712-733; `performSplit` use at 723-725).  Empty Vec
/// means the case dropped (match-fail,
/// refineSubst-contradictory, conjoin-fail, etc.).
///
/// Multi-arm fan-out semantics: HS's `_applySource` runs in the
/// `Reduction` monad whose `DisjT` layer replicates the WHOLE remaining
/// continuation per disjunct.  Concretely, when `solveSubstEqs SplitNow`
/// inside `refineSubst` produces N AC arms, each arm carries its own
/// `eq_store` (one of the `performSplit` results) into the subsequent
/// `substSystem` / `markGoalAsSolved` / `conjoinSystem` steps.  We
/// mirror that here by re-running the post-`solve_term_eqs` body once
/// per arm with that arm's eq_store installed.
///
/// Case-name disambiguation: callers push `(case_label, sys, fact)` per
/// returned entry.  When the same `case_label` shows up twice in the
/// upstream `Vec<(String, System, LNFact)>`, the proof-method dispatcher
/// (`proof_method.rs`:595-611) appends `_case_N` per HS's
/// `uniqueListBy ... distinguish cases` (ProofMethod.hs:308, with
/// `uniqueListBy` at ProofMethod.hs:91 and `distinguish` at
/// ProofMethod.hs:335).
/// HS-faithful split of `applySource` at the `conjoinSystem` boundary:
/// this half does match + refineSubst + restrict + someInst (the
/// `matchToGoal`→`refineSource`→someInst part of `_applySource`,
/// Sources.hs:336-468) and returns one `RefineArm` per surviving
/// refineSubst arm WITHOUT conjoining.  The caller dedups the arms
/// (HS `removeRedundantCases`, BEFORE conjoin) then calls
/// `conjoin_refine_arm` only on survivors — so the expensive bilinear
/// `conjoinSystem` re-narrow is paid only for cases HS actually keeps.
fn refine_source_case_action(
    ctx: &crate::constraint::solver::context::ProofContext,
    live_sys: &System,
    src: &Source,
    case_sys: &System,
    live_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
) -> Vec<RefineArm> {
    use crate::constraint::solver::reduction::{
        Reduction, SolveOutcome, SplitStrategy, bounds_max,
    };
    use tamarin_term::lterm::HasFrees;

    // Task #166 diagnostic: structured drop-reason tracing.  Set
    // TAM_DBG_APPLY_SOURCE=1 to log every drop site with case name +
    // reason.  Use this to track WHICH source-case drops at WHICH
    // step (match-fail, refineSubst-fail, conjoin-fail, etc.).
    let dbg_apply = tamarin_utils::env_gate!("TAM_DBG_APPLY_SOURCE");
    // Only consumed by the TAM_DBG_APPLY_SOURCE trace below.  Matching
    // the case by content deep-clones every case `System` via
    // `cases_or_empty()`, so skip it entirely in the common (untraced)
    // path.  (The `ptr::eq` fast path never matched: `cases_or_empty()`
    // returns fresh clones, never the `case_sys` pointer passed in.)
    let case_label: String = if dbg_apply {
        src.cases_or_empty().iter()
            .find_map(|(n, sys)|
                if std::ptr::eq(sys as *const _, case_sys as *const _) {
                    Some(n.clone())
                } else { None })
            .unwrap_or_else(|| {
                // Fallback: try matching by content (rule names + counts).
                let case_signature: Vec<String> = case_sys.nodes.iter()
                    .map(|(_, r)| crate::constraint::solver::reduction::rule_case_name(r))
                    .collect();
                src.cases_or_empty().iter()
                    .find_map(|(n, sys)| {
                        let s: Vec<String> = sys.nodes.iter()
                            .map(|(_, r)| crate::constraint::solver::reduction::rule_case_name(r))
                            .collect();
                        if s == case_signature { Some(n.clone()) } else { None }
                    })
                    .unwrap_or_else(|| format!("?({})",
                        case_signature.join(",").chars().take(50).collect::<String>()))
            })
    } else {
        String::new()
    };
    let dbg = |reason: &str| {
        if dbg_apply {
            eprintln!("[applySource] DROP case={} reason={} live_node={:?} fa_live.tag={:?}",
                case_label, reason, live_node, fa_live.tag);
        }
    };

    // Pull the abstract `cdGoal` (NodeId + LNFact) out of `src`.
    let (abstract_node_orig, abstract_action_orig) = match &src.goal {
        crate::constraint::constraints::Goal::Action(n, fa) => (n.clone(), fa.clone()),
        _ => { dbg("src-goal-not-Action"); return Vec::new(); },
    };
    if fa_live.tag != abstract_action_orig.tag
        || fa_live.terms.len() != abstract_action_orig.terms.len()
    {
        dbg("tag/arity-mismatch");
        return Vec::new();
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
    // HS's `_applySource` runs `someInst sysTh0` inside the Reduction
    // monad's FreshT (Sources.hs), which is initialized from the
    // LIVE system's global fresh counter — so the case's non-goal vars
    // get fresh indices above EVERY live var, not just the goal's frees.
    // Previously we shifted only past goal_max; that left case vars like
    // `vr.0`/`i1.0` at index 0, colliding with live's existing
    // `vr.0=Init_1`/`i1.0=Init_2` nodes at conjoinSystem→setNodes and
    // tripping shape_mismatch on cases HS keeps.  Closes BP cluster
    // (Joux PFS/EphkRev/establish, RYY/RYY_PFS key_secrecy, TAK1/
    // TAK1_eCK_like session_key_establish, Chen_Kudla key_secrecy_*).
    let live_max = system_max_idx(live_sys);
    let rename_shift = goal_max.max(live_max).saturating_add(1);
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
    if tamarin_utils::env_gate!("TAM_DBG_CASE_PRE_FRESHEN") {
        eprintln!("[case_pre_freshen] case={}: case_sys.nodes:", case_label);
        for (id, ru) in case_sys.nodes.iter() {
            let nm = crate::constraint::solver::reduction::rule_case_name(ru);
            if nm == "Serv_1" || nm == "Register_pk" || nm == "Client_1" {
                eprintln!("[case_pre_freshen]   node {:?} → {}", id, nm);
                for (i, p) in ru.premises.iter().enumerate() {
                    eprintln!("[case_pre_freshen]     prem[{}]: {:?}", i,
                        format!("{:?}", p).chars().take(1000).collect::<String>());
                }
                for (i, c) in ru.conclusions.iter().enumerate() {
                    eprintln!("[case_pre_freshen]     conc[{}]: {:?}", i,
                        format!("{:?}", c).chars().take(1000).collect::<String>());
                }
            }
        }
    }
    // TAM_DBG_CASE_DISJ=1: dump case_sys's eq_store.conj BEFORE freshen.
    if tamarin_utils::env_gate!("TAM_DBG_CASE_DISJ") {
        let trunc = if tamarin_utils::env_gate!("TAM_DBG_CASE_DISJ_FULL") { 9999 } else { 60 };
        for (i, d) in case_sys.eq_store.conj.iter().enumerate() {
            for (j, s) in d.substs.iter().enumerate() {
                let pairs: Vec<String> = s.to_list().iter()
                    .map(|(k, v)| format!("{}.{}/{:?}→{:?}", k.name, k.idx, k.sort,
                        format!("{:?}", v).chars().take(trunc).collect::<String>()))
                    .collect();
                eprintln!("[case_disj-pre] case={} disj[{}].subst[{}]={:?} entries=[{}]",
                    case_label, i, j, d.split_id, pairs.join(", "));
            }
        }
    }
    let renamed_case = freshen_system_keep_with_shift(
        case_sys, rename_shift, &empty_keep);
    // TAM_DBG_CASE_DISJ=1: dump renamed_case's eq_store.conj AFTER freshen.
    if tamarin_utils::env_gate!("TAM_DBG_CASE_DISJ") {
        let trunc = if tamarin_utils::env_gate!("TAM_DBG_CASE_DISJ_FULL") { 9999 } else { 60 };
        for (i, d) in renamed_case.eq_store.conj.iter().enumerate() {
            for (j, s) in d.substs.iter().enumerate() {
                let pairs: Vec<String> = s.to_list().iter()
                    .map(|(k, v)| format!("{}.{}/{:?}→{:?}", k.name, k.idx, k.sort,
                        format!("{:?}", v).chars().take(trunc).collect::<String>()))
                    .collect();
                eprintln!("[case_disj-post] case={} disj[{}].subst[{}]={:?} entries=[{}]",
                    case_label, i, j, d.split_id, pairs.join(", "));
            }
        }
    }

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

    // HS-faithful `doMatch (faTerm matchFact faPat <> iTerm matchLVar
    // iPat)` = `runReader (solveMatchLNTerm match) hnd` (Sources.hs:381,
    // 414).  `solveMatchLTerm` (Term/Unification.hs:209-214) runs the
    // native matcher and ONLY shells out to `matchViaMaude` on the
    // `Left ACProblem` branch; a `Left NoMatcher` returns `[]` with NO
    // Maude round-trip.  Mirror that 3-way split: native NoMatcher ⇒
    // bail (no Maude), native match ⇒ use it, NeedsAc ⇒ Maude fallback.
    let match_pairs: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = {
        use tamarin_term::unification::MatchOutcome;
        let problem = tamarin_term::rewriting::Match::DelayedMatches(pairs.clone());
        match tamarin_term::unification::solve_match_lterm::<
            tamarin_term::lterm::Name, _>(
            &tamarin_term::lterm::sort_of_name, problem,
        ) {
            MatchOutcome::Matched(s) => s.to_list(),
            MatchOutcome::NoMatcher => { dbg("match-empty"); return Vec::new(); }
            MatchOutcome::NeedsAc => {
                let match_eqs: Vec<_> = pairs.into_iter()
                    .map(|(t, p)| tamarin_term::rewriting::Equal { lhs: t, rhs: p })
                    .collect();
                let substs_res = ctx.maude.match_eqs(&match_eqs);
                let mut substs = match substs_res {
                    Ok(s) => s,
                    Err(_) => { dbg("maude-match-err"); return Vec::new(); },
                };
                if substs.is_empty() { dbg("match-empty"); return Vec::new(); }
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
    if tamarin_utils::env_gate!("TAM_DBG_APPLY_REFINE") {
        eprintln!("[apply_refine] case={} PRE-solve_term_eqs eq_store entries:", case_label);
        for (v, t) in refined.sys.eq_store.subst.to_list().iter().take(10) {
            eprintln!("[apply_refine]   {}.{}/{:?} → {:?}", v.name, v.idx, v.sort,
                format!("{:?}", t).chars().take(100).collect::<String>());
        }
    }
    // HS-faithful `solveSubstEqs` (Reduction.hs:736):
    //   solveTermEqs split [Equal (varTerm v) t | (v, t) <- substToList subst]
    // builds `Equal (varTerm v) t` with no conditional flip.
    let term_eqs: Vec<_> = match_pairs.into_iter()
        .map(|(v, t)| {
            let pattern_var_term = tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(v));
            tamarin_term::rewriting::Equal {
                lhs: pattern_var_term,
                rhs: t,
            }
        })
        .collect();
    // -----------------------------------------------------------------
    // refineSubst fan-out (HS Reduction.hs:712-733; `performSplit` use
    // at 723-725).
    //
    // HS's `solveTermEqs SplitNow` calls
    //     disjunctionOfList $ performSplit eqs2 splitId
    // when the AC unifier produces multiple disjunctive results.  In the
    // Reduction monad's `DisjT` layer this replicates the WHOLE remaining
    // continuation per arm — so each arm carries its own `sEqStore` into
    // the subsequent `substSystem` / `markGoalAsSolved` / `conjoinSystem`
    // steps that make up `_applySource` (HS Sources.hs).
    //
    // RS's `solve_term_eqs` returns `SolveOutcome::Cases(arms)` when N>1
    // AC arms survive per-arm simp; it does NOT install any arm into
    // `self.sys.eq_store` in that case.  Previously we treated `Cases` as
    // success and proceeded with `refined.sys` whose eq_store was still
    // the pre-call value — silently dropping every arm's Fresh-Fresh
    // bindings.  This caused the DH wrong-verdict cluster (KEA_plus +
    // 7 siblings): a `~tid → ~ekI`-style binding from one AC arm never
    // entered the live system, so HS's `Sessk_reveal_case_1` carried a
    // witness merge that contradicted, while RS's stale-eq-store version
    // didn't, leaving the lemma's existential reachable.
    //
    // Fix: when `Cases(arms)` returns, fan out — re-run the
    // post-`solve_term_eqs` continuation once per arm with that arm's
    // eq_store installed.  Each arm produces a distinct output entry; the
    // upstream caller pushes `(case_label, sys, fact)` per entry and the
    // proof-method dispatcher (`proof_method.rs`:595-611) handles
    // `_case_N` disambiguation when two entries share `case_label`,
    // matching HS's `uniqueListBy ... distinguish cases` (HS
    // ProofMethod.hs:308, with `uniqueListBy` at ProofMethod.hs:91 and
    // `distinguish` at ProofMethod.hs:335).
    //
    // Arm order is preserved from `EquationStore::perform_split`, which
    // matches HS's `performSplit eqs2 splitId` enumeration order (Maude
    // unifier result order).
    let arm_eq_stores: Vec<crate::tools::equation_store::EquationStore> =
        if term_eqs.is_empty() {
            // No refineSubst; keep current eq_store as the sole arm.
            if tamarin_utils::env_gate!("TAM_RS_DBG_APPLY_SRC_FANOUT_ALL") {
                eprintln!("[apply_src_fanout] case={} arms=0/skip n_term_eqs={}",
                    case_label, term_eqs.len());
            }
            vec![(*refined.sys.eq_store).clone()]
        } else {
            let outcome = refined.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs);
            match outcome {
                Err(_) | Ok(SolveOutcome::Contradictory) => {
                    if tamarin_utils::env_gate!("TAM_RS_DBG_APPLY_SRC_FANOUT_ALL") {
                        eprintln!("[apply_src_fanout] case={} arms=0/contra n_term_eqs={}",
                            case_label, term_eqs.len());
                    }
                    dbg("refineSubst-contradictory");
                    return Vec::new();
                }
                Ok(SolveOutcome::Linear(_)) => {
                    if tamarin_utils::env_gate!("TAM_RS_DBG_APPLY_SRC_FANOUT_ALL") {
                        eprintln!("[apply_src_fanout] case={} arms=1/linear n_term_eqs={}",
                            case_label, term_eqs.len());
                    }
                    // Single arm: solve_term_eqs already installed it
                    // into refined.sys.eq_store.  Mirror as a single-arm
                    // Vec so the post-continuation runs once with that
                    // store.
                    vec![(*refined.sys.eq_store).clone()]
                }
                Ok(SolveOutcome::Cases(arms)) => {
                    if tamarin_utils::env_gate!("TAM_RS_DBG_APPLY_SRC_FANOUT")
                        || tamarin_utils::env_gate!("TAM_RS_DBG_APPLY_SRC_FANOUT_ALL") {
                        eprintln!("[apply_src_fanout] case={} arms={} n_term_eqs={}",
                            case_label, arms.len(), term_eqs.len());
                    }
                    arms
                }
            }
        };

    // Fork off a per-arm continuation.  Each arm gets its own clone of
    // the post-refineSubst `refined.sys`, then runs `subst_system` →
    // `restrict_eq_store_to_stable_vars` → `freshen` → `conjoin` →
    // `solve_fact_eqs` → `close_trivial_chains` — same flow as before
    // but per-arm so each arm's eq_store substitutes through the rest
    // of the case body independently.
    let post_solve_sys_template = refined.sys.clone();
    // Each output entry is `(grafted_sys, live_action, refined_case)` —
    // the third element is the post-refineSubst+restrict case sub-system
    // BEFORE someInst+conjoinSystem.  Callers dedup on this to mirror
    // HS's `refineSource` → `removeRedundantCases` step which happens
    // BEFORE `_applySource`'s `someInst sysTh0 >> conjoinSystem sysTh`
    // (Sources.hs:131-148, 444-468).  Two refineSubst arms whose
    // post-restrict case sub-systems are alpha-equivalent should
    // collapse to one — without this dedup, RS conjoins both, and
    // any per-arm `setNodes:ruleInfoMismatch` (RS `shape_mismatch`)
    // drops cases HS keeps because HS never conjoined the duplicate.
    let mut out_arms: Vec<RefineArm> =
        Vec::with_capacity(arm_eq_stores.len());

    for arm_eq_store in arm_eq_stores {
        // Install this arm's eq_store into a fresh per-arm Reduction
        // whose system body is the post-refineSubst template.  This
        // mirrors HS's `DisjT` replication of the Reduction continuation
        // (Reduction.hs:724-725 `disjunctionOfList performSplit`).
        let mut refined = fork_arm_reduction(ctx, &post_solve_sys_template, arm_eq_store);
    if tamarin_utils::env_gate!("TAM_DBG_APPLY_REFINE") {
        eprintln!("[apply_refine] case={} POST-solve_term_eqs eq_store entries:", case_label);
        for (v, t) in refined.sys.eq_store.subst.to_list().iter().take(15) {
            eprintln!("[apply_refine]   {}.{}/{:?} → {:?}", v.name, v.idx, v.sort,
                format!("{:?}", t).chars().take(100).collect::<String>());
        }
    }
    refined.subst_system();
    if refined.sys.eq_store.is_false() {
        dbg("post-subst-eq-store-false");
        continue;
    }
    if tamarin_utils::env_gate!("TAM_DBG_APPLY_REFINE") {
        eprintln!("[apply_refine] case={} POST-subst:", case_label);
        for (id, ru) in refined.sys.nodes.iter() {
            let nm = crate::constraint::solver::reduction::rule_case_name(ru);
            if nm == "Serv_1" || nm == "Register_pk" {
                eprintln!("[apply_refine]   node {:?} → {}", id, nm);
                let trunc = if tamarin_utils::env_gate!("TAM_DBG_APPLY_REFINE_FULL") { 1000 } else { 280 };
                for (i, p) in ru.premises.iter().enumerate() {
                    eprintln!("[apply_refine]     prem[{}]: {:?}", i,
                        format!("{:?}", p).chars().take(trunc).collect::<String>());
                }
                for (i, c) in ru.conclusions.iter().enumerate() {
                    eprintln!("[apply_refine]     conc[{}]: {:?}", i,
                        format!("{:?}", c).chars().take(trunc).collect::<String>());
                }
                for (i, a) in ru.actions.iter().enumerate() {
                    eprintln!("[apply_refine]     act[{}]: {:?}", i,
                        format!("{:?}", a).chars().take(trunc).collect::<String>());
                }
            }
        }
    }
    // Mirror Haskell `refineSource ctxt (refineSubst subst) (set cdGoal goalTerm th)`
    // (Sources.hs:285,290): after refineSubst, restrict the case's
    // eq-store to `frees (cdGoal th) = frees goalTerm` — the LIVE
    // goal's free vars (since `set cdGoal goalTerm` was applied).
    // Drops any leftover abstract/rule-internal bindings introduced
    // during precompute and renamed via Step A.1.
    let runtime_stable = collect_node_and_fact_frees(live_node, fa_live);
    restrict_eq_store_to_stable_vars(&mut refined.sys, &runtime_stable);
    crate::state_trace::emit(
        "applySource_refined", Some(&live_goal_for_trace), &refined.sys);
    let refined_case = refined.sys;
    // Save a copy of the post-refineSubst+restrict case sub-system to
    // attach to each output entry — used by the caller to dedup
    // alpha-equivalent refineSubst arms across source cases
    // (HS Sources.hs `removeRedundantCases ctxt stableVars`).
    let refined_case_for_dedup = refined_case.clone();

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
    // reset the MaudeHandle's global `Arc<AtomicU64>` counter to
    // `avoid(live_sys) + 1` below, then `freshen_system_some_inst`
    // draws fresh idxs from it per unique LVar in traversal order.
    // ---------------------------------------------------------------
    let keep_vars = collect_node_and_fact_frees(live_node, fa_live);
    let post_refine_max = bounds_max(&refined_case);
    ctx.maude.ensure_above(post_refine_max);
    // HS-faithful `someInst`: traversal-order per-var fresh idx
    // allocation, matching Haskell's `someInst` + `importBinding`
    // (LTerm.hs:601-602 + Bind.hs:128-140).  Each unique LVar in
    // HS-mapFrees traversal order gets the next idx from the global
    // Maude counter.
    //
    // HS-faithful counter init: HS calls `runReduction (m <* simplifySystem)
    // ctxt sys (avoid sys)` per proof step (ProofMethod.hs:306), so the
    // FreshT counter resets to `avoid(live_sys) + 1` BEFORE each apply.
    // Reset Rust's global counter to match.  Safe because all live_sys
    // vars are < avoid(live_sys), so any new allocation at idx
    // ≥ avoid(live_sys)+1 won't collide.
    let avoid_live = bounds_max(live_sys);
    ctx.maude.reset_counter_to(avoid_live.saturating_add(1));
    let freshened_case = freshen_system_some_inst(&refined_case, &keep_vars, &ctx.maude);

    // TAM_RS_TRACE_APPLY_SRC=1 dumps live_sys + freshened case + post-conjoin
    // state.  Pairs with HS's TAM_HS_TRACE_APPLY_SRC for KAS_key_secrecy
    // divergence investigation.  Output: [APPLY_SRC] path=<casePath>
    // goal=<KU(...)> @ <node> case=<name>, then keep/shift_base/preFrees/
    // postFrees, plus live_sys nodes+subst+goals and POST-conjoin
    // nodes+subst+splits+goals.  Both pre- and post-conjoin dumps so we
    // can diff each phase against HS's equivalent.
    if tamarin_utils::env_gate!("TAM_RS_TRACE_APPLY_SRC") {
        let ls = |v: &tamarin_term::lterm::LVar| -> String {
            let sort = match v.sort {
                tamarin_term::lterm::LSort::Fresh => "~",
                tamarin_term::lterm::LSort::Pub   => "$",
                tamarin_term::lterm::LSort::Msg   => "",
                tamarin_term::lterm::LSort::Node  => "#",
                tamarin_term::lterm::LSort::Nat   => "%",
            };
            format!("{}{}.{}", sort, v.name, v.idx)
        };
        let collect_frees = |sys: &System| -> Vec<tamarin_term::lterm::LVar> {
            let mut out: Vec<tamarin_term::lterm::LVar> = Vec::new();
            let mut seen = std::collections::BTreeSet::new();
            let push = |v: &tamarin_term::lterm::LVar,
                        out: &mut Vec<tamarin_term::lterm::LVar>,
                        seen: &mut std::collections::BTreeSet<tamarin_term::lterm::LVar>| {
                if seen.insert(v.clone()) { out.push(v.clone()); }
            };
            for (id, ru) in sys.nodes.iter() {
                push(id, &mut out, &mut seen);
                ru.for_each_free(&mut |v| push(v, &mut out, &mut seen));
            }
            for e in &sys.edges {
                push(&e.src.0, &mut out, &mut seen);
                push(&e.tgt.0, &mut out, &mut seen);
            }
            for (g, _) in sys.goals.iter() {
                match g {
                    crate::constraint::constraints::Goal::Action(n, fa) => {
                        push(n, &mut out, &mut seen);
                        fa.for_each_free(&mut |v| push(v, &mut out, &mut seen));
                    }
                    crate::constraint::constraints::Goal::Premise(p, fa) => {
                        push(&p.0, &mut out, &mut seen);
                        fa.for_each_free(&mut |v| push(v, &mut out, &mut seen));
                    }
                    _ => {}
                }
            }
            out
        };
        let pre_frees = collect_frees(&refined_case);
        let post_frees = collect_frees(&freshened_case);
        let path = crate::constraint::solver::trace::case_path_string();
        eprintln!("[APPLY_SRC] path={} goal=KU({}) @ {} case={}",
            path,
            fa_live.terms.iter().map(|t| format!("{:?}",t)).collect::<Vec<_>>().join(","),
            ls(live_node), case_label);
        eprintln!("[APPLY_SRC]   keep=[{}]",
            keep_vars.iter().map(&ls).collect::<Vec<_>>().join(","));
        eprintln!("[APPLY_SRC]   freshAfter={}", ctx.maude.fresh_counter_peek());
        eprintln!("[APPLY_SRC]   preFrees=[{}]",
            pre_frees.iter().map(&ls).collect::<Vec<_>>().join(","));
        eprintln!("[APPLY_SRC]   postFrees=[{}]",
            post_frees.iter().map(ls).collect::<Vec<_>>().join(","));
    }

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
        None => { dbg("no-KU-action-in-freshened-case"); continue; },
    };

    // HS-faithful split: STOP here (BEFORE conjoinSystem).  The caller
    // dedups these arms (`removeRedundantCases`, Sources.hs:236-260) and
    // calls `conjoin_refine_arm` only on survivors, so the expensive
    // bilinear `conjoinSystem` re-narrow is never paid for a case HS
    // drops.
    out_arms.push(RefineArm {
        freshened_case,
        live_action,
        refined_case_for_dedup,
    });
    } // end `for arm_eq_store in arm_eq_stores`
    out_arms
}

/// HS-faithful conjoin half of `applySource` (`_applySource`,
/// Sources.hs:447-468) for a single surviving `RefineArm`: runs
/// `markGoalAsSolved` + `conjoinSystem` + the conjoin-fanout drain +
/// E.5 edge fact-eq propagation + close-trivial-chains, returning one
/// `(grafted_sys, live_action, refined_case_for_dedup)` per output arm.
/// Called only on cases that survived `removeRedundantCases`.
fn conjoin_refine_arm(
    ctx: &crate::constraint::solver::context::ProofContext,
    live_sys: &System,
    live_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
    arm: RefineArm,
) -> Vec<(System, crate::fact::LNFact, System)> {
    use crate::constraint::solver::reduction::{Reduction, SolveOutcome};

    let RefineArm { freshened_case, live_action, refined_case_for_dedup } = arm;

    // dbg/trace plumbing (mirrors the refine half).  `case_label` is not
    // recoverable post-split; left empty (TAM_DBG_APPLY_SOURCE drop traces
    // here print case= blank, which is fine — the refine half already
    // logged the labelled drops).
    let dbg_apply = tamarin_utils::env_gate!("TAM_DBG_APPLY_SOURCE");
    let case_label = String::new();
    let dbg = |reason: &str| {
        if dbg_apply {
            eprintln!("[applySource] DROP case={} reason={} live_node={:?} fa_live.tag={:?}",
                case_label, reason, live_node, fa_live.tag);
        }
    };
    let live_goal_for_trace = crate::constraint::constraints::Goal::Action(
        live_node.clone(), fa_live.clone());

    let mut out_arms: Vec<(System, crate::fact::LNFact, System)> = Vec::new();

    // ---------------------------------------------------------------
    // B — `markGoalAsSolved "precomputed" goal`.
    // E — `conjoinSystem sysTh`.
    // ---------------------------------------------------------------
    let mut r = Reduction::new(ctx, live_sys.clone());
    let live_goal = crate::constraint::constraints::Goal::Action(
        live_node.clone(), fa_live.clone());
    // HS-faithful (Sources.hs:196-216): `solveAllSafeGoals.safeGoal`
    // returns `not (isKUFact fa)` for ActionG (Sources.hs:202), so
    // HS's saturate-time precompute NEVER picks a KU action goal
    // and therefore never calls `applySource` on one (Sources.hs
    // `markGoalAsSolved "precomputed" goal`).  Any precompute-time
    // resolution of a KU goal in HS happens only through chain
    // closure / N5_u merging / N6 ordering — none of which mark
    // the KU ActionG goal as solved in the case sub-system.
    //
    // RS reaches this site during saturate via the chain-fold path
    // (`saturate_out_premise` → ... → `solve_with_source_cases_action_with_ctx`
    // → `conjoin_refine_arm`).  Marking the live_goal as
    // solved during saturate produces case sub-systems with
    // pre-solved KU(...) ActionG goals; `conjoin_system`'s
    // `combineGoalStatus` (Reduction.hs:510-511 `solved1 || solved2`)
    // then stamps solved=true on the live system's KU goals — the
    // runtime `case c_S` (or equivalent constructor) proof step HS
    // emits never fires because the goal is no longer "open".
    // Concrete manifestation: Yubikey's Login_reachable skipped
    // two `case c_S` steps (`... → BuyANewYubikey → c_S → c_S → SOLVED`
    // in HS, `... → BuyANewYubikey → SOLVED` in RS).
    //
    // Gate the mark on `!in_precompute_mode()` so saturate-time
    // grafts emit a sub-system whose ActionG goals match HS's
    // safe-goal-only saturation outputs.
    if let Some(slot) = r.sys.goals_mut().iter_mut().find(|(g, _)| g == &live_goal) {
        if !in_precompute_mode() {
            slot.1.solved = true;
        }
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
        return out_arms;
    }

    // Drain `conjoin_system`'s step-12 fanout (HS Reduction.hs:736
    // `solveSubstEqs SplitNow` inside DisjT).  arm[0] is in r.sys;
    // arms[1..] are post-substSystem snapshots in
    // `pending_conjoin_arm_systems`.  We replay the rest of
    // `_applySource` (E.5 edge_eqs, F close_trivial_chains, output
    // push) per stashed sys.  HS-equivalent: each `DisjT` arm
    // continues independently through the post-`solveSubstEqs`
    // continuation.
    let conjoin_arm_systems = std::mem::take(
        &mut r.pending_conjoin_arm_systems);
    let dbg_cf = tamarin_utils::env_gate!("TAM_RS_DBG_CONJOIN_FANOUT");
    if dbg_cf && !conjoin_arm_systems.is_empty() {
        eprintln!("[conjoin_fanout] conjoin_refine_arm drained {} extra arms (case={})",
            conjoin_arm_systems.len(), case_label);
    }
    // Build a Vec<Reduction> over arm0 + extra-arms so the post-conjoin
    // work loop runs uniformly.  arm0 is the in-place `r`; arms[1..]
    // each get a fresh Reduction with the pre-drained sys installed.
    let mut arm_reductions: Vec<Reduction> = Vec::with_capacity(
        1 + conjoin_arm_systems.len());
    arm_reductions.push(r);
    for sys_i in conjoin_arm_systems {
        arm_reductions.push(Reduction::new(ctx, sys_i));
    }

    // E.5 — edge fact-equality propagation (see per-arm comment below).
    // `live_node_ids` depends only on `live_sys` (an immutable param,
    // invariant across arms), so build it ONCE here instead of cloning
    // every node id on each arm iteration.
    let live_node_ids = collect_node_ids(live_sys);

    for mut r in arm_reductions {

    // ---------------------------------------------------------------
    // E.5 — edge fact-equality propagation.  Mirror the equivalent
    // step in `apply_source_case_premise`.  After conjoin, walk every
    // edge in the joined system and ensure its conclusion fact and
    // premise fact are unified.  Without this, a Serv_1 source-case
    // grafted alongside an existing Register_pk produces a second
    // Register_pk whose `$A` is at a different LVar than the
    // lemma-chain Register_pk's `$A`.  The two `!Ltk`/`!Pk` chains
    // never coalesce, and the lemma's universal
    // `∀a. AnswerRequest($S, ~k) @ a ⇒ ⊥` matcher fails when
    // Serv_1's action references `$S.Pub.0` while the lemma's
    // universal references `$S.Pub.1`.
    //
    // SCOPING (HS-faithful): HS's `conjoinSystem` (Reduction.hs:660-690)
    // performs NO edge fact-equality solve at all — `joinSets sEdges`
    // (Reduction.hs:667) unions the edge SET and relies on the saturated
    // case being edge-consistent.  This E.5 step is an RS-only compensation
    // for saturate output that isn't fully edge-consistent.  It MUST only
    // touch edges INTRODUCED by the grafted case — re-solving a
    // pre-existing LIVE edge re-narrows the live equation store and can
    // collapse live disjunctions HS keeps (Joux_EphkRev: re-solving the
    // live em-exponent Kd-pair chain edge folded the `splitEqs(3)/(4)`
    // disjunctions, turning HS's Split×3/×4 cascade into RS's Split×1).
    // A grafted edge is one with at least one endpoint NOT a pre-existing
    // live node.  `live_node_ids` is computed once above the loop.
    let edge_eqs: Vec<_> = r.sys.edges.iter().filter_map(|e| {
        if live_node_ids.contains(&e.src.0)
            && live_node_ids.contains(&e.tgt.0)
        {
            return None;
        }
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
    if tamarin_utils::env_gate!("TAM_DBG_APPLY_E5") {
        let path = crate::constraint::solver::trace::case_path_string();
        eprintln!("[conjoin_refine_arm E.5] path={} edge_eqs.len={}", path, edge_eqs.len());
        for (i, e) in edge_eqs.iter().enumerate() {
            eprintln!("  eq[{}]: {:?} = {:?}", i,
                format!("{:?}", e.lhs).chars().take(160).collect::<String>(),
                format!("{:?}", e.rhs).chars().take(160).collect::<String>());
        }
    }
    // E.5 fanout: `solve_fact_eqs(SplitNow)` may return `Cases(arms)`
    // when the edge-fact unification yields multiple AC unifier arms
    // (HS `solveFactEqs SplitNow` → `solveTermEqs SplitNow` →
    // `disjunctionOfList $ performSplit eqs2 splitId` forks the
    // `Reduction`/`DisjT` continuation, Reduction.hs:712-733;
    // `performSplit` use at 723-725).  We
    // mirror that here: each arm continues the rest of `_applySource`
    // (F close_trivial_chains + output push) independently.  Each arm's
    // eq-store (from `perform_split`) PRESERVES the live system's other
    // disjunctions — `solve_term_eqs`'s `Cases` branch does NOT
    // reinstall `self.sys.eq_store` (it leaves the `mem::take`'d default
    // store, equation_store.rs:2159 / reduction.rs Cases arm), so the
    // caller MUST install an arm.  Previously this code only handled
    // `Linear`/`Contradictory` and fell through on `Cases` with `r.sys`
    // carrying the wiped default eq-store (conj=[], next_split=0) — that
    // silently dropped the live `splitEqs` disjunctions, collapsing
    // Joux_EphkRev's EphkRev cascade (HS Split×3/×4 → RS Split×1).
    let mut e5_arm_systems: Vec<System> = Vec::new();
    if !edge_eqs.is_empty() {
        let res = r.solve_fact_eqs(
            crate::constraint::solver::reduction::SplitStrategy::SplitNow,
            &edge_eqs);
        match res {
            Err(_) | Ok(SolveOutcome::Contradictory) => {
                crate::state_trace::emit(
                    "applySource_drop_edge_eqs", Some(&live_goal_for_trace), &r.sys);
                continue;
            }
            Ok(SolveOutcome::Linear(_)) => {
                // Single arm: `solve_term_eqs` already installed it into
                // `r.sys.eq_store`.
                r.subst_system();
                e5_arm_systems.push(r.sys.clone());
            }
            Ok(SolveOutcome::Cases(arms)) => {
                // Multi-arm fanout: `solve_term_eqs` returned the arms
                // WITHOUT installing any into `r.sys`.  Install each arm
                // into a clone of the pre-solve `r.sys`, run substSystem,
                // and continue the rest of `_applySource` per arm.
                let template = r.sys.clone();
                subst_arms_into(ctx, &template, arms, &mut e5_arm_systems);
                if e5_arm_systems.is_empty() { continue; }
            }
        }
    } else {
        e5_arm_systems.push(r.sys.clone());
    }

    for r_sys in e5_arm_systems {
    let mut r = Reduction::new(ctx, r_sys);

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

    // (No RS-only empty-subst `apply_eq_store` variant re-filter here: HS has
    // none; the conflicting-variant drop is edge-driven via `solveFactEqs`
    // (E.5), which RS mirrors. A second re-key here collapsed distinct
    // witnesses and rotated split ordering — verify_checksign_test::test4/5.)

    crate::state_trace::emit(
        "applySource_out", Some(&live_goal_for_trace), &r.sys);
    out_arms.push((r.sys, live_action.clone(), refined_case_for_dedup.clone()));
    } // end `for r_sys in e5_arm_systems`
    } // end `for r in arm_reductions`
    out_arms
}

/// Haskell-faithful `applySource` for Premise goals.  Mirrors
/// `conjoin_refine_arm` step-for-step, with the Premise-specific
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
) -> Vec<System> {
    use crate::constraint::solver::reduction::{
        Reduction, SolveOutcome, SplitStrategy, bounds_max,
    };
    use tamarin_term::lterm::HasFrees;

    let dbg_apply = tamarin_utils::env_gate!("TAM_DBG_APPLY_SOURCE");
    // Only consumed by the TAM_DBG_APPLY_SOURCE trace below.  Matching
    // the case by content deep-clones every case `System` via
    // `cases_or_empty()`, so skip it entirely in the common (untraced)
    // path.  (The `ptr::eq` fast path never matched: `cases_or_empty()`
    // returns fresh clones, never the `case_sys` pointer passed in.)
    let case_label: String = if dbg_apply {
        src.cases_or_empty().iter()
            .find_map(|(n, sys)|
                if std::ptr::eq(sys as *const _, case_sys as *const _) {
                    Some(n.clone())
                } else { None })
            .unwrap_or_else(|| {
                // Fallback: try matching by content (rule names + counts).
                let case_signature: Vec<String> = case_sys.nodes.iter()
                    .map(|(_, r)| crate::constraint::solver::reduction::rule_case_name(r))
                    .collect();
                src.cases_or_empty().iter()
                    .find_map(|(n, sys)| {
                        let s: Vec<String> = sys.nodes.iter()
                            .map(|(_, r)| crate::constraint::solver::reduction::rule_case_name(r))
                            .collect();
                        if s == case_signature { Some(n.clone()) } else { None }
                    })
                    .unwrap_or_else(|| format!("?({})",
                        case_signature.join(",").chars().take(50).collect::<String>()))
            })
    } else {
        String::new()
    };
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
            _ => { dbg("src-goal-not-Premise"); return Vec::new(); },
        };
    if fa_live.tag != abstract_prem_fact_orig.tag
        || fa_live.terms.len() != abstract_prem_fact_orig.terms.len()
    {
        dbg("tag/arity-mismatch");
        return Vec::new();
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
    // HS's `_applySource` runs `someInst sysTh0` inside the Reduction
    // monad's FreshT (Sources.hs), which is initialized from the
    // LIVE system's global fresh counter — so the case's non-goal vars
    // get fresh indices above EVERY live var, not just the goal's frees.
    // Previously we shifted only past goal_max; that left case vars like
    // `vr.0`/`i1.0` at index 0, colliding with live's existing
    // `vr.0=Init_1`/`i1.0=Init_2` nodes at conjoinSystem→setNodes and
    // tripping shape_mismatch on cases HS keeps.  Closes BP cluster
    // (Joux PFS/EphkRev/establish, RYY/RYY_PFS key_secrecy, TAK1/
    // TAK1_eCK_like session_key_establish, Chen_Kudla key_secrecy_*).
    let live_max = system_max_idx(live_sys);
    let rename_shift = goal_max.max(live_max).saturating_add(1);
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
    // HS-faithful `doMatch` (Sources.hs:390,414) — see the action-path
    // twin above: only the `NeedsAc` (HS `Left ACProblem`) branch shells
    // out to Maude; `NoMatcher` returns `[]` natively.
    let match_pairs: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> = {
        use tamarin_term::unification::MatchOutcome;
        let problem = tamarin_term::rewriting::Match::DelayedMatches(pairs.clone());
        match tamarin_term::unification::solve_match_lterm::<
            tamarin_term::lterm::Name, _>(
            &tamarin_term::lterm::sort_of_name, problem,
        ) {
            MatchOutcome::Matched(s) => s.to_list(),
            MatchOutcome::NoMatcher => { dbg("match-empty"); return Vec::new(); }
            MatchOutcome::NeedsAc => {
                let match_eqs: Vec<_> = pairs.into_iter()
                    .map(|(t, p)| tamarin_term::rewriting::Equal { lhs: t, rhs: p })
                    .collect();
                let substs_res = ctx.maude.match_eqs(&match_eqs);
                let mut substs = match substs_res {
                    Ok(s) => s,
                    Err(_) => { dbg("maude-match-err"); return Vec::new(); },
                };
                if substs.is_empty() { dbg("match-empty"); return Vec::new(); }
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
    for (g, _) in renamed_case.goals_mut().iter_mut() {
        if let crate::constraint::constraints::Goal::Premise(p, _) = g {
            if *p == pat_prem {
                *p = new_prem.clone();
            }
        }
    }

    // TAM_RS_TRACE_APPLY_SRC_PREM=1: dump per-case match unifier so HS↔RS
    // unifier-selection diffs are visible.  Logs the live goal, the case
    // being applied, and the match_pairs (the substitution produced by
    // matchToGoal / refineSubst-input).  Pair with HS's same flag.
    if tamarin_utils::env_gate!("TAM_RS_TRACE_APPLY_SRC_PREM") {
        let path = crate::constraint::solver::trace::case_path_string();
        let live_fact = format!("{:?}", fa_live);
        let live_fact = live_fact.chars().take(220).collect::<String>();
        eprintln!("[APPLY_SRC_PREM] path={} live={}@{:?}.p{} case={}",
            path, live_fact, live_node, live_prem_idx.0, case_label);
        for (v, t) in &match_pairs {
            let t_str = format!("{:?}", t).chars().take(200).collect::<String>();
            eprintln!("[APPLY_SRC_PREM]   subst {}.{}/{:?} -> {}",
                v.name, v.idx, v.sort, t_str);
        }
    }

    // A.3 — refineSubst: solveSubstEqs SplitNow subst >> substSystem.
    let mut refined = Reduction::new(ctx, renamed_case);
    // HS-faithful `solveSubstEqs` (Reduction.hs:736): build
    // `Equal (varTerm v) t` with no conditional flip.
    let term_eqs: Vec<_> = match_pairs.into_iter()
        .map(|(v, t)| {
            let pattern_var_term = tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(v));
            tamarin_term::rewriting::Equal {
                lhs: pattern_var_term,
                rhs: t,
            }
        })
        .collect();
    // HS-faithful multi-arm fanout (Reduction.hs:724-725 + Sources.hs:330-333):
    // `refineSubst subst = solveSubstEqs SplitNow subst >> substSystem`.
    // `solveSubstEqs SplitNow` runs `disjunctionOfList $ performSplit eqs2
    // splitId` when the AC unifier returns multiple solutions.  Each arm
    // becomes a separate `Reduction` branch and `conjoinSystem sysTh`
    // runs once per arm — producing one Source-applied System per arm.
    //
    // Mirror `conjoin_refine_arm`'s pattern: capture `Cases(arms)`
    // from `solve_term_eqs` and re-run the post-`solve_term_eqs`
    // continuation once per arm.  Without this, a multiset Counter
    // premise solve yielded by HS as `Inc_case_1 | Inc_case_2` collapsed
    // to a single Inc case in RS (the second AC arm's eq_store was
    // silently dropped).
    let arm_eq_stores: Vec<crate::tools::equation_store::EquationStore> =
        if term_eqs.is_empty() {
            vec![(*refined.sys.eq_store).clone()]
        } else {
            let outcome = refined.solve_term_eqs(SplitStrategy::SplitNow, &term_eqs);
            match outcome {
                Err(_) | Ok(SolveOutcome::Contradictory) => {
                    dbg("refineSubst-contradictory");
                    return Vec::new();
                }
                Ok(SolveOutcome::Linear(_)) => {
                    vec![(*refined.sys.eq_store).clone()]
                }
                Ok(SolveOutcome::Cases(arms)) => {
                    if tamarin_utils::env_gate!("TAM_RS_DBG_APPLY_SRC_FANOUT") {
                        eprintln!("[apply_src_prem_fanout] case={} arms={}",
                            case_label, arms.len());
                    }
                    arms
                }
            }
        };

    let post_solve_sys_template = refined.sys.clone();
    let mut out_arms: Vec<System> = Vec::with_capacity(arm_eq_stores.len());

    // E.5 — `prem_live_node_ids` depends only on `live_sys` (an immutable
    // param, invariant across arms), so build it ONCE here instead of
    // cloning every node id on each arm iteration.  See the per-arm E.5
    // comment below.
    let prem_live_node_ids = collect_node_ids(live_sys);

    for arm_eq_store in arm_eq_stores {
        let mut refined = fork_arm_reduction(ctx, &post_solve_sys_template, arm_eq_store);

    refined.subst_system();
    if refined.sys.eq_store.is_false() {
        dbg("post-subst-eq-store-false");
        continue;
    }
    let runtime_stable = collect_node_and_fact_frees(live_node, fa_live);
    restrict_eq_store_to_stable_vars(&mut refined.sys, &runtime_stable);
    crate::state_trace::emit(
        "applySource_prem_refined", Some(&live_goal_for_trace), &refined.sys);
    let refined_case = refined.sys;

    // D — someInst keepVarBindings.
    let keep_vars = collect_node_and_fact_frees(live_node, fa_live);
    let post_refine_max = bounds_max(&refined_case);
    ctx.maude.ensure_above(post_refine_max);
    // HS-faithful `someInst`: traversal-order per-var fresh idx
    // allocation, matching Haskell's `someInst` + `importBinding`
    // (LTerm.hs:601-602 + Bind.hs:128-140).  Each unique LVar in
    // HS-mapFrees traversal order gets the next idx from the global
    // Maude counter.
    //
    // HS-faithful counter init: HS calls `runReduction (m <* simplifySystem)
    // ctxt sys (avoid sys)` per proof step (ProofMethod.hs:306), so the
    // FreshT counter resets to `avoid(live_sys) + 1` BEFORE each apply.
    // Reset Rust's global counter to match.  Safe because all live_sys
    // vars are < avoid(live_sys), so any new allocation at idx
    // ≥ avoid(live_sys)+1 won't collide.
    let avoid_live = bounds_max(live_sys);
    ctx.maude.reset_counter_to(avoid_live.saturating_add(1));
    let freshened_case = freshen_system_some_inst(&refined_case, &keep_vars, &ctx.maude);
    // B+E — markGoalAsSolved + conjoinSystem.
    let mut r = Reduction::new(ctx, live_sys.clone());
    let live_goal = crate::constraint::constraints::Goal::Premise(
        (live_node.clone(), live_prem_idx), fa_live.clone());
    if let Some(slot) = r.sys.goals_mut().iter_mut().find(|(g, _)| g == &live_goal) {
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
        continue;
    }

    // E.5 — edge fact-equality propagation.  Mirror Haskell's runtime
    // `insertEdges` (Reduction.hs:278-280) which calls `solveFactEqs SplitNow`
    // on every new edge so producer-conclusion ⇆ consumer-premise terms
    // unify before downstream `insertImpliedFormulas` runs.
    //
    // `conjoin_system` copies edges (Reduction.hs's `joinSets sEdges`) but
    // doesn't run solveFactEqs on them.  In Haskell the runtime path goes
    // `solvePremise → insertEdges → solveFactEqs` BEFORE conjoin reaches
    // the eq-pass; here we install the source case's edges via conjoin
    // directly, so we must re-fire fact-equality on them.
    //
    // Without this: Minimal_HashChain::Success_charn case Gen_Stop_case_1
    // installs an `!Final(kZero)` ←→ `!Final(kOrig)` edge but never unifies
    // kZero ⇆ kOrig, so the IH guard `ChainKey(kOrig)` can't match the
    // Gen_Stop node's `ChainKey(kZero)` action and gfalse never enters
    // sFormulas → Rust does an extra solve step where Haskell sees
    // `by contradiction /* from formulas */`.  Same pattern as the
    // action-path edge fact-equality fix at sources.rs:4549-4568.
    // SCOPING (HS-faithful): the E.5 edge-fact solve must only touch edges
    // INTRODUCED by the grafted source case, NOT pre-existing LIVE edges.
    // HS's `conjoinSystem` (Reduction.hs:660-690) does NO edge solve at all —
    // `joinSets sEdges` (Reduction.hs:667) unions the edge SET and lets the
    // node-merge (`setNodes` → `solveRuleEqs SplitLater`) unify producer/consumer
    // multisets of LIVE-LIVE edges LAZILY (as a deferred AC `splitEqs`).  RS's
    // premise E.5 eagerly `solve_fact_eqs(SplitNow)`s every edge; re-solving a
    // LIVE-LIVE edge re-narrows the live equation store and collapses
    // disjunctions HS keeps deferred.  On alethea selectionphase this PINS the
    // witness BB_2/AgSt_BB2 multiset code ('1') on the live `vr.5 → vr.11`
    // edge before the `#a3` AgSt_A3 node-merge fires, turning HS's 2-unifier
    // SplitLater merge into RS's pinned 1-unifier APPLY — which collapses
    // `#a3`'s multiset nonce onto the witness `no1.0` (HS keeps it the fresh
    // `no1.1`, with `#a3`'s y's fresh `.2`).  This is the SAME live-edge
    // hazard already guarded on the ACTION-path E.5 (sources.rs:4549-4568,
    // citing Joux_EphkRev's collapsed em-exponent splitEqs cascade); the
    // premise path was missing the guard.  A grafted edge has at least one
    // endpoint that is NOT a pre-existing live node — only those get the
    // eager solve.  `prem_live_node_ids` is computed once above the loop.
    let edge_eqs: Vec<_> = r.sys.edges.iter().filter_map(|e| {
        if prem_live_node_ids.contains(&e.src.0)
            && prem_live_node_ids.contains(&e.tgt.0)
        {
            return None;
        }
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
    // E.5 fanout: `solve_fact_eqs(SplitNow)` may return `Cases(arms)`
    // when the edge-fact unification yields multiple AC unifier arms.
    // `solve_term_eqs`'s `Cases` branch does NOT reinstall `r.sys.eq_store`
    // (it leaves the `mem::take`'d default store), so we MUST install each
    // arm — otherwise the system proceeds with a wiped eq-store, silently
    // dropping every live/grafted disjunction.  This mirrors the action
    // variant's E.5 fanout; the premise path previously only branched on
    // Err/Contradictory and fell through on `Cases` with the wiped store.
    // Continue the rest of `_applySource` (F + push) per arm.
    let mut e5_arm_systems: Vec<System> = Vec::new();
    if !edge_eqs.is_empty() {
        let res = r.solve_fact_eqs(
            crate::constraint::solver::reduction::SplitStrategy::SplitNow,
            &edge_eqs);
        match res {
            Err(_) | Ok(SolveOutcome::Contradictory) => {
                crate::state_trace::emit(
                    "applySource_prem_drop_edge_eqs",
                    Some(&live_goal_for_trace), &r.sys);
                continue;
            }
            Ok(SolveOutcome::Linear(_)) => {
                r.subst_system();
                e5_arm_systems.push(r.sys.clone());
            }
            Ok(SolveOutcome::Cases(arms)) => {
                let template = r.sys.clone();
                subst_arms_into(ctx, &template, arms, &mut e5_arm_systems);
                if e5_arm_systems.is_empty() { continue; }
            }
        }
    } else {
        e5_arm_systems.push(r.sys.clone());
    }

    for r_sys in e5_arm_systems {
    let mut r = Reduction::new(ctx, r_sys);

    // F — close trivial chains.
    close_trivial_chains_in_graft(&mut r);

    // G — RS-only `apply_eq_store(empty_subst)` variant SplitG re-filter.
    //
    // HS HAS NO STANDALONE EMPTY-SUBST `applyEqStore` REFILTER.  HS's
    // `applyEqStore` (EquationStore.hs:348) is only ever called with a
    // REAL `asubst` (from `solveSubstEqs`/`solveFactEqs`/`addEqs`); the
    // variant-drop for conflicting variants happens organically when the
    // conflicting binding enters via the normal solve path.  In particular
    // HS's `insertEdges` (Reduction.hs:278-280) runs `solveFactEqs SplitNow`
    // on every new edge's producer-conclusion ⇆ consumer-premise pair, and
    // THAT applyEqStore (with the real edge binding) drops a variant whose
    // range conflicts (e.g. TESLA Receiver0b variant `z → verify(...)`
    // vs the edge's `z → true`).  Step E.5 above already mirrors this
    // edge-driven `solve_fact_eqs`, so the variant-drop is HS-faithful
    // WITHOUT this extra call.
    //
    // This standalone empty-subst re-key was an RS-only artifact: with an
    // empty `asubst`, `newsubst = eqsSubst` and `applyBound` RE-KEYS the
    // surviving variants' witnesses a SECOND time (after solveTermEqs
    // already keyed them once).  Because each per-variant `applyBound`
    // resets the fresh counter to the same base (HS-faithful per-call
    // `evalFreshAvoiding`), the second re-key collapses two distinct
    // witnesses onto the SAME idx (e.g. verify_checksign_test::test4/test5:
    // sign→~k.15 and checksign→~k.15 COLLIDE, where HS keeps sign→~k.14,
    // checksign→~k.11 distinct).  The collision falls through `Ord
    // LNSubstVFresh` to the next key and rotates the 2-way split (RS picks
    // split_case_2 where HS picks split_case_1).

    crate::state_trace::emit(
        "applySource_prem_out", Some(&live_goal_for_trace), &r.sys);
    out_arms.push(r.sys);
    } // end `for r_sys in e5_arm_systems`
    } // end `for arm_eq_store in arm_eq_stores`
    out_arms
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
            // HS-faithful: never auto-close a chain that `openChainGoals`
            // (Goals.hs:99-108) keeps as an OPEN ranked goal.  A DnK
            // chain whose conclusion is NOT a Msg-sorted variable (a
            // concrete app OR a Fresh/Pub/Nat name) is ALWAYS open in HS
            // (`otherwise -> not solved`); HS solves it via the explicit
            // `solveChain` proof method, never via an eager graft-time
            // direct edge.  RS's over-eager closure here dropped the
            // deconstruction chain `(#vl,0)~~>(#vk,0)` (conc KD(~x),
            // Fresh-sorted) during the RFID_Simple `!KU(aenc)` Alice
            // graft, where HS keeps it open and renders it as
            // `solve( (#vl,0)~~>(#vk,0) ) case Var_fresh_1_x`.  Gate on
            // the canonical `openGoals` mirror so RS leaves open exactly
            // what HS leaves open; only chains HS itself auto-handles
            // (union-all-known) remain eligible for direct-edge closure.
            if crate::constraint::solver::goals::is_open_for_saturate(
                &Goal::Chain(c.clone(), p.clone()), &r.sys)
            {
                return None;
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
            Err(_) | Ok(SolveOutcome::Contradictory) | Ok(SolveOutcome::Cases(_)) => {
                // Direct-edge closure not possible, OR it SPLIT into
                // multiple AC arms.  On the `Cases` path `solve_term_eqs`
                // does NOT reinstall the eq-store (it leaves the
                // `mem::take`'d default), so continuing would corrupt the
                // system with a wiped store; and this function's contract
                // is explicitly "if Branch 1 fails or splits, leave the
                // chain as-is".  Restore the snapshot and bail — the chain
                // stays open for the search layer (Branch 2 destructor or
                // Disj-case).
                r.sys = snapshot;
                break;
            }
            Ok(SolveOutcome::Linear(_)) => {
                // Single arm: `solve_term_eqs` installed it.  Mark the
                // chain solved.
                let chain_goal = Goal::Chain(c, p);
                if let Some(slot) = r.sys.goals_mut().iter_mut()
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
/// live goal's `live_node`.  Unlike a premise-source graft, no premise
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
    for (id, rule) in case_sys.nodes.iter() {
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
    // The case's pre-solved goals must stay marked solved in the live
    // system, or downstream
    // search re-picks them as `case Register_pk` for already-resolved
    // premises (the KAS2_eCK case_1.Resp_2 divergence).
    for (g, st) in case_sys.goals.iter() {
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
            out.goals_mut().push((renamed_goal, st.clone()));
        }
    }
    let live_goal = crate::constraint::constraints::Goal::Action(
        live_node.clone(), fa_live.clone());
    if let Some(slot) = out.goals_mut().iter_mut().find(|(g, _)| g == &live_goal) {
        // HS-faithful: see the matching gate in `conjoin_refine_arm`.
        // `solveAllSafeGoals.safeGoal` (Sources.hs:202) excludes KU
        // ActionG goals from saturate-time dispatch, so applying a
        // source-case for a KU goal during saturate must not mark
        // the live goal as solved — otherwise the case sub-system
        // carries pre-solved KU(...) ActionG goals into the live
        // system via `conjoin_system`'s `combineGoalStatus`.
        if !in_precompute_mode() {
            slot.1.solved = true;
        }
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
    out.eq_store_mut().subst = tamarin_term::subst::Subst::from_list(merged_pairs);
    Some(out)
}

// =============================================================================
// removeRedundantCases — HS Sources.hs
// =============================================================================
//
// Direct port of:
//
//   removeRedundantCases :: ProofContext -> [LVar] -> (a -> System) ->  [a] -> [a]
//   removeRedundantCases ctxt stableVars getSys cases0 =
//       if enableBP msig || enableMSet msig then cases else cases0
//     where
//       decoratedCases = map (second addNormSys) $  zip [(0::Int)..] cases0
//       cases = map (fst . snd) . sortOn fst
//             . sortednubBy (\(_,(_, x)) (_,(_, y)) -> compareSystemsUpToNewVars x y)
//             $ decoratedCases
//       addNormSys = id &&&
//         ((modify sEqStore dropNameHintsBound) . renameDropNameHints . getSys)
//       orderedVars sys =
//           filter ((/= LSortNode) . lvarSort) $ map fst . sortOn snd . varOccurences $ sys
//       renameDropNameHints sys =
//         (`evalFresh` avoid stableVars) . (`evalBindT` stableVarBindings) $ do
//             _ <- renameDropNamehint (orderedVars sys)
//             renameDropNamehint sys
//         where stableVarBindings = M.fromList (map (\v -> (v, v)) stableVars)
//
// Where:
//   varOccurences sys: walks `_sNodes` ONLY (System's foldFreesOcc
//     commented out everything except field a). Produces
//     [(LVar, Set Occurence)] where Occurence = [String].
//   renameDropNamehint: assigns each LVar a fresh idx with name "".
//   compareSystemsUpToNewVars: compareNodesUpToNewVars first; if EQ
//     fall through to structural compare on (b..m, empty nodes).
//   compareRulesUpToNewVars: ignores `_rNewVars`.
//   dropNameHintsBound: drops name hints in `eqStore.conj` VFresh substs.
//
// Implementation strategy (per HS):
//   1. Gate on BP/MSet — non-BP/MSet returns cases0 as-is.
//   2. For each case build a canonical key from the normalised system.
//      The normalisation walks free vars in HS-determined order
//      (varOccurences-ordered first, then foldFrees), assigning each a
//      fresh idx with empty name. Then keys excluding rule.new_vars
//      capture exactly what `compareSystemsUpToNewVars` compares.
//   3. Run a verbatim port of HS `sortednubBy` (`sortednub_by`) over the
//      index-decorated list, comparing on the canonical key, then
//      `sortOn fst` to restore original-index order (matches `sortOn fst`
//      in HS).  NOTE: `sortednubBy` does NOT keep the first element of an
//      EQ-group — its run-detection phase (`sequences`) does
//      `EQ -> sequences xs`, dropping the earlier element and keeping the
//      LATER one; the `merge` phase drops the right-list element on EQ.
//      Since every EQ-group member has an identical key and `sortOn fst`
//      washes out cross-group order, the observable effect is "keep the
//      highest-original-index member of each equal-key group".  (The
//      previous `BTreeSet` first-wins dedup was unfaithful — it flipped
//      the surviving representative on symmetric AC peers, e.g. Joux/Scott
//      `Session_Key_Secrecy_PFS`'s B↔C mirror.)

/// Walk the free LVars of `sys.nodes` in HS `foldFreesOcc` order
/// (`HS instance HasFrees System`: only field `a` is walked; commented
/// out for `b..m`).  Produces a list of `(LVar, BTreeSet<Vec<String>>)`
/// where the inner set is the set of occurrence-context strings each
/// var appears in.  Mirrors `varOccurences`
/// (`lib/term/src/Term/LTerm.hs:593`).
///
/// HS context format (per HasFrees-instance tree under `foldFreesOcc`):
///   - Map (NodeId, RuleACInst):  context = same `p` for both k and v
///     (`foldFreesOcc f p = M.foldrWithKey combine` calling
///     `foldFreesOcc f p (k, v)`).
///   - Tuple `(k, v)`:  k gets "0":p, v gets "1":p.
///   - Rule i ps cs as _nvs:  the three fact lists run under
///     `((show i):c)` as a (ps, cs, as) triple — each gets
///     "0"/"1"/"2":((show i):c).
///   - [a] (Vec):  each element runs under (show i):c.
///   - Fact:  `f for_each_free` runs each term arg; we walk arg list
///     positionally as well.
///   - Term: a Var leaf returns the LVar with the current context.
///
/// We emit `(v, ctx)` pairs and bucket by var. The outer `_sNodes` map
/// walks its (k,v) entries in BTreeMap key order — i.e. NodeId Ord. RS's
/// `sys.nodes` is `Vec<(NodeId, RuleACInst)>`; we sort by NodeId before
/// walking to match HS.
fn var_occurrences_nodes(
    sys: &crate::constraint::system::System,
) -> Vec<(tamarin_term::lterm::LVar, std::collections::BTreeSet<Vec<String>>)> {
    use tamarin_term::lterm::LVar;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use std::collections::BTreeMap;
    use std::collections::BTreeSet;
    // ctx is HS's [String] occurrence path; head is innermost.
    // We push for each tree-descend, then mutate-and-pop is impractical;
    // we just clone (HS uses persistent list = sharing tail).
    // HS `foldFreesOcc` context string for a function symbol head
    // (Term.hs `instance HasFrees (Term l)`, LTerm.hs:745-748):
    //   FApp (NoEq o) as  ->  push `BC.unpack . fst $ o`  (the bare op name)
    //   FApp o        as  ->  push `show o`               (the FunSym, for AC/C/List)
    // The SAME context is pushed once for the whole arg list — HS does NOT
    // descend per-argument with an index, so every argument of an `FApp`
    // shares the symbol-name context.  (Previously RS pushed the arg INDEX
    // and no symbol name, which produced occurrence-sets incompatible with
    // HS's `varOccurences`, breaking the canonical `renameDropNameHints`
    // ordering and so under-collapsing alpha-equivalent cases in
    // `removeRedundantCases`.)
    fn funsym_occ_ctx(sym: &tamarin_term::function_symbols::FunSym) -> String {
        use tamarin_term::function_symbols::{FunSym, AcSym, CSym};
        match sym {
            FunSym::NoEq(s) => String::from_utf8_lossy(&s.name).into_owned(),
            FunSym::Ac(ac) => match ac {
                AcSym::Union => "AC Union".to_string(),
                AcSym::Mult => "AC Mult".to_string(),
                AcSym::Xor => "AC Xor".to_string(),
                AcSym::NatPlus => "AC NatPlus".to_string(),
            },
            FunSym::C(c) => match c {
                CSym::EMap => "C EMap".to_string(),
            },
            FunSym::List => "List".to_string(),
        }
    }
    // HS `show (factTag fa)` (derived `Show FactTag`, Fact.hs:132-143).
    //   ProtoFact mult name arity -> "ProtoFact <mult> \"<name>\" <arity>"
    //   FreshFact/OutFact/InFact/KUFact/KDFact/DedFact/TermFact (nullary)
    fn fact_tag_occ_ctx(f: &crate::fact::LNFact) -> String {
        use crate::fact::{FactTag, Multiplicity};
        match &f.tag {
            FactTag::Proto(m, name, arity) => {
                let mstr = match m {
                    Multiplicity::Persistent => "Persistent",
                    Multiplicity::Linear => "Linear",
                };
                format!("ProtoFact {} {:?} {}", mstr, name, arity)
            }
            FactTag::Fresh => "FreshFact".to_string(),
            FactTag::Out => "OutFact".to_string(),
            FactTag::In => "InFact".to_string(),
            FactTag::Ku => "KUFact".to_string(),
            FactTag::Kd => "KDFact".to_string(),
            FactTag::Ded => "DedFact".to_string(),
            FactTag::Term => "TermFact".to_string(),
        }
    }
    fn visit_term(
        t: &tamarin_term::lterm::LNTerm,
        ctx: &[String],
        out: &mut BTreeMap<LVar, BTreeSet<Vec<String>>>,
    ) {
        match t {
            Term::Lit(Lit::Var(v)) => {
                out.entry(v.clone()).or_default().insert(ctx.to_vec());
            }
            Term::Lit(Lit::Con(_)) => {}
            Term::App(sym, args) => {
                // HS `instance HasFrees (Term l)` `foldFreesOcc`
                // (LTerm.hs:744-748):
                //   FApp (NoEq o) as -> foldFreesOcc f ((opName):c) as
                //   FApp o        as -> mconcat $ map (foldFreesOcc f (show o:c)) as
                //                       -- AC or C symbols
                // For a NoEq function the args are descended as a LIST, so the
                // `HasFrees [a]` instance (LTerm.hs:843) prefixes EACH arg with
                // its positional index `show i`: arg i's context becomes
                // `[show i, opName, ...c]`.  For AC/C symbols HS maps over the
                // args DIRECTLY (no list instance), so they get only
                // `[show o, ...c]` with NO per-arg index (AC args are unordered
                // anyway).  RS previously omitted the NoEq per-arg index, which
                // made structurally-distinct vars at different argument
                // positions (e.g. alethea's H1 vs H2 `encp`/`sg` operands)
                // collapse to the SAME occurrence-context set; that under-
                // discrimination broke the canonical `renameDropNameHints`
                // ordering so `removeRedundantCases` kept alpha-equivalent
                // split cases as distinct (`split_case_1` instead of `split`).
                let mut sub = vec![funsym_occ_ctx(sym)];
                sub.extend(ctx.iter().cloned());
                let is_ac_or_c = sym.is_ac() || sym.is_c();
                for (i, a) in args.iter().enumerate() {
                    if is_ac_or_c {
                        // AC/C: no per-arg index (HS maps directly).
                        visit_term(a, &sub, out);
                    } else {
                        // NoEq: prefix the arg index (HS list instance).
                        let mut arg_ctx = vec![i.to_string()];
                        arg_ctx.extend(sub.iter().cloned());
                        visit_term(a, &arg_ctx, out);
                    }
                }
            }
        }
    }
    // HS `instance HasFrees Fact` (Fact.hs:187):
    //   foldFreesOcc f c fa = foldFreesOcc f (show (factTag fa):c) (factTerms fa)
    // i.e. push `show (factTag fa)` then descend into the term LIST, which
    // (via the `[a]` instance) pushes the list index `show i` per term.  So
    // term i's context = [show i, show factTag, ...c].  RS previously pushed
    // only the term index and omitted the factTag layer.
    fn visit_fact(
        f: &crate::fact::LNFact,
        ctx: &[String],
        out: &mut BTreeMap<LVar, BTreeSet<Vec<String>>>,
    ) {
        let mut tag_ctx = vec![fact_tag_occ_ctx(f)];
        tag_ctx.extend(ctx.iter().cloned());
        for (i, t) in f.terms.iter().enumerate() {
            let mut sub = vec![i.to_string()];
            sub.extend(tag_ctx.iter().cloned());
            visit_term(t, &sub, out);
        }
    }
    fn visit_facts(
        fs: &[crate::fact::LNFact],
        ctx: &[String],
        out: &mut BTreeMap<LVar, BTreeSet<Vec<String>>>,
    ) {
        for (i, f) in fs.iter().enumerate() {
            let mut sub = vec![i.to_string()];
            sub.extend(ctx.iter().cloned());
            visit_fact(f, &sub, out);
        }
    }
    // foldFreesOcc Rule:
    //   foldFreesOcc f c (Rule i ps cs as _) =
    //     foldFreesOcc f ((show i):c) (ps, cs, as)
    // tuple (ps, cs, as) walks: ps → "0":c, cs → "1":c, as → "2":c.
    fn visit_rule(
        r: &crate::rule::RuleACInst,
        ctx: &[String],
        out: &mut BTreeMap<LVar, BTreeSet<Vec<String>>>,
    ) {
        let mut rule_ctx = vec![format!("{:?}", r.info)];
        rule_ctx.extend(ctx.iter().cloned());
        // ps
        let mut ps_ctx = vec!["0".to_string()];
        ps_ctx.extend(rule_ctx.iter().cloned());
        visit_facts(&r.premises, &ps_ctx, out);
        // cs
        let mut cs_ctx = vec!["1".to_string()];
        cs_ctx.extend(rule_ctx.iter().cloned());
        visit_facts(&r.conclusions, &cs_ctx, out);
        // as
        let mut as_ctx = vec!["2".to_string()];
        as_ctx.extend(rule_ctx.iter().cloned());
        visit_facts(&r.actions, &as_ctx, out);
    }
    // M.Map's foldFreesOcc passes the same `p` to each (k, v) tuple, then
    // the tuple instance splits "0":p and "1":p.  We walk in BTreeMap-key
    // order (Ord LVar on NodeId) — HS's M.foldrWithKey iterates ASC.
    let mut nodes_sorted: Vec<&(tamarin_term::lterm::LVar, crate::rule::RuleACInst)> =
        sys.nodes.iter().collect();
    nodes_sorted.sort_by(|a, b| a.0.cmp(&b.0));
    let base_ctx: Vec<String> = Vec::new();
    let mut out: BTreeMap<LVar, BTreeSet<Vec<String>>> = BTreeMap::new();
    for (nid, rule) in &nodes_sorted {
        // For (k, v) tuple: "0":p for k (NodeId is just an LVar), "1":p for v.
        let mut k_ctx = vec!["0".to_string()];
        k_ctx.extend(base_ctx.iter().cloned());
        out.entry((*nid).clone()).or_default().insert(k_ctx);
        let mut v_ctx = vec!["1".to_string()];
        v_ctx.extend(base_ctx.iter().cloned());
        visit_rule(rule, &v_ctx, &mut out);
    }
    out.into_iter().collect()
}

/// Walk a Goal collecting free LVars in DFS order.
fn goal_walk_frees(g: &crate::constraint::constraints::Goal, push: &mut dyn FnMut(&tamarin_term::lterm::LVar)) {
    use crate::constraint::constraints::Goal;
    use tamarin_term::lterm::HasFrees;
    match g {
        Goal::Action(i, fa) => { push(i); fa.for_each_free(push); }
        Goal::Premise(p, fa) => { push(&p.0); fa.for_each_free(push); }
        Goal::Chain(c, p) => { push(&c.0); push(&p.0); }
        Goal::Subterm((a, b)) => { a.for_each_free(push); b.for_each_free(push); }
        // Disj/Split: bound vars excluded for renaming purposes; for our
        // canonical-key purpose, we walk free vars in Disj alternatives.
        Goal::Disj(d) => {
            for alt in &d.0 {
                guarded_walk_frees(alt, push);
            }
        }
        Goal::Split(_) => {}
    }
}

/// Walk a Guarded collecting free LVars in DFS order.  Free LVars
/// correspond to BVar::Free leaves; we reconstruct an LVar by combining
/// VarSpec name/idx with a best-effort sort.  HS's `Guarded` lives over
/// LVar directly, so its free vars carry full LSort.  RS's `Guarded`
/// uses VarSpec which has a SortHint; we map it back to LSort.
fn guarded_walk_frees(g: &crate::guarded::Guarded, push: &mut dyn FnMut(&tamarin_term::lterm::LVar)) {
    let mut frees: Vec<tamarin_parser::ast::VarSpec> = Vec::new();
    fn collect(g: &crate::guarded::Guarded, out: &mut Vec<tamarin_parser::ast::VarSpec>) {
        use crate::guarded::Guarded;
        match g {
            Guarded::Atom(a) => crate::guarded_types::collect_free_atom(a, out),
            Guarded::Disj(items) | Guarded::Conj(items) =>
                for it in items { collect(it, out); },
            Guarded::GGuarded { guards, body, .. } => {
                for a in guards { crate::guarded_types::collect_free_atom(a, out); }
                collect(body, out);
            }
        }
    }
    collect(g, &mut frees);
    for vs in &frees {
        let sort = varspec_sort_to_lsort(&vs.sort);
        push(&tamarin_term::lterm::LVar { name: tamarin_term::intern::intern_str(vs.name.as_str()), sort, idx: vs.idx });
    }
}

fn varspec_sort_to_lsort(s: &tamarin_parser::ast::SortHint) -> tamarin_term::lterm::LSort {
    use tamarin_parser::ast::{SortHint, SuffixSort};
    use tamarin_term::lterm::LSort;
    match s {
        SortHint::Msg => LSort::Msg,
        SortHint::Pub => LSort::Pub,
        SortHint::Fresh => LSort::Fresh,
        SortHint::Node => LSort::Node,
        SortHint::Nat => LSort::Nat,
        SortHint::Suffix(SuffixSort::Msg) => LSort::Msg,
        SortHint::Suffix(SuffixSort::Pub) => LSort::Pub,
        SortHint::Suffix(SuffixSort::Fresh) => LSort::Fresh,
        SortHint::Suffix(SuffixSort::Node) => LSort::Node,
        SortHint::Suffix(SuffixSort::Nat) => LSort::Nat,
        SortHint::Untagged => LSort::Msg,
    }
}

/// HS `foldFrees`-order walk of every free LVar in a System.  The HS
/// `instance HasFrees System` walks a..m in order (System.hs:1834-1848);
/// we replicate field-by-field.  Each callback fires for every
/// occurrence (including duplicates), so the binding-map registration
/// is deterministic over DFS order.
fn system_walk_frees(
    sys: &crate::constraint::system::System,
    push: &mut dyn FnMut(&tamarin_term::lterm::LVar),
) {
    use tamarin_term::lterm::HasFrees;
    // a: sNodes (Map NodeId RuleACInst) — BTreeMap-key order.
    let mut nodes_sorted: Vec<&(tamarin_term::lterm::LVar, crate::rule::RuleACInst)> =
        sys.nodes.iter().collect();
    nodes_sorted.sort_by(|a, b| a.0.cmp(&b.0));
    for (nid, rule) in &nodes_sorted {
        push(nid);
        rule.for_each_free(push);
    }
    // b: sEdges (Set Edge) — set Ord order.
    let mut edges_sorted: Vec<&crate::constraint::constraints::Edge> = sys.edges.iter().collect();
    edges_sorted.sort();
    for e in &edges_sorted {
        push(&e.src.0);
        push(&e.tgt.0);
    }
    // c: sLessAtoms (Set LessAtom) — set Ord order.
    let mut less_sorted: Vec<&crate::constraint::constraints::LessAtom> =
        sys.less_atoms.iter().collect();
    less_sorted.sort();
    for la in &less_sorted {
        push(&la.smaller);
        push(&la.larger);
    }
    // d: sLastAtom (Maybe NodeId).
    if let Some(la) = &sys.last_atom { push(la); }
    // e: sSubtermStore.
    for st in &sys.subterm_store.subterms {
        st.small.for_each_free(push);
        st.big.for_each_free(push);
    }
    for st in &sys.subterm_store.solved_subterms {
        st.small.for_each_free(push);
        st.big.for_each_free(push);
    }
    // f: sEqStore (subst + conj + nextSplitId).
    for (v, t) in sys.eq_store.subst.to_list() {
        push(&v);
        t.for_each_free(push);
    }
    for disj in &sys.eq_store.conj {
        for sub in &disj.substs {
            // VFresh: range vars are FRESH (don't enter the binding map);
            // only the DOMAIN vars participate as free.  This mirrors
            // HS's HasFrees instance for SubstVFresh which treats range
            // vars as bound.
            for (v, _) in sub.to_list() {
                push(&v);
            }
        }
    }
    // g: sFormulas (Set LNGuarded) — HS `Set` walks in ascending
    // `Ord LNGuarded`.  Use `cmp_guarded` (the codebase's HS-Ord
    // comparator, as in `freshen_system_some_inst`) rather than a
    // `Debug`-string sort: the derived-Debug rendering does NOT match
    // HS Ord (e.g. `LVar` renders name-before-idx, while HS `Ord LVar`
    // is idx-first), which would make the fresh-idx assignment order —
    // and thus the dedup key — diverge from Haskell.
    let mut formulas_sorted: Vec<&crate::guarded::Guarded> = sys.formulas.iter().collect();
    formulas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for f in &formulas_sorted {
        guarded_walk_frees(f, push);
    }
    // h: sSolvedFormulas.
    let mut solved_sorted: Vec<&crate::guarded::Guarded> =
        sys.solved_formulas.iter().collect();
    solved_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for f in &solved_sorted {
        guarded_walk_frees(f, push);
    }
    // i: sLemmas.
    let mut lemmas_sorted: Vec<&crate::guarded::Guarded> = sys.lemmas.iter().collect();
    lemmas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for f in &lemmas_sorted {
        guarded_walk_frees(f, push);
    }
    // j: sGoals (Map Goal GoalStatus) — HS `Map` walks ascending
    // `Ord Goal`.  Use `goal_cmp` (HS-Ord, as in
    // `freshen_system_some_inst`) rather than a `Debug`-string sort,
    // which sorts goal variants alphabetically and vars name-first —
    // both diverging from HS Ord.
    let mut goals_sorted: Vec<&(crate::constraint::constraints::Goal,
                                crate::constraint::system::GoalStatus)>
        = sys.goals.iter().collect();
    goals_sorted.sort_by(|a, b| {
        crate::constraint::solver::goals::goal_cmp(&a.0, &b.0)
    });
    for (g, _st) in &goals_sorted {
        goal_walk_frees(g, push);
    }
    // k, l, m: no LVars.
}

/// Compute the HS-faithful rename map for `renameDropNameHints sys`
/// (HS Sources.hs:345-348):
///   1. Start binding = { v ↦ v | v ∈ stableVars }
///   2. Fresh state = avoid stableVars (i.e. next idx > max stable idx)
///   3. Walk orderedVars sys = filter (/= Node) . map fst . sortOn snd
///      . varOccurences $ sys.  For each var not in binding, assign it a
///      fresh LVar with name="", same sort, incrementing fresh idx.
///   4. Walk sys.foldFrees (every field a..m).  Same import-binding
///      logic: skip if bound, else assign fresh.
///
/// Returns the binding map.  Stable vars map to themselves (unchanged).
fn compute_rename_map(
    sys: &crate::constraint::system::System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) -> std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar> {
    use tamarin_term::lterm::{LSort, LVar};
    use std::collections::BTreeMap;
    let mut rename: BTreeMap<LVar, LVar> = BTreeMap::new();
    // Step 1: stable vars bind to themselves.
    for v in stable_vars { rename.insert(v.clone(), v.clone()); }
    // Step 2: fresh state = avoid stableVars.
    let mut fresh_state = tamarin_utils::fresh::FastFreshState::nothing_used();
    if let Some(max) = stable_vars.iter().map(|v| v.idx).max() {
        fresh_state.fresh_idents(max + 1);
    }
    // Import helper.  HS's `importBinding (`LVar` lvarSort x) x ""`:
    //   - mkR n i = LVar i (lvarSort x) n   -- argument order is
    //     `LVar :: String -> LSort -> Integer -> LVar`, so `(`LVar` sort)`
    //     partially applies sort → result is `\name idx -> LVar name sort idx`.
    //   - Pre-bound vars stay; new vars get a fresh idx + empty name.
    let import = |v: &LVar,
                  rename: &mut BTreeMap<LVar, LVar>,
                  fresh: &mut tamarin_utils::fresh::FastFreshState| {
        if rename.contains_key(v) { return; }
        let new_idx = fresh.fresh_ident();
        let new_v = LVar { name: "".into(), sort: v.sort, idx: new_idx };
        rename.insert(v.clone(), new_v);
    };
    // Step 3: orderedVars sys — varOccurences from nodes ONLY,
    // sorted by occurrence set, filtered to non-Node sort.
    let mut occs = var_occurrences_nodes(sys);
    occs.sort_by(|a, b| a.1.cmp(&b.1));
    for (v, _occs) in &occs {
        if v.sort == LSort::Node { continue; }
        import(v, &mut rename, &mut fresh_state);
    }
    // Step 4: system_walk_frees walks the entire System in HS foldFrees
    // order, registering any var not yet bound.
    system_walk_frees(sys, &mut |v: &LVar| {
        import(v, &mut rename, &mut fresh_state);
    });
    rename
}

/// Apply rename to an LVar; if missing, return as-is (Node-sort vars
/// without an occurrence in `_sNodes` may not appear in the map).
fn rn(
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    v: &tamarin_term::lterm::LVar,
) -> tamarin_term::lterm::LVar {
    rename.get(v).cloned().unwrap_or_else(|| v.clone())
}

/// Write a term to the key buffer with renamed vars.
///
/// For AC and C function symbols, child renderings are sorted alphabetically
/// post-rename so that the key is invariant under permutation of AC args
/// (HS's `renameDropNameHints` calls `fAppAC` which re-canonicalizes the
/// term under the renamed-var Ord; our pre-rendered Vec retains the
/// pre-rename order, so we sort the rendered children here to match).
/// Without this, two systems that differ ONLY by which renamed var ends
/// up in which AC slot (e.g. `Union(v4, v5)` vs `Union(v5, v4)` after
/// renaming `B↔C` to `v4↔v5`) get distinct keys and survive
/// `removeRedundantCases`.
fn write_term_to_key(
    t: &tamarin_term::lterm::LNTerm,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use std::fmt::Write as _;
    match t {
        Term::Lit(Lit::Var(v)) => {
            let rv = rn(rename, v);
            let _ = write!(out, "v{}:{:?}", rv.idx, rv.sort);
        }
        Term::Lit(Lit::Con(c)) => { let _ = write!(out, "{:?}", c); }
        Term::App(sym, args) => {
            let _ = write!(out, "{:?}(", sym);
            // For AC/C symbols, sort child renderings (post-rename) to
            // make the key permutation-invariant.
            if sym.is_ac() || sym.is_c() {
                let mut rendered: Vec<String> = args.iter()
                    .map(|a| {
                        let mut s = String::new();
                        write_term_to_key(a, rename, &mut s);
                        s
                    })
                    .collect();
                rendered.sort();
                for (i, s) in rendered.iter().enumerate() {
                    if i > 0 { out.push(','); }
                    out.push_str(s);
                }
            } else {
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { out.push(','); }
                    write_term_to_key(a, rename, out);
                }
            }
            out.push(')');
        }
    }
}

fn write_fact_to_key(
    f: &crate::fact::LNFact,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use std::fmt::Write as _;
    let _ = write!(out, "{:?}:{:?}[", f.tag, f.annotations);
    for (i, t) in f.terms.iter().enumerate() {
        if i > 0 { out.push(','); }
        write_term_to_key(t, rename, out);
    }
    out.push(']');
}

fn write_rule_to_key_excl_new_vars(
    r: &crate::rule::RuleACInst,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use std::fmt::Write as _;
    let _ = write!(out, "info={:?};", r.info);
    out.push_str("ps:[");
    for (i, p) in r.premises.iter().enumerate() {
        if i > 0 { out.push(','); }
        write_fact_to_key(p, rename, out);
    }
    out.push_str("];cs:[");
    for (i, c) in r.conclusions.iter().enumerate() {
        if i > 0 { out.push(','); }
        write_fact_to_key(c, rename, out);
    }
    out.push_str("];as:[");
    for (i, a) in r.actions.iter().enumerate() {
        if i > 0 { out.push(','); }
        write_fact_to_key(a, rename, out);
    }
    out.push(']');
    // Crucial: rule.new_vars EXCLUDED per `compareRulesUpToNewVars`.
}

/// Render a `Guarded` formula into the redundant-case dedup key buffer,
/// applying the free-var alpha-`rename` INLINE.
///
/// PERF/FAITHFULNESS: this is a direct structural serializer.  The previous
/// implementation cloned the whole formula via `subst_guarded` (to apply
/// the rename) and then `format!("{:?}", _)`-ed it through the derived
/// `Debug` machinery — that path was ~19% of UM3 self+children time
/// (GTerm clone churn + the slow generic `Debug` formatter builders +
/// an intermediate `String` allocation per formula).  We instead walk the
/// formula once, renaming free LVar leaves in place and writing a compact
/// structural fingerprint, with NO clone and NO `Debug` dispatch.
///
/// The produced key BYTES differ from the old `Debug` rendering, but the
/// induced equivalence partition is IDENTICAL: `compute_compare_systems_key`
/// keys are purely internal (never reach `--prove` output), and they are
/// only ever compared for equality/ordering against other keys from the
/// SAME `removeRedundantCases` call.  The `rename` map is a var→var alpha
/// renaming (`compute_rename_map`), so substituting it never produces a
/// `Pair` and `mk_gpair`'s tuple-flattening (the one non-rename effect of
/// `subst_guarded`) can never fire here — i.e. the old `subst_guarded`
/// step did *nothing but rename free vars* for this input class.  This
/// serializer renames the same free vars and is injective over the formula
/// structure, so two formulas collide here iff they collided before.
fn write_guarded_to_key(
    g: &crate::guarded::Guarded,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    write_guarded_struct(g, rename, out);
}

/// Look up the renamed identity of a `Free` GTerm var and write it.
fn write_gfree_var(
    v: &tamarin_parser::ast::VarSpec,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use std::fmt::Write as _;
    let sort = varspec_sort_to_lsort(&v.sort);
    let lv = tamarin_term::lterm::LVar { name: tamarin_term::intern::intern_str(v.name.as_str()), sort, idx: v.idx };
    let rv = rename.get(&lv).unwrap_or(&lv);
    // Encode the renamed identity (name + idx + sort) — matches what the
    // old subst_guarded+Debug path encoded for a Free leaf.
    let _ = write!(out, "F{}#{}:{:?}", rv.name, rv.idx, rv.sort);
}

fn write_gterm_struct(
    t: &crate::guarded_types::GTerm,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use crate::guarded_types::{BVar, GTerm};
    use std::fmt::Write as _;
    match t {
        GTerm::Var(BVar::Free(v)) => write_gfree_var(v, rename, out),
        GTerm::Var(BVar::Bound(n)) => { let _ = write!(out, "B{}", n); }
        GTerm::PubLit(s) => { let _ = write!(out, "p'{}'", s); }
        GTerm::FreshLit(s) => { let _ = write!(out, "f'{}'", s); }
        GTerm::NatLit(s) => { let _ = write!(out, "n'{}'", s); }
        GTerm::Number(x) => { let _ = write!(out, "#{}", x); }
        GTerm::NumberOne => out.push_str("#1"),
        GTerm::NatOne => out.push_str("%1"),
        GTerm::DhNeutral => out.push_str("dhN"),
        GTerm::App(name, args) => {
            let _ = write!(out, "{}(", name);
            for (i, a) in args.iter().enumerate() {
                if i > 0 { out.push(','); }
                write_gterm_struct(a, rename, out);
            }
            out.push(')');
        }
        GTerm::AlgApp(name, a, b) => {
            let _ = write!(out, "{}^(", name);
            write_gterm_struct(a, rename, out);
            out.push(',');
            write_gterm_struct(b, rename, out);
            out.push(')');
        }
        GTerm::Pair(items) => {
            out.push('<');
            for (i, a) in items.iter().enumerate() {
                if i > 0 { out.push(','); }
                write_gterm_struct(a, rename, out);
            }
            out.push('>');
        }
        GTerm::Diff(a, b) => {
            out.push_str("diff(");
            write_gterm_struct(a, rename, out);
            out.push(',');
            write_gterm_struct(b, rename, out);
            out.push(')');
        }
        GTerm::BinOp(op, a, b) => {
            let _ = write!(out, "{:?}(", op);
            write_gterm_struct(a, rename, out);
            out.push(',');
            write_gterm_struct(b, rename, out);
            out.push(')');
        }
        GTerm::PatMatch(t) => {
            out.push_str("=(");
            write_gterm_struct(t, rename, out);
            out.push(')');
        }
    }
}

fn write_gfact_struct(
    f: &crate::guarded_types::GFact,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use std::fmt::Write as _;
    let _ = write!(out, "{}{}:{:?}[", if f.persistent { "!" } else { "" }, f.name, f.annotations);
    for (i, t) in f.args.iter().enumerate() {
        if i > 0 { out.push(','); }
        write_gterm_struct(t, rename, out);
    }
    out.push(']');
}

fn write_gatom_struct(
    a: &crate::guarded_types::GAtom,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use crate::guarded_types::GAtom;
    let bin = |tag: &str, x: &crate::guarded_types::GTerm, y: &crate::guarded_types::GTerm,
               out: &mut String| {
        out.push_str(tag);
        out.push('(');
        write_gterm_struct(x, rename, out);
        out.push(',');
        write_gterm_struct(y, rename, out);
        out.push(')');
    };
    match a {
        GAtom::Eq(x, y) => bin("EQ", x, y, out),
        GAtom::Less(x, y) => bin("LT", x, y, out),
        GAtom::LessMset(x, y) => bin("LTm", x, y, out),
        GAtom::Subterm(x, y) => bin("SUB", x, y, out),
        GAtom::Action(f, t) => {
            out.push_str("ACT(");
            write_gfact_struct(f, rename, out);
            out.push('@');
            write_gterm_struct(t, rename, out);
            out.push(')');
        }
        GAtom::Last(t) => {
            out.push_str("LAST(");
            write_gterm_struct(t, rename, out);
            out.push(')');
        }
        GAtom::Pred(f) => {
            out.push_str("PRED(");
            write_gfact_struct(f, rename, out);
            out.push(')');
        }
    }
}

fn write_guarded_struct(
    g: &crate::guarded::Guarded,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use crate::guarded::Guarded;
    use std::fmt::Write as _;
    match g {
        Guarded::Atom(a) => {
            out.push_str("A{");
            write_gatom_struct(a, rename, out);
            out.push('}');
        }
        Guarded::Disj(items) => {
            out.push_str("OR[");
            for (i, it) in items.iter().enumerate() {
                if i > 0 { out.push(';'); }
                write_guarded_struct(it, rename, out);
            }
            out.push(']');
        }
        Guarded::Conj(items) => {
            out.push_str("AND[");
            for (i, it) in items.iter().enumerate() {
                if i > 0 { out.push(';'); }
                write_guarded_struct(it, rename, out);
            }
            out.push(']');
        }
        Guarded::GGuarded { qua, vars, guards, body } => {
            let _ = write!(out, "G{:?}(", qua);
            for (i, b) in vars.iter().enumerate() {
                if i > 0 { out.push(','); }
                let _ = write!(out, "{}:{:?}", b.name, b.sort);
            }
            out.push_str("){");
            for (i, a) in guards.iter().enumerate() {
                if i > 0 { out.push(';'); }
                write_gatom_struct(a, rename, out);
            }
            out.push_str("}=>");
            write_guarded_struct(body, rename, out);
        }
    }
}

/// Build the canonical key used to identify a system up to alpha-renaming
/// of non-stable vars and modulo rule.new_vars.  Two systems with the
/// same key are considered redundant per HS's `compareSystemsUpToNewVars`
/// + `renameDropNameHints` + `dropNameHintsBound`.
fn compute_compare_systems_key(
    sys: &crate::constraint::system::System,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) -> String {
    use std::fmt::Write as _;
    let rename = compute_rename_map(sys, stable_vars);
    let mut out = String::new();
    // NODES (with renamed ids, excluding rule.new_vars).
    out.push_str("NODES:[");
    let mut nodes_sorted: Vec<&(tamarin_term::lterm::LVar, crate::rule::RuleACInst)> =
        sys.nodes.iter().collect();
    nodes_sorted.sort_by_key(|a| rn(&rename, &a.0));
    for (nid, rule) in &nodes_sorted {
        let rid = rn(&rename, nid);
        let _ = write!(out, "{{id={}:{:?};", rid.idx, rid.sort);
        write_rule_to_key_excl_new_vars(rule, &rename, &mut out);
        out.push_str("};");
    }
    out.push(']');
    // EDGES.
    out.push_str(";EDGES:[");
    let mut edges_renamed: Vec<(tamarin_term::lterm::LVar, crate::rule::ConcIdx,
                                tamarin_term::lterm::LVar, crate::rule::PremIdx)>
        = sys.edges.iter()
            .map(|e| (rn(&rename, &e.src.0), e.src.1, rn(&rename, &e.tgt.0), e.tgt.1))
            .collect();
    edges_renamed.sort();
    for (s, si, t, ti) in &edges_renamed {
        let _ = write!(out, "{}:{:?}.{:?}->{}:{:?}.{:?};",
            s.idx, s.sort, si, t.idx, t.sort, ti);
    }
    out.push(']');
    // LESS.
    out.push_str(";LESS:[");
    let mut less_renamed: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LVar,
                               crate::constraint::constraints::Reason)> = sys.less_atoms.iter()
        .map(|la| (rn(&rename, &la.smaller), rn(&rename, &la.larger), la.reason))
        .collect();
    less_renamed.sort_by(|a, b| (&a.0, &a.1).cmp(&(&b.0, &b.1)));
    for (s, t, _r) in &less_renamed {
        let _ = write!(out, "{}<{};", s.idx, t.idx);
    }
    out.push(']');
    // LAST.
    out.push_str(";LAST:");
    if let Some(j) = &sys.last_atom {
        let r = rn(&rename, j);
        let _ = write!(out, "{}", r.idx);
    }
    // SUBTERM STORE.
    out.push_str(";STORE:[");
    for st in &sys.subterm_store.subterms {
        write_term_to_key(&st.small, &rename, &mut out);
        out.push_str("<<");
        write_term_to_key(&st.big, &rename, &mut out);
        out.push(';');
    }
    out.push_str("]/SOLVED:[");
    for st in &sys.subterm_store.solved_subterms {
        write_term_to_key(&st.small, &rename, &mut out);
        out.push_str("<<");
        write_term_to_key(&st.big, &rename, &mut out);
        out.push(';');
    }
    out.push(']');
    // EQSTORE.subst (free subst).
    out.push_str(";SUBST:[");
    let mut subst_pairs: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> =
        sys.eq_store.subst.to_list();
    // Re-key by renamed var, then sort.
    let mut subst_keyed: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)> =
        subst_pairs.drain(..).map(|(v, t)| (rn(&rename, &v), t)).collect();
    subst_keyed.sort_by(|a, b| a.0.cmp(&b.0));
    for (v, t) in &subst_keyed {
        let _ = write!(out, "{}:{:?}=", v.idx, v.sort);
        write_term_to_key(t, &rename, &mut out);
        out.push(',');
    }
    out.push(']');
    // EQSTORE.conj — domain vars renamed; range is VFresh so name-hints
    // are dropped (we serialise range structurally with empty names).
    out.push_str(";CONJ:[");
    for disj in &sys.eq_store.conj {
        let _ = write!(out, "id={:?};", disj.split_id);
        let mut sub_strs: Vec<String> = Vec::new();
        for sub in &disj.substs {
            let mut s = String::new();
            let mut entries: Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)>
                = sub.to_list().into_iter()
                .map(|(v, t)| (rn(&rename, &v), t))
                .collect();
            entries.sort_by(|a, b| a.0.cmp(&b.0));
            for (v, t) in &entries {
                let _ = write!(s, "{}:{:?}=", v.idx, v.sort);
                // For VFresh range vars: strip name hints by writing
                // "v{idx}" using a local counter — equivalent to HS's
                // `renameDropNamehint` over the range terms.
                // Build a per-substitution local rename: range vars in
                // DFS order → empty-name + fresh local idx.
                let mut local_ren: std::collections::BTreeMap<
                    tamarin_term::lterm::LVar, tamarin_term::lterm::LVar> = Default::default();
                let mut local_next: u64 = 0;
                let local_import = |v: &tamarin_term::lterm::LVar,
                                    m: &mut std::collections::BTreeMap<
                                        tamarin_term::lterm::LVar,
                                        tamarin_term::lterm::LVar>,
                                    n: &mut u64| {
                    if !m.contains_key(v) {
                        m.insert(v.clone(), tamarin_term::lterm::LVar {
                            name: "".into(), sort: v.sort, idx: *n,
                        });
                        *n += 1;
                    }
                };
                use tamarin_term::lterm::HasFrees;
                t.for_each_free(&mut |v| local_import(v, &mut local_ren, &mut local_next));
                write_term_to_key_local(t, &local_ren, &mut s);
                s.push(',');
            }
            sub_strs.push(s);
        }
        sub_strs.sort();
        for s in &sub_strs { out.push_str(s); out.push('|'); }
        out.push(';');
    }
    out.push(']');
    // FORMULAS.
    out.push_str(";FORMS:[");
    let mut forms_renamed: Vec<String> = sys.formulas.iter().map(|g| {
        let mut s = String::new();
        write_guarded_to_key(g, &rename, &mut s);
        s
    }).collect();
    forms_renamed.sort();
    for s in &forms_renamed { out.push_str(s); out.push(';'); }
    out.push(']');
    // SOLVED FORMULAS.
    out.push_str(";SOLV_FORMS:[");
    let mut solved_renamed: Vec<String> = sys.solved_formulas.iter().map(|g| {
        let mut s = String::new();
        write_guarded_to_key(g, &rename, &mut s);
        s
    }).collect();
    solved_renamed.sort();
    for s in &solved_renamed { out.push_str(s); out.push(';'); }
    out.push(']');
    // LEMMAS.
    out.push_str(";LEMMAS:[");
    let mut lemmas_renamed: Vec<String> = sys.lemmas.iter().map(|g| {
        let mut s = String::new();
        write_guarded_to_key(g, &rename, &mut s);
        s
    }).collect();
    lemmas_renamed.sort();
    for s in &lemmas_renamed { out.push_str(s); out.push(';'); }
    out.push(']');
    // GOALS (deterministic order, renamed-var keyed).
    // HS structural Ord on System includes `_sGoals :: Map Goal
    // GoalStatus` — both the Goal key AND the GoalStatus value
    // participate.  GoalStatus = (gsSolved, gsNr, gsLoopBreaker)
    // per System.hs:370-380.  RS previously stripped GoalStatus,
    // making cases with the same goals but different goal-status
    // (e.g. different gsNr from differing creation order) compare
    // equal — under-discriminating per HS.  Include status fields.
    out.push_str(";GOALS:[");
    let mut goal_strs: Vec<String> = sys.goals.iter().map(|(g, st)| {
        let mut s = String::new();
        write_goal_to_key(g, &rename, &mut s);
        let _ = write!(s, ":st={},{},{}", st.solved, st.nr, st.looping);
        s
    }).collect();
    goal_strs.sort();
    for s in &goal_strs { out.push_str(s); out.push(';'); }
    out.push(']');
    // HS also includes `_sNextGoalNr :: Integer` in the structural Ord
    // (System.hs:394).  Include for faithfulness.
    let _ = write!(out, ";NEXT_NR={}", sys.next_goal_nr);
    // SOURCE KIND / DIFF — affect compareSystemsUpToNewVars only via
    // structural fallthrough when m != False.
    let _ = write!(out, ";SK={:?};SIDE={:?}", sys.source_kind, sys.side);
    out
}

/// Serialise a Goal with renamed vars.
fn write_goal_to_key(
    g: &crate::constraint::constraints::Goal,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use crate::constraint::constraints::Goal;
    use std::fmt::Write as _;
    match g {
        Goal::Action(i, fa) => {
            let ri = rn(rename, i);
            let _ = write!(out, "A({}:{:?},", ri.idx, ri.sort);
            write_fact_to_key(fa, rename, out);
            out.push(')');
        }
        Goal::Premise(p, fa) => {
            let ri = rn(rename, &p.0);
            let _ = write!(out, "P({}:{:?}.{:?},", ri.idx, ri.sort, p.1);
            write_fact_to_key(fa, rename, out);
            out.push(')');
        }
        Goal::Chain(c, p) => {
            let rc = rn(rename, &c.0);
            let rp = rn(rename, &p.0);
            let _ = write!(out, "C({}:{:?}.{:?}->{}:{:?}.{:?})",
                rc.idx, rc.sort, c.1, rp.idx, rp.sort, p.1);
        }
        Goal::Subterm((a, b)) => {
            out.push_str("S(");
            write_term_to_key(a, rename, out);
            out.push_str("<<");
            write_term_to_key(b, rename, out);
            out.push(')');
        }
        Goal::Split(id) => {
            let _ = write!(out, "Sp({:?})", id);
        }
        Goal::Disj(d) => {
            out.push_str("D[");
            let mut alt_strs: Vec<String> = d.0.iter().map(|alt| {
                let mut s = String::new();
                write_guarded_to_key(alt, rename, &mut s);
                s
            }).collect();
            alt_strs.sort();
            for s in &alt_strs { out.push_str(s); out.push('|'); }
            out.push(']');
        }
    }
}

/// Local variant of `write_term_to_key` that uses a local rename map
/// for VFresh range vars (no fallback to identity).
fn write_term_to_key_local(
    t: &tamarin_term::lterm::LNTerm,
    rename: &std::collections::BTreeMap<tamarin_term::lterm::LVar, tamarin_term::lterm::LVar>,
    out: &mut String,
) {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use std::fmt::Write as _;
    match t {
        Term::Lit(Lit::Var(v)) => {
            let rv = rename.get(v).cloned().unwrap_or_else(|| v.clone());
            let _ = write!(out, "v{}:{:?}", rv.idx, rv.sort);
        }
        Term::Lit(Lit::Con(c)) => { let _ = write!(out, "{:?}", c); }
        Term::App(sym, args) => {
            let _ = write!(out, "{:?}(", sym);
            // For AC/C symbols, sort child renderings (post-rename) to
            // make the key permutation-invariant.  See `write_term_to_key`
            // for the rationale.
            if sym.is_ac() || sym.is_c() {
                let mut rendered: Vec<String> = args.iter()
                    .map(|a| {
                        let mut s = String::new();
                        write_term_to_key_local(a, rename, &mut s);
                        s
                    })
                    .collect();
                rendered.sort();
                for (i, s) in rendered.iter().enumerate() {
                    if i > 0 { out.push(','); }
                    out.push_str(s);
                }
            } else {
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { out.push(','); }
                    write_term_to_key_local(a, rename, out);
                }
            }
            out.push(')');
        }
    }
}

/// Direct port of Haskell `removeRedundantCases` (Sources.hs:236-260).
/// Direct port of HS `sortednubBy` (`lib/utils/src/Extension/Prelude.hs:52`,
/// GHC's `Data.List.sortBy` adapted to drop duplicates).  Sorts by `cmp`
/// AND removes elements for which an earlier-in-the-merge element compares
/// `EQ`.  The survivor of an `EQ`-group is NOT simply the first input
/// element: the run-detection phase (`sequences`) does `EQ -> sequences xs`
/// which drops the *earlier* element and keeps the *later* one, while the
/// `merge` phase drops the right-list element on `EQ`.  We replicate the
/// algorithm verbatim so survivor selection matches HS exactly.
fn sortednub_by<T, C>(cmp: &C, xs: Vec<T>) -> Vec<T>
where
    C: Fn(&T, &T) -> std::cmp::Ordering,
{
    use std::cmp::Ordering::*;
    // sequences: build maximal ascending/descending runs, dropping EQ.
    fn sequences<T, C>(cmp: &C, mut xs: Vec<T>) -> Vec<Vec<T>>
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        // Iteratively consume `xs`; mirrors the recursive HS `sequences`.
        let mut runs: Vec<Vec<T>> = Vec::new();
        loop {
            if xs.len() < 2 {
                runs.push(xs);
                return runs;
            }
            // pop first two (a, b) preserving the rest order.
            let mut it = xs.into_iter();
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            let rest: Vec<T> = it.collect();
            match cmp(&a, &b) {
                Greater => {
                    // descending b [a] rest'
                    let (run, remaining) = descending(cmp, b, vec![a], rest);
                    runs.push(run);
                    xs = remaining;
                }
                Equal => {
                    // a `cmp` b == EQ -> sequences xs (drop a, keep from b)
                    let mut next = Vec::with_capacity(rest.len() + 1);
                    next.push(b);
                    next.extend(rest);
                    xs = next;
                }
                Less => {
                    // ascending b (a:) rest
                    let (run, remaining) = ascending(cmp, b, vec![a], rest);
                    runs.push(run);
                    xs = remaining;
                }
            }
        }
    }

    // descending a as (b:bs) | a `cmp` b == GT = descending b (a:as) bs
    // descending a as bs = (a:as) : sequences bs   -- (a:as) already reversed -> ascending
    fn descending<T, C>(cmp: &C, mut a: T, mut acc: Vec<T>, mut bs: Vec<T>) -> (Vec<T>, Vec<T>)
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        loop {
            if let Some(b_ref) = bs.first() {
                if cmp(&a, b_ref) == Greater {
                    let mut it = bs.into_iter();
                    let b = it.next().unwrap();
                    bs = it.collect();
                    acc.insert(0, a); // a:as  (acc holds run in ascending order)
                    a = b;
                    continue;
                }
            }
            // (a:as) : run is acc with a prepended; acc already ascending, so result ascending
            acc.insert(0, a);
            return (acc, bs);
        }
    }

    // ascending a as (b:bs) | a `cmp` b == LT = ascending b (\ys -> as (a:ys)) bs
    // ascending a as bs = as [a] : sequences bs
    fn ascending<T, C>(cmp: &C, mut a: T, mut acc: Vec<T>, mut bs: Vec<T>) -> (Vec<T>, Vec<T>)
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        loop {
            if let Some(b_ref) = bs.first() {
                if cmp(&a, b_ref) == Less {
                    let mut it = bs.into_iter();
                    let b = it.next().unwrap();
                    bs = it.collect();
                    acc.push(a); // as ++ [a]
                    a = b;
                    continue;
                }
            }
            acc.push(a); // as [a]
            return (acc, bs);
        }
    }

    // merge two sorted-deduped runs, dropping EQ (right element).
    fn merge<T, C>(cmp: &C, a: Vec<T>, b: Vec<T>) -> Vec<T>
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        let cap = a.len() + b.len();
        let mut out: Vec<T> = Vec::with_capacity(cap);
        let mut ai = a.into_iter().peekable();
        let mut bi = b.into_iter().peekable();
        loop {
            match (ai.peek(), bi.peek()) {
                (Some(av), Some(bv)) => match cmp(av, bv) {
                    Greater => out.push(bi.next().unwrap()),
                    Equal => {
                        // drop the right-list element (b), keep left
                        bi.next();
                    }
                    Less => out.push(ai.next().unwrap()),
                },
                (Some(_), None) => {
                    out.extend(ai);
                    return out;
                }
                (None, _) => {
                    out.extend(bi);
                    return out;
                }
            }
        }
    }

    fn merge_pairs<T, C>(cmp: &C, xs: Vec<Vec<T>>) -> Vec<Vec<T>>
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        let mut out: Vec<Vec<T>> = Vec::with_capacity(xs.len().div_ceil(2));
        let mut it = xs.into_iter();
        loop {
            match (it.next(), it.next()) {
                (Some(a), Some(b)) => out.push(merge(cmp, a, b)),
                (Some(a), None) => {
                    out.push(a);
                    return out;
                }
                (None, _) => return out,
            }
        }
    }

    fn merge_all<T, C>(cmp: &C, mut xs: Vec<Vec<T>>) -> Vec<T>
    where
        C: Fn(&T, &T) -> std::cmp::Ordering,
    {
        if xs.is_empty() {
            return Vec::new();
        }
        while xs.len() > 1 {
            xs = merge_pairs(cmp, xs);
        }
        xs.into_iter().next().unwrap()
    }

    merge_all(cmp, sequences(cmp, xs))
}

/// Gated on BP/MSet per HS short-circuit.  Faithful port of HS
/// `removeRedundantCases` (`Sources.hs:236-260`, body at 242-244): decorate each case with
/// its original index, run `sortednubBy compareSystemsUpToNewVars` over the
/// decorated list, then `sortOn fst` to restore original-index order.  The
/// survivor of an alpha-equivalent group is the one `sortednubBy` keeps —
/// which is the LAST element of an `EQ`-run, NOT the first (the previous
/// implementation's `BTreeSet` first-wins was WRONG; cf. Joux/Scott
/// `Session_Key_Secrecy_PFS` B↔C mirror).  We port `sortednubBy` verbatim
/// rather than approximate it: for the common case (an `EQ`-group of pure
/// alpha-duplicates with identical keys) this keeps the LAST member and,
/// after `sortOn fst`, emits survivors in original-index order — the exact
/// flip the Joux/Scott mirror needed.  (The string key encodes what
/// `compareSystemsUpToNewVars` distinguishes, so two cases compare `EQ`
/// here iff they are alpha-equivalent there.)
pub fn remove_redundant_cases<T, F>(
    enable_bp: bool,
    enable_mset: bool,
    stable_vars: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
    get_sys: F,
    cases: Vec<T>,
) -> Vec<T>
where
    F: Fn(&T) -> &crate::constraint::system::System,
{
    if !(enable_bp || enable_mset) { return cases; }
    let dbg = tamarin_utils::env_gate!("TAM_RS_DBG_REMOVE_REDUNDANT");
    let dump = tamarin_utils::env_gate!("TAM_RS_DBG_RRC_DUMP");
    let pre = cases.len();
    // Decorate with (original index, canonical key).  HS:
    //   decoratedCases = map (second addNormSys) $ zip [0..] cases0
    // where addNormSys produces the renamed/normed system; we precompute
    // the string key (which encodes exactly what compareSystemsUpToNewVars
    // distinguishes) instead of carrying the normed System.
    let mut decorated: Vec<(usize, String, T)> = Vec::with_capacity(pre);
    for (idx, c) in cases.into_iter().enumerate() {
        let key = compute_compare_systems_key(get_sys(&c), stable_vars);
        if dbg {
            eprintln!("[RRC] key_len={} stable_vars={} nodes={}",
                key.len(), stable_vars.len(), get_sys(&c).nodes.len());
        }
        if dump && pre > 1 {
            eprintln!("[RRC_DUMP] idx={} key={}", idx, key);
        }
        decorated.push((idx, key, c));
    }
    // sortednubBy (\(_,x) (_,y) -> compare x y)  -- compare on the key only,
    // matching HS comparing on the normed system via compareSystemsUpToNewVars.
    let deduped = sortednub_by(&|a: &(usize, String, T), b: &(usize, String, T)| {
        a.1.cmp(&b.1)
    }, decorated);
    // sortOn fst : restore original-index order.
    let mut deduped = deduped;
    deduped.sort_by_key(|a| a.0);
    let out: Vec<T> = deduped.into_iter().map(|(_, _, c)| c).collect();
    if dbg && out.len() != pre {
        eprintln!("[RRC] dedup {} → {}", pre, out.len());
    }
    out
}

// `saturate_fanout_variant_splits` (a saturate-time variant SplitG
// fan-out) was removed: Haskell's `someRuleACInst` leaves the
// `RuleACConstrs` SplitG OPEN at saturate time (SplitG is not a "safe"
// goal while chains are open — `doSplit = noChainGoals && not (null
// chains)`, Sources.hs:152-164), and variant narrowing happens at
// runtime as a deeper `case split` step rather than as sibling source
// cases.  A prior commit (a64042c4) fanned variants out here, producing
// `Resolve1_case_N`/`S_2_case_N`/`B_1_case_N` siblings Haskell never
// emits; the helper was reduced to a permanent no-op and is now deleted,
// with its `None`-branch inlined at the (chain-fold) call site.

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

    /// Was: assert `precompute_full_sources` populates `cases` eagerly
    /// at `ProofContext::new` time.  Now: `precompute_full_sources` is
    /// HS-faithful lazy — Sources are pushed with uncomputed
    /// `cases_cell`, materialised on first `cases(ctx)` call.  The
    /// per-tag-entry presence assertion still holds (the Source for
    /// tag A is in `ctx.full_sources`); the eager-case assertion does
    /// not.  Update or split this test when re-enabling saturate.
    #[test]
    #[ignore = "expects eager cases; see lazy-precompute refactor"]
    fn precompute_full_sources_emits_per_tag_entries() {
        use crate::fact::{Fact, FactTag, Multiplicity, fresh_fact};
        use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
        use tamarin_term::builtin::msg_var;

        let path = match maude_path() { Some(p) => p, None => return };
        let h = tamarin_term::maude_proc::MaudeHandle::start(
            &path, tamarin_term::maude_sig::pair_maude_sig()).unwrap();

        let a_tag = FactTag::Proto(Multiplicity::Linear, "A".into(), 1);
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
        assert!(!a_src.cases_or_empty().is_empty(),
            "source for A should have at least one case (Init / Loop)");
    }

    /// Bilinear-pairing source: when `enableBP` is set, HS Sources.hs
    /// emits a `KU(em(t.1, t.2))` source.  Without this, BP-theory
    /// targets (Chen_Kudla, Joux, RYY, Scott, TAK1) miss the em
    /// source-case enumeration entirely.  Pre-fix RS only iterated
    /// `msig.fun_syms` for NoEq symbols and skipped C(EMap) silently.
    #[test]
    fn precompute_full_sources_emits_em_when_bp_enabled() {
        use crate::constraint::constraints::Goal;
        use crate::fact::{Fact, FactTag, Multiplicity, fresh_fact};
        use crate::rule::{ProtoRuleE, ProtoRuleEInfo, Rule};
        use tamarin_term::builtin::msg_var;

        let path = match maude_path() { Some(p) => p, None => return };
        let h = tamarin_term::maude_proc::MaudeHandle::start(
            &path, tamarin_term::maude_sig::bp_maude_sig()).unwrap();

        // Minimal protocol so there's at least one proto rule (so
        // `precompute_full_sources` actually runs).
        let a_tag = FactTag::Proto(Multiplicity::Linear, "A".into(), 1);
        let a_fact = Fact::new(a_tag.clone(), vec![msg_var("x", 0)]);
        let init: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Init"),
            vec![fresh_fact(msg_var("x", 0))],
            vec![a_fact.clone()],
            vec![],
        );
        let rules = vec![crate::theory::OpenProtoRule::new(init)];
        let ctx = crate::constraint::solver::context::ProofContext::new(h, rules);
        // Find the KU(em(...)) source.
        let em_src = ctx.full_sources.iter().find(|s| match &s.goal {
            Goal::Action(_, fa) => {
                if fa.tag != FactTag::Ku || fa.terms.len() != 1 { return false; }
                matches!(&fa.terms[0], tamarin_term::term::Term::App(
                    tamarin_term::function_symbols::FunSym::C(
                        tamarin_term::function_symbols::CSym::EMap), _))
            },
            _ => false,
        });
        assert!(em_src.is_some(),
            "expected a KU(em(...)) source for BP-enabled theory; got: {:?}",
            ctx.full_sources.iter().map(|s| &s.goal).collect::<Vec<_>>());
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
        sys.invalidate_max_var_idx_cache();
        sys.eq_store_mut().subst = Subst::from_list(vec![
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
        sys.invalidate_max_var_idx_cache();
        sys.eq_store_mut().subst = Subst::from_list(vec![
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
        sys.invalidate_max_var_idx_cache();
        sys.eq_store_mut().subst = Subst::from_list(vec![
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
    // HS-faithful source-case naming invariant.
    //
    // By the time a case name reaches the runtime, `refineSource` has
    // already applied HS's `combine` (Sources.hs:135-139, ported in
    // `combine_case_names_list`) over the `[String]` step-name list, and
    // the result is joined with `intercalate "_"` (ProofMethod.hs:511).
    // The stored name is therefore the FINAL display name and must be
    // used verbatim — HS never re-splits a single name on `_`.
    // =========================================================================

    /// `combine` keeps a single non-coerce element verbatim, including when it
    /// is a `c_<sym>` construction-rule name whose symbol contains underscores
    /// (e.g. `c_KDF_SKc` must stay intact, never split to `SKc` — the
    /// fm24-cardpayments C8 divergence).
    #[test]
    fn combine_keeps_underscore_bearing_constr_name_intact() {
        // Single construction-rule name → kept whole.
        assert_eq!(
            combine_case_names_list(&["c_KDF_SKc".to_string()], &[]),
            vec!["c_KDF_SKc".to_string()]);
        // Leading "coerce" element dropped, next element kept whole.
        assert_eq!(
            combine_case_names_list(
                &["coerce".to_string(), "c_KDF_SKc".to_string()], &[]),
            vec!["c_KDF_SKc".to_string()]);
        // Underscore-free constructors are likewise kept verbatim.
        assert_eq!(
            combine_case_names_list(&["c_senc".to_string()], &[]),
            vec!["c_senc".to_string()]);
        // Protocol-rule names with underscores kept whole.
        assert_eq!(
            combine_case_names_list(&["Card_Responds_To_GPO_C8".to_string()], &[]),
            vec!["Card_Responds_To_GPO_C8".to_string()]);
    }

    /// `case_name_list_to_string` is HS `intercalate "_"`.
    #[test]
    fn case_name_list_to_string_is_intercalate_underscore() {
        assert_eq!(case_name_list_to_string(&["c_KDF_SKc".to_string()]), "c_KDF_SKc");
        assert_eq!(case_name_list_to_string(
            &["a".to_string(), "b".to_string()]), "a_b");
        assert_eq!(case_name_list_to_string(&[]), "");
    }
}
