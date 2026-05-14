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
}

impl Source {
    pub fn new(goal: crate::constraint::constraints::Goal) -> Self {
        Source { goal, cases: Vec::new() }
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

        let sys = System::empty();
        let mut red = Reduction::new(ctx, sys);
        red.insert_goal(goal.clone());
        let outcome = red.solve_premise_goal(
            &(goal_node.clone(), PremIdx(0)),
            &abstract_fact);
        // Propagate eq-store substitution into nodes/edges/goals for
        // each case before saving — without this, the case stores its
        // rules' original vars (e.g., `x_1`) while the abstract terms
        // (`t_1`) live only in the eq-store.  Saturation needs the
        // unified form so its substitution can rewrite the rule vars
        // to match the outer case's premise term.
        let normalize = |sys: System| -> System {
            let mut r = Reduction::new(ctx, sys);
            r.subst_system();
            r.sys
        };
        let cases = match outcome {
            GoalCases::Linear => vec![("only".into(), normalize(red.sys))],
            GoalCases::LinearNamed(name) => vec![(name, normalize(red.sys))],
            GoalCases::Cases(systems) => systems.into_iter()
                .map(|(name, s)| (name, normalize(s)))
                .collect(),
            GoalCases::Contradictory => Vec::new(),
        };
        if cases.is_empty() { continue; }
        out.push(Source { goal, cases });
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
            if noeq.arity == 0 { continue; }
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
        let sys = System::empty();
        let mut red = Reduction::new(ctx, sys);
        red.insert_goal(goal.clone());
        let outcome = red.solve_action_goal(&goal_node, &ku_fact);
        let normalize = |sys: System| -> System {
            let mut r = Reduction::new(ctx, sys);
            r.subst_system();
            r.sys
        };
        let cases = match outcome {
            GoalCases::Linear => vec![("only".into(), normalize(red.sys))],
            GoalCases::LinearNamed(name) => vec![(name, normalize(red.sys))],
            GoalCases::Cases(systems) => systems.into_iter()
                .map(|(name, s)| (name, normalize(s)))
                .collect(),
            GoalCases::Contradictory => Vec::new(),
        };
        if cases.is_empty() { continue; }
        out.push(Source { goal, cases });
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
                        if let Some(grafted) = saturate_out_premise(
                            ctx, sys, &p, &fa, name)
                        {
                            for (sub_name, sub_sys) in grafted {
                                new_cases.push((sub_name, sub_sys));
                                new_used.push(case_used.clone());
                                changed = true;
                            }
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
                                        let canonical = tamarin_term::lterm::LVar {
                                            name: lv.name.clone(),
                                            sort: s,
                                            idx: lv.idx,
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
                            let live_sys = apply_lvar_subst(sys, &term_subst);
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
            next.push(Source { goal: src.goal.clone(), cases: new_cases });
            next_used.push(new_used);
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
    // Drop cases that leave open `Chain` goals — the KD branch of
    // `solve_premise_goal` introduces a Chain that should be closed
    // by `solve_chain_goal`, but if we hand the runtime a case with
    // an unresolved Chain it sometimes contradicts spuriously
    // (likely the Chain endpoint's unification interacts with
    // the rest of the system in ways we don't model at precompute).
    // Keeping only Chain-free cases is conservative but avoids the
    // verdict regressions we hit when grafting partial chains.
    let chain_free = |s: &System| -> bool {
        !s.goals.iter().any(|(g, st)|
            !st.solved && matches!(g, Goal::Chain(_, _)))
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
    // DFS chain-closure backtracking (Haskell's `disjunctionOfList`).
    fn close_chains_dfs(
        ctx: &crate::constraint::solver::context::ProofContext,
        s: System,
        budget: usize,
    ) -> Option<System> {
        // Check FIRST whether there's any chain left to close.  If
        // not, the system is already chain-free and we return success
        // regardless of remaining budget.  The budget exhaustion check
        // applies only when we'd need to extend further.
        let chain = s.goals.iter().find_map(|(g, st)| {
            if st.solved || st.looping { return None; }
            if let Goal::Chain(c, p) = g {
                Some((c.clone(), p.clone()))
            } else { None }
        });
        let Some((c, p)) = chain else { return Some(s); };
        if budget == 0 { return None; }
        let mut sub = Reduction::new(ctx, s);
        set_precompute_mode(false);
        let outcome = sub.solve_chain_goal(&c, &p);
        set_precompute_mode(true);
        match outcome {
            GoalCases::Contradictory => None,
            GoalCases::Linear | GoalCases::LinearNamed(_) =>
                close_chains_dfs(ctx, sub.sys, budget - 1),
            GoalCases::Cases(cases) => {
                for (_, c_sys) in cases {
                    if let Some(r) = close_chains_dfs(ctx, c_sys, budget - 1) {
                        return Some(r);
                    }
                }
                None
            }
        }
    }
    for (sub_name, sys) in raw {
        let close_result = close_chains_dfs(ctx, sys, 4);
        if std::env::var("TAM_DBG_SAT").is_ok() {
            eprintln!("[sat]   close_chains_dfs sub_name={:?} → success={}",
                sub_name, close_result.is_some());
        }
        let Some(s) = close_result else { continue };
        if chain_free(&s) {
            // Prefer `sub_name` (the recursive `solve_premise_goal`
            // case-name, which is the protocol rule's name for the
            // upstream Out producer) over `producer_name(&s)` (which
            // walks edges to the original premise and returns the
            // destructor rule's name after chain extension).  This
            // matches Haskell `refineSource`'s `combine` which strips
            // leading "coerce" and uses the FIRST non-coerce case-name
            // from the accumulated solver-name list (Sources.hs:135-137).
            // The first non-coerce name comes from the recursive
            // solvePremise on the IRecv's Out premise (e.g. "responder"),
            // not from the chain-closing destructor (e.g. "d_0_fst").
            let name = if !sub_name.is_empty() {
                format!("{}_{}", outer_name, sub_name)
            } else {
                let final_producer = producer_name(&s);
                format!("{}_{}", outer_name, final_producer)
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
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_term::lterm::LSort;
    match &src.goal {
        Goal::Action(_, fa) if fa.tag == FactTag::Ku && fa.terms.len() == 1 => {
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
        Goal::Premise(_, fa) => Some(format!("PR:{:?}", fa.tag)),
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
        let name = format!("{}_{}", outer_name, case_label);
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
    use crate::constraint::solver::contradictions::contradictions;
    use crate::constraint::solver::reduction::Reduction;
    use crate::constraint::solver::simplify::simplify_system;
    if assumptions.is_empty() { return sources; }

    // Step 1 (Haskell `updateSystem`): inject the [sources] lemma
    // assumptions into every case's formulas and re-simplify so the
    // implied universals fire and prune cases whose flow violates the
    // typing.  Cases that surface a contradiction are dropped.
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
            let mut red = Reduction::new(ctx, refined);
            simplify_system(&mut red);
            if !contradictions(ctx, &red.sys).is_empty() { continue; }
            new_cases.push((name, red.sys));
        }
        if !new_cases.is_empty() {
            intermediate.push(Source { goal: src.goal, cases: new_cases });
        }
    }

    // Step 2 (Haskell `saturateSources`): re-saturate with the
    // assumption-augmented cases.  This is the critical step our
    // earlier port skipped — it propagates the typing constraints
    // through the recursive premise expansion, pruning cases whose
    // continuation introduces premises that violate the [sources]
    // typing.
    let limit = 5usize;
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
            out.push(Source { goal: src.goal, cases: new_cases });
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
        // Snapshot the source list for filterCases — passed as `ths`
        // to `solve_all_safe_goals` so its `solveWithSource` branch
        // can look up matching cases for useful KU goals.
        let ths_snapshot = saturated.clone();
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
        for (i, src) in saturated.into_iter().enumerate() {
            let mut new_cases: Vec<(String, System)> = Vec::new();
            for (name, sys) in src.cases {
                let before_formulas = sys.formulas.len();
                let before_open = sys.goals.iter().filter(|(_, st)| !st.solved).count();
                let case_name_for_dbg = name.clone();
                let sys_orig = sys.clone();
                let mut red = Reduction::new(ctx, sys);
                set_precompute_mode(true);
                // Saturate-time filterCases (Haskell `solveAllSafeGoals`):
                // pass the current source list + a fresh used-set so
                // useful KU goals get closed via `solveWithSource`,
                // mirroring Haskell's full saturation.  Closing these
                // at precompute prevents the runtime re-spawn loop.
                let mut used: std::collections::BTreeSet<String> = Default::default();
                solve_all_safe_goals(
                    &mut red, &ths_snapshot, &mut used, /* chains_left */ 10);
                set_precompute_mode(false);
                let after_formulas = red.sys.formulas.len();
                let after_open = red.sys.goals.iter().filter(|(_, st)| !st.solved).count();
                let after_contras = contradictions(ctx, &red.sys);
                if dbg {
                    eprintln!("  case {:?}: formulas {}→{}, open goals {}→{}, contras={} ({:?})",
                        case_name_for_dbg, before_formulas, after_formulas,
                        before_open, after_open, after_contras.len(),
                        after_contras.iter().map(|c| format!("{:?}", c)).collect::<Vec<_>>());
                }
                if !after_contras.is_empty() {
                    // Distinguish "definitive" contradictions (the case
                    // is structurally impossible — keep dropping it)
                    // from "speculative" contradictions (saturation
                    // explored one branch of a Disj and that branch
                    // failed, but other branches may succeed —
                    // preserve the case in its PRE-SATURATE state and
                    // let runtime explore other branches).
                    //
                    // Haskell's `saturateSources` keeps a case when
                    // contradictions only arise from speculative
                    // disjunctive exploration; mirror that here by
                    // checking whether the pre-saturate state ALSO has
                    // the contradiction.  If only post-saturate has it,
                    // it's speculative — keep the pre-saturate.
                    use crate::constraint::solver::contradictions::Contradiction;
                    let only_eq_or_subterm = after_contras.iter().all(|c|
                        matches!(c, Contradiction::IncompatibleEqs
                                  | Contradiction::SubtermCyclic
                                  | Contradiction::NonNormalTerms));
                    let pre_contras = contradictions(ctx, &sys_orig);
                    let pre_has_contras = !pre_contras.is_empty();
                    if only_eq_or_subterm && !pre_has_contras {
                        // Speculative — keep pre-saturate state.
                        if dbg {
                            eprintln!("    → speculative contradiction, restoring pre-saturate state");
                        }
                        new_cases.push((name, sys_orig));
                        changed = true;
                        continue;
                    }
                    changed = true;
                    continue;
                }
                new_cases.push((name, red.sys));
            }
            if !new_cases.is_empty() {
                next.push(Source { goal: src.goal, cases: new_cases });
            }
            if next.last().map(|s| s.cases.len())
                != current.get(i).map(|s| s.cases.len())
            {
                changed = true;
            }
        }
        current = next;
        if !changed { break; }
    }
    current
}

/// Port of Haskell's `solveAllSafeGoals` (`Sources.hs:144-225`).
///
/// Iteratively simplifies the system, then picks one "safe" goal to
/// solve, repeating until no safe goal remains.  A goal is safe if:
///   - `Chain(_, _)` and chains_left > 0
///   - `Action(_, fa)` with `fa` NOT a KU fact
///   - `Premise(_, fa)` with `fa` NOT a KU/KD-Xor/NoSources fact
///   - `Disj` / `Split` / `Subterm` — only when split is allowed
///     (no open chain goals AND there ARE unsolved-chain constraints
///     in the system, per Haskell's `splitAllowed` flag)
///
/// KD-premise goals (and chain-prem-1 goals) take priority — they're
/// solved first, ahead of other safe goals.  When a goal-solve produces
/// multiple cases, we take the first case (best-effort saturation —
/// the case-fork would otherwise blow up the source-case count).
///
/// This is what propagates [sources]-typing assumptions transitively:
/// solving an open KD/Chain/Action goal grafts a producer rule,
/// adding facts and equations that interact with the typing-universal
/// formulas added by `refineWithSourceAsms` to detect contradictions.
fn solve_all_safe_goals(
    red: &mut crate::constraint::solver::reduction::Reduction,
    ths: &[Source],
    used: &mut std::collections::BTreeSet<String>,
    chains_limit: i64,
) {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::contradictions::contradictions;
    use crate::constraint::solver::goals::dispatch_solve_goal;
    use crate::constraint::solver::reduction::{GoalCases, SolveOutcome, SplitStrategy};
    use crate::constraint::solver::simplify::simplify_system;
    use crate::fact::FactTag;

    let mut chains_left = chains_limit;
    // Bound the outer loop to prevent runaway iteration (matches
    // Haskell's reliance on `openChainsLimit` plus the natural
    // monotonicity of goal-solving; we add a hard cap for safety).
    let outer_cap: i64 = 40;
    for _iter in 0..outer_cap {
        simplify_system(red);
        if !contradictions(&red.ctx, &red.sys).is_empty() {
            return;
        }
        // Snapshot open goals (skip solved + loop-breakers).
        let goals: Vec<(Goal, bool /* looping */)> = red.sys.goals.iter()
            .filter(|(_, st)| !st.solved && !st.looping)
            .map(|(g, st)| (g.clone(), st.looping))
            .collect();
        // Check if there are unsolved chain constraints (used for
        // splitAllowed flag — Disj/Split/Subterm goals only count
        // as "safe" when chains exist to keep the search bounded).
        let any_unsolved_chain = red.sys.goals.iter().any(|(g, st)|
            !st.solved && matches!(g, Goal::Chain(_, _)));
        let any_chain_goal = goals.iter().any(|(g, _)| matches!(g, Goal::Chain(_, _)));
        let split_allowed = !any_chain_goal && any_unsolved_chain;

        // Classify goals into kd_prem (priority) and safe.
        let is_kd_prem = |g: &Goal| -> bool {
            matches!(g, Goal::Premise(_, fa) if fa.tag == FactTag::Kd)
        };
        let is_chain_prem1 = |g: &Goal| -> bool {
            matches!(g, Goal::Chain(_, (_, pi)) if pi.0 == 1)
        };
        let is_safe = |g: &Goal| -> bool {
            match g {
                Goal::Chain(_, _) => chains_left > 0,
                Goal::Action(_, fa) => !matches!(fa.tag, FactTag::Ku),
                Goal::Premise(_, fa) => !matches!(fa.tag, FactTag::Ku | FactTag::Kd),
                Goal::Disj(_) | Goal::Split(_) | Goal::Subterm(_) => split_allowed,
            }
        };
        // Priority order: KD-premise / chain-prem1 first, then safe.
        let pick = goals.iter()
            .find(|(g, _)| is_kd_prem(g) || is_chain_prem1(g))
            .or_else(|| goals.iter().find(|(g, _)| is_safe(g)));

        if let Some((goal, _)) = pick {
            let goal = goal.clone();
            // Track chain budget: if we're solving a chain goal, decrement.
            if matches!(goal, Goal::Chain(_, _)) {
                chains_left -= 1;
            }
            // Solve the goal.  For multi-case outcomes, take the FIRST
            // case — saturation is one branch of the precompute, mirroring
            // Haskell's single-branch threading inside the Reduction monad.
            let outcome = dispatch_solve_goal(red, &goal);
            match outcome {
                GoalCases::Contradictory => return,
                GoalCases::Linear | GoalCases::LinearNamed(_) => {}
                GoalCases::Cases(cases) => {
                    if let Some((_, first)) = cases.into_iter().next() {
                        red.sys = first;
                    } else {
                        return;
                    }
                }
            }
            continue;
        }

        // No safe goal left — try the `solveWithSourceAndReturn`
        // branch of Haskell's `solveAllSafeGoals.solve`.  This is the
        // critical step our earlier port skipped: useful KU action
        // goals get resolved against the current source list, with
        // `used` tracking which cases have already been consumed in
        // this saturation branch (Haskell's `filterCases`).  Without
        // this, chain-saturated cases leave open KU goals that
        // recursively re-spawn the same source at runtime, looping.
        if ths.is_empty() { return; }
        let useful_ku = goals.iter().find_map(|(g, _)| match g {
            Goal::Action(i, fa) if matches!(fa.tag, FactTag::Ku) =>
                Some((i.clone(), fa.clone())),
            _ => None,
        });
        let Some((i, fa)) = useful_ku else { return };
        let avoid_max = system_max_idx(&red.sys);
        let Some(case_pairs) = solve_with_source_cases_action(
            ths, &red.sys, &i, &fa, avoid_max) else { return };
        // Pick the first case whose name has not been used in this
        // branch.  Mirrors `filterCases usedCase ths` followed by
        // `headMay` over the matching source's cases.
        let chosen = case_pairs.into_iter()
            .find(|(name, _, _)| !used.contains(name));
        let Some((case_name, sys, case_action)) = chosen else { return };
        red.sys = sys;
        let res = red.solve_fact_eqs(
            SplitStrategy::SplitNow,
            &[tamarin_term::rewriting::Equal {
                lhs: case_action, rhs: fa.clone(),
            }],
        );
        if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
            return;
        }
        // Edge-induced fact unification (same idiom as the runtime
        // graft sites in `reduction.rs`): propagate chain-internal
        // var bindings to live system vars by re-equating every
        // edge's source-conclusion and target-premise facts.
        // Tag/arity mismatches mean the case carries an edge with
        // incompatible facts — an invariant violation in the case
        // that should fail the graft, not be silently dropped.
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
        if tag_mismatch_edge { return; }
        if !chain_eqs.is_empty() {
            let r2 = red.solve_fact_eqs(SplitStrategy::SplitNow, &chain_eqs);
            if matches!(r2, Err(_) | Ok(SolveOutcome::Contradictory)) {
                return;
            }
        }
        red.subst_system();
        used.insert(case_name);
    }
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
        let grafted = match graft_case_into(
            sys, &renamed, &abstract_renamed, goal_node,
            goal_prem_idx, fa_prem,
        ) {
            Some(g) => g, None => continue,
        };
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
    for (g, st) in &case_sys.goals {
        if st.solved { continue; }
        let renamed_goal = match g {
            crate::constraint::constraints::Goal::Premise(p, fa)
                if &p.0 == abstract_node => continue,
            crate::constraint::constraints::Goal::Premise(p, fa) => {
                crate::constraint::constraints::Goal::Premise(
                    (rename_node(&p.0), p.1), fa.clone())
            }
            crate::constraint::constraints::Goal::Action(n, fa) =>
                crate::constraint::constraints::Goal::Action(rename_node(n), fa.clone()),
            other => other.clone(),
        };
        out.add_goal_with_loop_flag(renamed_goal, st.looping);
    }
    let live_goal = crate::constraint::constraints::Goal::Premise(
        (live_node.clone(), live_prem_idx), fa_prem.clone());
    if let Some(slot) = out.goals.iter_mut().find(|(g, _)| g == &live_goal) {
        slot.1.solved = true;
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

    let mut out: Vec<(String, System, crate::fact::LNFact)> = Vec::new();
    for (name, case_sys) in &src.cases {
        let case_label = saturated_chain_root(name);
        // Haskell-faithful `applySource` path when a ProofContext is
        // available.  Uses one-way Maude match + someInst
        // keepVarBindings + conjoinSystem setNodes-collision rule-eqs.
        // Falls back to the legacy freshen+graft path only when no
        // context is available (saturate-time callers).
        //
        // The legacy fallback remains for `saturate_out_premise` etc.
        // which compute source-cases at precompute time and don't
        // have a ProofContext handy.  Setting `TAM_LEGACY_APPLY_SOURCE=1`
        // forces the legacy path everywhere for diagnostics.
        let use_legacy = std::env::var("TAM_LEGACY_APPLY_SOURCE").is_ok();
        if let Some(ctx) = ctx_opt {
            if !use_legacy {
                // Find the case's specific action fact (the per-rule one
                // with its rule-specific vars).
                let action_fact = case_sys.nodes.iter().find_map(|(id, ru)| {
                    if id == &abstract_orig {
                        ru.actions.iter().find(|a| a.tag == FactTag::Ku).cloned()
                    } else { None }
                });
                let Some(action_fact) = action_fact else { continue };
                // Try matching with the case-specific action first; if it
                // fails (typically a sort mismatch — Fresh-sorted case
                // pattern var vs Msg-sorted live var), retry with the
                // source's ABSTRACT pattern (Msg-sorted t_i vars). The
                // case-specific match is preferred because it preserves
                // the specific bindings the case carries; the abstract
                // fallback covers the Haskell-faithful case where the
                // case's per-rule fresh vars need to narrow live vars.
                // Try case-specific matching first. If that fails AND the
                // source's abstract pattern is App-headed (e.g. KU(senc),
                // KU(h)), fall back to matching against the abstract
                // pattern. Mirrors Haskell's `matchToGoal` (Sources.hs:288)
                // which matches against `cdGoal` (the abstract Msg-sorted
                // t_i pattern). For App-headed patterns, the case-
                // specific terms carry per-rule Fresh-sorted fresh-vars
                // that strict matching can't unify with Msg-sorted live
                // protocol vars; the abstract Msg-sorted pattern matches
                // both. Skipped for bare-var KU sources (KU(t:Fresh))
                // where the case-specific terms already share live's
                // sort and the fallback would relax soundness.
                let result = apply_source_case_action(
                    ctx, sys, case_sys,
                    &abstract_orig, &action_fact,
                    goal_node, fa_live,
                ).or_else(|| {
                    let abstract_action_pat = match &src.goal {
                        Goal::Action(_, fa) => fa.clone(),
                        _ => return None,
                    };
                    let is_app_pattern = matches!(
                        abstract_action_pat.terms.first(),
                        Some(tamarin_term::term::Term::App(_, _))
                    );
                    if !is_app_pattern { return None; }
                    apply_source_case_action(
                        ctx, sys, case_sys,
                        &abstract_orig, &abstract_action_pat,
                        goal_node, fa_live,
                    )
                });
                if let Some((grafted_sys, live_action)) = result {
                    out.push((case_label, grafted_sys, live_action));
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
        let Some(grafted) = graft_case_into_action(
            sys, &renamed, &abstract_renamed, goal_node, fa_live,
        ) else { continue };
        out.push((case_label, grafted, action_fact));
    }
    if out.is_empty() { return None; }
    Some(out)
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
    tail.to_string()
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

/// Freshen all vars in `sys` EXCEPT those in `keep`. Mirrors Haskell's
/// `someInst sysTh0 keepVarBindings` (Sources.hs:348). Vars in `keep`
/// are preserved (they correspond to live-system vars introduced by
/// the match-subst); other vars get shifted by `avoid_max + 1` so they
/// don't collide with live-system vars.
fn freshen_system_keep(
    sys: &System,
    avoid_max: u64,
    keep: &std::collections::BTreeSet<tamarin_term::lterm::LVar>,
) -> System {
    use tamarin_term::lterm::HasFrees;
    let shift_lvar = |v: &tamarin_term::lterm::LVar| {
        if keep.contains(v) {
            v.clone()
        } else {
            let mut v2 = v.clone();
            v2.idx = v2.idx.saturating_add(avoid_max.saturating_add(1));
            v2
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
                other => other,
            };
            (g2, st)
        })
        .collect();
    if let Some(la) = out.last_atom.take() {
        out.last_atom = Some(shift_lvar(&la));
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
/// ```
///
/// Steps:
/// 1. Compute match-subst via one-way Maude match (pattern → subject).
///    Binds case pattern vars to live goal terms; live vars unchanged.
/// 2. Apply the match-subst to `case_sys` via Reduction + solve_term_eqs
///    + subst_system. Mirrors Haskell `refineSubst`.
/// 3. Freshen non-goal vars (`someInst keepVarBindings`): rename case
///    vars EXCEPT those in `keep_vars` (= free vars of live goal).
/// 4. Graft into live via `conjoinSystem`-equivalent: setNodes-style
///    rule-eq emission on node-id collisions, edges/less-atoms/goals
///    union, eq-store subst merged via solve_term_eqs (not direct
///    append).  All eqs are narrowed by Maude.
fn apply_source_case_action(
    ctx: &crate::constraint::solver::context::ProofContext,
    live_sys: &System,
    case_sys: &System,
    abstract_node: &crate::constraint::constraints::NodeId,
    abstract_action: &crate::fact::LNFact,
    live_node: &crate::constraint::constraints::NodeId,
    fa_live: &crate::fact::LNFact,
) -> Option<(System, crate::fact::LNFact)> {
    use crate::constraint::solver::reduction::{
        Reduction, SolveOutcome, SplitStrategy,
    };
    use tamarin_term::lterm::HasFrees;

    // -------------------------------------------------------------------
    // Step 0: Pre-rename ALL case vars by shifting their idx above
    // `bounds_max(live_sys)`.  Mirrors Haskell's `rename th0` in
    // `matchToGoal` (Sources.hs:307): before matching, the source is
    // freshened so its vars cannot collide with the live system's vars.
    // Without this, two unrelated semantic nodes can share a name (e.g.
    // both case and live have `vk#12` from precompute/runtime KU-goal
    // naming conventions); the subsequent match-subst + subst_system
    // then merges them and fails on incompatible rule fact terms.
    // -------------------------------------------------------------------
    let avoid_max = crate::constraint::solver::reduction::bounds_max(live_sys);
    let shift = |v: &tamarin_term::lterm::LVar| {
        let mut v2 = v.clone();
        v2.idx = v2.idx.saturating_add(avoid_max.saturating_add(1));
        v2
    };
    let empty_keep: std::collections::BTreeSet<tamarin_term::lterm::LVar>
        = std::collections::BTreeSet::new();
    let renamed_case = freshen_system_keep(case_sys, avoid_max, &empty_keep);
    let renamed_abstract_node = shift(abstract_node);
    let renamed_abstract_action = abstract_action.clone()
        .map_free(&mut |v| shift(&v));

    // -------------------------------------------------------------------
    // Step 1: One-way Maude match: pattern (renamed case's abstract
    // action terms) ↑ subject (live goal terms).  Returns substitution
    // binding pattern vars to live values; live vars are unbound.
    // -------------------------------------------------------------------
    if fa_live.tag != renamed_abstract_action.tag
        || fa_live.terms.len() != renamed_abstract_action.terms.len()
    {
        return None;
    }
    let match_pairs_attempt: Option<Vec<(tamarin_term::lterm::LVar, tamarin_term::lterm::LNTerm)>> = {
        let mut pairs: Vec<(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)>
            = Vec::new();
        for (lt, pt) in fa_live.terms.iter().zip(renamed_abstract_action.terms.iter()) {
            pairs.push((lt.clone(), pt.clone()));
        }
        if &renamed_abstract_node != live_node {
            pairs.push((
                tamarin_term::term::Term::Lit(
                    tamarin_term::vterm::Lit::Var(live_node.clone())),
                tamarin_term::term::Term::Lit(
                    tamarin_term::vterm::Lit::Var(renamed_abstract_node.clone())),
            ));
        }
        let problem = tamarin_term::rewriting::Match::DelayedMatches(pairs);
        tamarin_term::unification::solve_match_lterm_no_ac::<
            tamarin_term::lterm::Name, _>(
            &tamarin_term::lterm::sort_of_name, problem,
        ).map(|s| s.to_list())
    };
    let match_pairs = match match_pairs_attempt {
        Some(pairs) => pairs,
        None => {
            let match_eqs: Vec<_> = fa_live.terms.iter()
                .zip(renamed_abstract_action.terms.iter())
                .map(|(lt, pt)| tamarin_term::rewriting::Equal {
                    lhs: lt.clone(),
                    rhs: pt.clone(),
                })
                .collect();
            let substs = ctx.maude.match_eqs(&match_eqs).ok()?;
            if substs.is_empty() { return None; }
            let mut pairs = substs.into_iter().next().unwrap();
            if &renamed_abstract_node != live_node {
                pairs.push((
                    renamed_abstract_node.clone(),
                    tamarin_term::term::Term::Lit(
                        tamarin_term::vterm::Lit::Var(live_node.clone())),
                ));
            }
            pairs
        }
    };

    // -------------------------------------------------------------------
    // Step 2: Apply match-subst to the renamed case (refineSubst):
    // solve_term_eqs adds pattern→subject bindings to the case's
    // eq-store; subst_system propagates them to nodes/edges/formulas.
    // -------------------------------------------------------------------
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
            return None;
        }
    }
    refined.subst_system();
    if refined.sys.eq_store.is_false() {
        return None;
    }
    let refined_case = refined.sys;

    // -------------------------------------------------------------------
    // Step 3: someInst keepVarBindings. Haskell renames the case AGAIN
    // before conjoinSystem (`evalBindT (someInst sysTh0) keepVarBindings`),
    // freshening any Maude witness vars introduced by refineSubst.
    // -------------------------------------------------------------------
    let mut keep_vars: std::collections::BTreeSet<tamarin_term::lterm::LVar>
        = std::collections::BTreeSet::new();
    keep_vars.insert(live_node.clone());
    let mut collect_vars = |v: &tamarin_term::lterm::LVar| {
        keep_vars.insert(v.clone());
    };
    fa_live.for_each_free(&mut collect_vars);
    let avoid_max2 = crate::constraint::solver::reduction::bounds_max(live_sys);
    let freshened_case = freshen_system_keep(&refined_case, avoid_max2, &keep_vars);

    // The abstract_node in the case maps to live_node after step 2's
    // subst_system (since we added the node-id binding to match-subst).
    // But the case's syntactic representation might still reference
    // abstract_node if subst_system didn't propagate node-id renames
    // (subst rewrites VARS in LNTerm; NodeId is also LVar, but rewrite
    // path differs).  Use live_node directly as the renamed target.
    let live_action = freshened_case.nodes.iter()
        .find(|(id, _)| id == live_node)
        .and_then(|(_, r)| r.actions.iter()
            .find(|a| a.tag == crate::fact::FactTag::Ku).cloned())
        .or_else(|| {
            // Fallback: maybe the abstract_node was renamed by freshen
            // (because not in keep). Find by case_sys's matching action.
            freshened_case.nodes.iter()
                .find_map(|(_, r)| r.actions.iter()
                    .find(|a| a.tag == crate::fact::FactTag::Ku).cloned())
        });
    let live_action = match live_action {
        Some(a) => a,
        None => return None,
    };

    // -------------------------------------------------------------------
    // Step 4: conjoinSystem.  Use the Reduction primitive that mirrors
    // Haskell's `conjoinSystem` step-by-step (joinSets + insertLast +
    // insertLess + insertGoalStatus + insertFormula + setNodes +
    // addDisj + conjoinSubtermStores + solveSubstEqs + substSystem).
    // -------------------------------------------------------------------
    let mut r = Reduction::new(ctx, live_sys.clone());
    // Mark the live goal as solved BEFORE conjoinSystem (Haskell's
    // `markGoalAsSolved "precomputed" goal` runs before `conjoinSystem`).
    let live_goal = crate::constraint::constraints::Goal::Action(
        live_node.clone(), fa_live.clone());
    if let Some(slot) = r.sys.goals.iter_mut().find(|(g, _)| g == &live_goal) {
        slot.1.solved = true;
    }
    let res = r.conjoin_system(&freshened_case);
    if matches!(res, Err(_) | Ok(SolveOutcome::Contradictory)) {
        return None;
    }
    Some((r.sys, live_action))
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
    for (g, st) in &case_sys.goals {
        if st.solved { continue; }
        let renamed_goal = match g {
            crate::constraint::constraints::Goal::Action(n, fa)
                if n == abstract_node => continue,
            crate::constraint::constraints::Goal::Action(n, fa) =>
                crate::constraint::constraints::Goal::Action(rename_node(n), fa.clone()),
            crate::constraint::constraints::Goal::Premise(p, fa) =>
                crate::constraint::constraints::Goal::Premise(
                    (rename_node(&p.0), p.1), fa.clone()),
            other => other.clone(),
        };
        out.add_goal_with_loop_flag(renamed_goal, st.looping);
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

/// `removeRedundantCases` placeholder. The full version filters cases
/// that are subsumed by earlier ones modulo AC; the structural skeleton
/// here is a no-op.
pub fn remove_redundant_cases<T: Clone>(cases: Vec<T>) -> Vec<T> { cases }

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
}
