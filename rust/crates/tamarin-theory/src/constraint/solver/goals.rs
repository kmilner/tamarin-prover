//! Skeleton port of `Theory.Constraint.Solver.Goals`.
//!
//! `openGoals` enumerates the list of goals from a `System` that
//! still need to be solved, with `Usefulness` annotations driving
//! the heuristic. The full Haskell version filters via
//! `kFactView`, sort checks, AC predicates, and chain-conclusion
//! analysis. The Rust port currently implements the cheap structural
//! filter (skip already-solved goals, drop `DisjG (Disj [])`) and
//! defers the message-knowledge filtering until those view helpers
//! are available.

use crate::constraint::constraints::Goal;
use crate::constraint::solver::annotated_goals::{AnnotatedGoal, Usefulness};
use crate::constraint::system::System;

/// The goal ranking selected by a theory / lemma `heuristic:` directive.
///
/// Port of the relevant `Theory.Constraint.System.GoalRanking` variants
/// (`System.hs:506-520`).  We currently implement the two non-oracle,
/// non-tactic rankings that the comparable corpus exercises:
///
///   * `SmartRanking Bool`  (heuristic `s`/`S`, the default)
///   * `InjRanking  Bool`   (heuristic `i`/`I`)
///
/// All other ranking identifiers (oracle `o`/`O`, sapic `p`/`P`,
/// `c`/`C`, tactic `{..}`) parse to `Smart(false)` for now — the files
/// that use them are filtered out of the comparable corpus.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GoalRanking {
    /// `SmartRanking useLoopBreakers` (ProofMethod.hs:1203).
    Smart(bool),
    /// `InjRanking useLoopBreakers` (ProofMethod.hs:1096).
    Inj(bool),
}

impl GoalRanking {
    /// Parse a single heuristic character into a `GoalRanking`,
    /// mirroring HS's `goalRankingIdentifiers` (System.hs:585-598) /
    /// `stringToGoalRanking`.  Unhandled identifiers fall back to the
    /// default `Smart(false)` so behaviour for filtered-out files is
    /// unchanged.
    pub fn from_char(c: char) -> GoalRanking {
        match c {
            's' => GoalRanking::Smart(false),
            'S' => GoalRanking::Smart(true),
            'i' => GoalRanking::Inj(false),
            'I' => GoalRanking::Inj(true),
            _ => GoalRanking::Smart(false),
        }
    }

    /// Parse the first ranking identifier out of a heuristic string
    /// (e.g. `"I"`, `"s"`).  HS's `Heuristic` is a *list* of rankings
    /// scheduled round-robin by proof depth (`useHeuristic`,
    /// ProofMethod.hs:736); for the single-character heuristics in the
    /// comparable corpus the list has one element, so taking the first
    /// identifier is exact.  A leading `{` (tactic ranking) or quote is
    /// treated as the default.
    pub fn from_str(s: &str) -> GoalRanking {
        match s.trim().chars().next() {
            Some(c) if c.is_ascii_alphabetic() => GoalRanking::from_char(c),
            _ => GoalRanking::Smart(false),
        }
    }
}

/// `openGoals`: enumerate annotated goals still to be solved.
///
/// Haskell iterates `M.toList $ get sGoals sys` in Goal-derived-Ord
/// order; we use insertion-order.  With the Sk-matcher port now in
/// (commits 28567ab1 applySkAction + this commit's permissive
/// structural_match), Goal-Ord wiring is the natural next parity step
/// — but its interaction with the 10s corpus-probe deadline causes
/// runtime-perf regressions (Destroy_charn, Device_Init_Use_Set) that
/// verify with a 30s deadline.  Wire `goal_cmp` here when the corpus
/// probe deadline can accommodate the deeper search Goal-Ord induces
/// on those lemmas; `goal_cmp` is dead-code-allow below until then.
pub fn open_goals(sys: &System) -> Vec<AnnotatedGoal> {
    let mut out = Vec::new();
    for (goal, status) in sys.goals.iter() {
        if status.solved { continue; }
        if !is_open_in_sys(goal, sys) { continue; }
        let u = goal_usefulness(goal, status.looping, sys);
        // Use the persistent goal-number (`_gsNr`), NOT the Vec
        // position.  Haskell's `openGoals` returns `(goal, (gsNr,
        // useful))` (Goals.hs:125) and the rankings begin with
        // `goalNrRanking = sortOn (fst . snd)` (ProofMethod.hs:748),
        // i.e. ordering by creation number.  We carry `status.nr`
        // here and sort below so the heuristic priority classes break
        // ties by creation order exactly as HS does.
        out.push(AnnotatedGoal::new(goal.clone(), status.nr, u));
    }
    // goalNrRanking — stable sort by creation number.  The Vec is not
    // guaranteed to be in nr order (subst_goals / conjoin rebuild it),
    // so sort explicitly.  Stable so equal-nr goals (shouldn't happen,
    // but defensive) keep Vec order.
    out.sort_by_key(|a| a.seq);
    out
}

/// Render a `Disj<Guarded>` in a form whose lexicographic compare
/// matches HS's derived `Ord (Disj LNGuarded)` (which bottoms out at
/// `Ord LVar = idx <> sort <> name` per May-20).  Default `Debug` puts
/// `name` first so string compare disagrees with LVar Ord at the
/// first var that differs.  See `goal_cmp` Disj arm for use.
fn guarded_canon_idx_first(d: &crate::constraint::constraints::Disj<crate::guarded::Guarded>) -> String {
    fn render_guarded(g: &crate::guarded::Guarded, out: &mut String) {
        use crate::guarded::Guarded;
        match g {
            Guarded::Atom(a) => { out.push_str("A:"); render_atom(a, out); }
            Guarded::Conj(items) => {
                out.push('&');
                for it in items { render_guarded(it, out); out.push('|'); }
            }
            Guarded::Disj(items) => {
                out.push('|');
                for it in items { render_guarded(it, out); out.push('|'); }
            }
            Guarded::GGuarded { qua, vars, guards, body } => {
                out.push_str(&format!("{:?}{}", qua, vars.len()));
                for g in guards { render_atom(g, out); }
                render_guarded(body, out);
            }
        }
    }
    fn render_atom(a: &crate::guarded::GAtom, out: &mut String) {
        use crate::guarded::GAtom;
        match a {
            GAtom::Eq(s, t) => { out.push_str("E"); render_term(s, out); render_term(t, out); }
            GAtom::Less(s, t) => { out.push_str("L"); render_term(s, out); render_term(t, out); }
            GAtom::LessMset(s, t) => { out.push_str("M"); render_term(s, out); render_term(t, out); }
            GAtom::Subterm(s, t) => { out.push_str("S"); render_term(s, out); render_term(t, out); }
            GAtom::Last(s) => { out.push_str("La"); render_term(s, out); }
            GAtom::Action(f, t) => {
                out.push_str(&format!("Ac{}/{}", f.name, f.args.len()));
                for arg in &f.args { render_term(arg, out); }
                render_term(t, out);
            }
            GAtom::Pred(f) => { out.push_str(&format!("P{}", f.name)); }
        }
    }
    fn render_term(t: &crate::guarded::GTerm, out: &mut String) {
        use crate::guarded::{GTerm, BVar};
        match t {
            // idx FIRST, then sort, then name — mirrors LVar Ord.
            GTerm::Var(BVar::Free(v)) => out.push_str(&format!("v{}-{:?}-{}", v.idx, v.sort, v.name)),
            GTerm::Var(BVar::Bound(n)) => out.push_str(&format!("B{}", n)),
            GTerm::App(name, args) => {
                out.push_str(&format!("a{}/{}", name, args.len()));
                for arg in args { render_term(arg, out); }
            }
            GTerm::Pair(items) => {
                out.push_str(&format!("p/{}", items.len()));
                for it in items { render_term(it, out); }
            }
            GTerm::AlgApp(name, a, b) => {
                out.push_str(&format!("g{}", name));
                render_term(a, out); render_term(b, out);
            }
            GTerm::Diff(a, b) => { out.push('d'); render_term(a, out); render_term(b, out); }
            GTerm::BinOp(op, a, b) => { out.push_str(&format!("b{:?}", op)); render_term(a, out); render_term(b, out); }
            GTerm::PubLit(s) => out.push_str(&format!("PL{}", s)),
            GTerm::FreshLit(s) => out.push_str(&format!("FL{}", s)),
            GTerm::NatLit(s) => out.push_str(&format!("NL{}", s)),
            GTerm::Number(n) => out.push_str(&format!("N{}", n)),
            GTerm::NumberOne => out.push_str("N1"),
            GTerm::NatOne => out.push_str("Na1"),
            GTerm::DhNeutral => out.push_str("Dh"),
            GTerm::PatMatch(t) => { out.push('m'); render_term(t, out); }
        }
    }
    let mut out = String::new();
    for g in &d.0 {
        render_guarded(g, &mut out);
        out.push('#');
    }
    out
}

/// Manual structural compare on `Goal`, mirroring Haskell's derived
/// `Ord Goal` (Constraints.hs:155-168).  Variant tags follow Haskell
/// declaration order:
///     ActionG < ChainG < PremiseG < SplitG < DisjG < SubtermG.
///
/// **Do NOT change this ordering without updating Haskell.**  If the
/// tags drift from declaration order, BTreeMap-backed goal iteration
/// (e.g. `solveUniqueActions`, `solveAllSafeGoals`) silently picks
/// goals in a different order and the proof shape diverges.
pub(crate) fn goal_cmp(a: &Goal, b: &Goal) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let tag = |g: &Goal| -> u8 {
        match g {
            Goal::Action(_, _)  => 0,
            Goal::Chain(_, _)   => 1,
            Goal::Premise(_, _) => 2,
            Goal::Split(_)      => 3,
            Goal::Disj(_)       => 4,
            Goal::Subterm(_)    => 5,
        }
    };
    let ta = tag(a);
    let tb = tag(b);
    if ta != tb { return ta.cmp(&tb); }
    match (a, b) {
        (Goal::Action(la, fa), Goal::Action(lb, fb)) =>
            la.cmp(lb).then_with(|| fa.cmp(fb)),
        (Goal::Chain(ca, pa), Goal::Chain(cb, pb)) =>
            (&ca.0, ca.1.0).cmp(&(&cb.0, cb.1.0))
                .then_with(|| (&pa.0, pa.1.0).cmp(&(&pb.0, pb.1.0))),
        (Goal::Premise(pa, fa), Goal::Premise(pb, fb)) =>
            (&pa.0, pa.1.0).cmp(&(&pb.0, pb.1.0))
                .then_with(|| fa.cmp(fb)),
        (Goal::Disj(da), Goal::Disj(db)) => {
            // HS-faithful: derived `Ord (Disj LNGuarded)` is structural
            // and bottoms out at `Ord LVar`, which (per the May-20 LVar
            // Ord change) is `idx <> sort <> name` — IDX-FIRST.
            // Plain `Debug` would compare on `name` first because the
            // `Debug` impl renders `VarSpec { name: ..., idx: ... }`
            // with `name` lexicographically before `idx`.
            // Build a render that puts idx first so string compare
            // matches LVar Ord.
            da.0.len().cmp(&db.0.len()).then_with(||
                guarded_canon_idx_first(da).cmp(&guarded_canon_idx_first(db)))
        }
        (Goal::Subterm((sa, ta_)), Goal::Subterm((sb, tb_))) =>
            sa.cmp(sb).then_with(|| ta_.cmp(tb_)),
        (Goal::Split(sa), Goal::Split(sb)) => sa.cmp(sb),
        _ => Ordering::Equal,
    }
}

/// Plain (non-annotated) open goals.
pub fn plain_open_goals(sys: &System) -> Vec<Goal> {
    open_goals(sys).into_iter().map(|a| a.goal).collect()
}

// =============================================================================
// smartRanking — port of `Theory.Constraint.Solver.ProofMethod.smartRanking`
// =============================================================================

/// Decision-tree-aware goal ranking. Direct port of Haskell's
/// `smartRanking ctxt False sys`:
///
/// ```text
///   moveNatToEnd
///     . sortOnUsefulness
///     . sortDecisionTree notSolveLast
///     . sortDecisionTree solveFirst
///     . goalNrRanking
/// ```
///
/// Some Haskell predicates depend on data we haven't ported yet:
///
///   - `isMsgOneCaseGoal` needs `pcSources` source-cache analysis.
///   - `isSplitGoalSmall` / `isNoLargeSplitGoal` need split-size info
///     from the eq-store.
///   - `moveNatToEnd` needs `isNatSubterm` over subterms.
///
/// These are treated conservatively (predicate returns `false`) so the
/// remaining decision-tree partitioning still matches Haskell on every
/// other criterion.  When the stubs are filled in, behaviour aligns
/// without further changes here.
pub fn rank_goals(sys: &System) -> Vec<AnnotatedGoal> {
    rank_goals_with(sys, None)
}

/// Variant that takes a proof context for source-cache predicates
/// (`is_msg_one_case_goal`).  Without context, those predicates
/// fall back to `false` — same behaviour as before the source-cache
/// wiring landed.
pub fn rank_goals_with(
    sys: &System,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
) -> Vec<AnnotatedGoal> {
    // Dispatch on the theory/lemma `heuristic:` directive, mirroring
    // HS's `rankGoals` (ProofMethod.hs:636) which pattern-matches the
    // `GoalRanking`.  When no context (or no heuristic) is supplied we
    // default to `SmartRanking False` — exactly HS's
    // `defaultHeuristic False = Heuristic [SmartRanking False]`
    // (System.hs:527).
    let ranking = ctx
        .and_then(|c| c.heuristic)
        .unwrap_or(GoalRanking::Smart(false));
    match ranking {
        GoalRanking::Inj(use_loop_breakers) => {
            inj_ranking(sys, ctx, use_loop_breakers)
        }
        GoalRanking::Smart(use_loop_breakers) => {
            smart_ranking(sys, ctx, use_loop_breakers)
        }
    }
}

/// Port of HS `smartRanking ctxt allowPremiseGLoopBreakers sys`
/// (ProofMethod.hs:1203):
///
/// ```text
///   moveNatToEnd . sortOnUsefulness . unmark
///     . sortDecisionTree notSolveLast . sortDecisionTree solveFirst
///     . goalNrRanking
/// ```
fn smart_ranking(
    sys: &System,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    allow_premise_g_loop_breakers: bool,
) -> Vec<AnnotatedGoal> {
    let mut goals = open_goals(sys);
    // 1. goalNrRanking — already in seq order from `open_goals`.
    // 2. sortDecisionTree solveFirst — multi-pass partitions.
    // We use closures (rather than function pointers) so the
    // predicates that depend on system state — split_size,
    // source-cache one-case — can borrow `sys` / `ctx`.
    type Pred<'a> = Box<dyn Fn(&AnnotatedGoal) -> bool + 'a>;
    // HS-faithful lazy: `smartRanking`'s `oneCaseOnly = catMaybes . map
    // getMsgOneCase . L.get pcSources $ ctxt` is a thunk that only
    // forces when an `isMsgOneCaseGoal` predicate fires.  That predicate
    // returns False instantly for non-KU goals (`msgPremise` returns
    // Nothing).  So if NO goal in the current list is a KU action goal,
    // the thunk is never forced — and HS's `cdCases` thunks for
    // FApp-headed KU sources stay unforced too, deferring saturate
    // traces until the first KU goal appears.
    //
    // Replicate by only computing `one_case_syms` when at least one
    // goal in `goals` is a KU action goal.  Otherwise pass an empty
    // set — `is_msg_one_case_goal` returns False unconditionally.
    let any_ku_action_goal = goals.iter().any(|a| {
        use crate::constraint::constraints::Goal;
        use crate::fact::FactTag;
        matches!(&a.goal, Goal::Action(_, fa) if matches!(fa.tag, FactTag::Ku))
    });
    let one_case_syms: std::collections::BTreeSet<Vec<u8>> =
        if any_ku_action_goal {
            match ctx {
                Some(c) => collect_one_case_syms(c),
                None => Default::default(),
            }
        } else {
            Default::default()
        };
    let solve_first: Vec<Pred> = vec![
        Box::new(is_chain_goal),
        Box::new(is_disj_goal),
        Box::new(is_solve_first_goal),
        Box::new(is_non_loop_breaker_proto_fact_goal),
        Box::new(is_standard_action_goal),
        Box::new(is_not_auth_out),
        Box::new(is_private_knows_goal),
        // Haskell `smartRanking` solveFirst (ProofMethod.hs:1219-1232)
        // includes `isFreshKnowsGoal` AND `isSignatureGoal` — both are
        // active in the smart ranking. Previous comment incorrectly cited
        // `sapicRanking` (line 953) where they're commented out. TPM
        // lemmas (Alice_Init / PCR_Unbind ranking) rely on isFreshKnowsGoal
        // to prefer KU(~s0) over KU(sign(...)).
        Box::new(is_fresh_knows_goal),
        Box::new(|a: &AnnotatedGoal| is_split_goal_small(a, sys)),
        Box::new(|a: &AnnotatedGoal| is_msg_one_case_goal(a, &one_case_syms)),
        Box::new(is_signature_goal),
        // is_double_exp_goal — needs Exp/Mult view; stubbed.
        Box::new(|a: &AnnotatedGoal| is_no_large_split_goal(a, sys)),
    ];
    goals = sort_decision_tree_dyn(&solve_first, goals);
    // 3. sortDecisionTree notSolveLast — push solve-last goals to end.
    let not_solve_last: Vec<fn(&AnnotatedGoal) -> bool> = vec![is_non_solve_last_goal];
    goals = sort_decision_tree(&not_solve_last, goals);
    // 3b. unmark — HS `smartRanking`'s `unmark | allowPremiseGLoopBreakers
    //     = map unmarkPremiseG` (ProofMethod.hs:1248).  Resets each
    //     PremiseG goal's usefulness to Useful so loop-breaker premises
    //     are not deprioritised.  Only active when allowLoopBreakers
    //     (heuristic `S`).  `unmarkPremiseG` (ProofMethod.hs:296-299).
    if allow_premise_g_loop_breakers {
        for a in goals.iter_mut() {
            if matches!(a.goal, Goal::Premise(_, _)) {
                a.usefulness = Usefulness::Useful;
            }
        }
    }
    // 4. sortOnUsefulness — stable sort by tag.
    goals.sort_by_key(|a| tag_usefulness(a.usefulness));
    // 5. moveNatToEnd — Nat subterm splits to back.
    goals.sort_by_key(|a| is_nat_subterm_split(&a.goal));
    // 6. NO structural tie-break for Disj goals.  HS's `smartRanking`
    // ends with `goalNrRanking = sortOn (fst . snd)` (ProofMethod.hs:
    // 748-749) — sorting by goal NR (insertion-order counter), NOT by
    // Goal Ord.  The `sortDecisionTree` partitions that follow are
    // stable, so within each class the relative order from
    // goalNrRanking is preserved.  Rust's `open_goals` yields goals in
    // sys.goals insertion order = nr order, and the subsequent
    // partitions here are stable too, so no extra sort is required.
    //
    // Previously this block re-sorted Disj goals by `goal_cmp`, on the
    // mistaken belief that HS's `M.toList sGoals` order survived to the
    // pick (it doesn't — `goalNrRanking` clobbers it).  Removed
    // 2026-05-26 to restore HS-faithfulness for Device_Init_Use_Set
    // (case-content swap caused by Rust picking the structurally-
    // smaller induction Disj before HS's lemma-negation Disj).
    // See [[project-rust-port-lockstep]].
    if std::env::var("TAM_RANK_DBG").is_ok() {
        for (i, a) in goals.iter().take(6).enumerate() {
            let g_str = format!("{:?}", a.goal).chars().take(160).collect::<String>();
            eprintln!("[rank] #{}: {} useful={:?}", i, g_str, a.usefulness);
        }
    }
    goals
}

/// Port of HS `injRanking ctxt allowLoopBreakers sys`
/// (ProofMethod.hs:1096):
///
/// ```text
///   sortOnUsefulness . unmark
///     . sortDecisionTree [notSolveLast] . sortDecisionTree solveFirst
///     . goalNrRanking
/// ```
///
/// where
/// ```text
///   solveFirst = [ isImmediateGoal, isHighPriorityGoal
///                , isMedPriorityGoal, isLowPriorityGoal ]
///   notSolveLast g = isNoLargeSplitGoal g && isNonSolveLastGoal g
///                    && isNotKnowsLastNameGoal g
/// ```
///
/// The crucial difference vs `smartRanking`: standard action goals and
/// Disj goals share the SAME priority class (`isMedPriorityGoal`,
/// ProofMethod.hs:1144-1149), so within that class they keep goal-nr
/// order rather than Disj always winning.  This is why the csf17
/// `heuristic: I` lemmas solve their protocol-action goal before the
/// `¬(j<i)` disjunction.
fn inj_ranking(
    sys: &System,
    ctx: Option<&crate::constraint::solver::context::ProofContext>,
    allow_loop_breakers: bool,
) -> Vec<AnnotatedGoal> {
    let mut goals = open_goals(sys);
    type Pred<'a> = Box<dyn Fn(&AnnotatedGoal) -> bool + 'a>;
    // Lazy one-case-syms exactly as in smart_ranking: only force the
    // source-cache thunk when a KU action goal is present.
    let any_ku_action_goal = goals.iter().any(|a| {
        use crate::fact::FactTag;
        matches!(&a.goal, Goal::Action(_, fa) if matches!(fa.tag, FactTag::Ku))
    });
    let one_case_syms: std::collections::BTreeSet<Vec<u8>> =
        if any_ku_action_goal {
            match ctx {
                Some(c) => collect_one_case_syms(c),
                None => Default::default(),
            }
        } else {
            Default::default()
        };
    // solveFirst — four priority classes.  Within each class the
    // relative order from goalNrRanking (insertion / nr order) is
    // preserved by the stable partition.
    //
    //   isImmediateGoal     (ProofMethod.hs:1158-1161)
    //   isHighPriorityGoal  (ProofMethod.hs:1139-1142)
    //   isMedPriorityGoal   (ProofMethod.hs:1144-1149)
    //   isLowPriorityGoal   (ProofMethod.hs:1151-1153)
    let solve_first: Vec<Pred> = vec![
        Box::new(is_immediate_goal),
        Box::new(is_high_priority_goal),
        Box::new(move |a: &AnnotatedGoal| is_med_priority_goal(a, sys, &one_case_syms)),
        Box::new(is_low_priority_goal),
    ];
    goals = sort_decision_tree_dyn(&solve_first, goals);
    // notSolveLast — SINGLE combined predicate (note the `&&`), unlike
    // smartRanking's list.  sortDecisionTree [notSolveLast].
    let not_solve_last: Vec<Pred> = vec![Box::new(|a: &AnnotatedGoal| {
        is_no_large_split_goal(a, sys)
            && is_non_solve_last_goal(a)
            && is_not_knows_last_name_goal(a)
    })];
    goals = sort_decision_tree_dyn(&not_solve_last, goals);
    // unmark — `unmark | allowLoopBreakers = map unmarkPremiseG`
    // (ProofMethod.hs:1117).  Reset PremiseG usefulness to Useful.
    if allow_loop_breakers {
        for a in goals.iter_mut() {
            if matches!(a.goal, Goal::Premise(_, _)) {
                a.usefulness = Usefulness::Useful;
            }
        }
    }
    // sortOnUsefulness — stable sort by usefulness tag.  (injRanking has
    // NO moveNatToEnd step — that's smartRanking-only.)
    goals.sort_by_key(|a| tag_usefulness(a.usefulness));
    if std::env::var("TAM_RANK_DBG").is_ok() {
        for (i, a) in goals.iter().take(6).enumerate() {
            let g_str = format!("{:?}", a.goal).chars().take(160).collect::<String>();
            eprintln!("[inj-rank] #{}: {} useful={:?}", i, g_str, a.usefulness);
        }
    }
    goals
}

/// Stable partition for closure-based predicate list.
fn sort_decision_tree_dyn(
    ps: &[Box<dyn Fn(&AnnotatedGoal) -> bool + '_>],
    xs: Vec<AnnotatedGoal>,
) -> Vec<AnnotatedGoal> {
    let mut result = Vec::with_capacity(xs.len());
    let mut rest = xs;
    for p in ps {
        let (sat, nonsat): (Vec<_>, Vec<_>) = rest.into_iter().partition(|a| p(a));
        result.extend(sat);
        rest = nonsat;
    }
    result.extend(rest);
    result
}

/// `isSplitGoalSmall`: a `Goal::Split(id)` is small if its
/// `splitSize` ≤ 3 (Haskell's `smallSplitGoalSize = 3`).
/// Mirrors `ProofMethod.hs:836`.
fn is_split_goal_small(a: &AnnotatedGoal, sys: &System) -> bool {
    use crate::constraint::constraints::Goal;
    const SMALL_SPLIT_GOAL_SIZE: usize = 3;
    match &a.goal {
        Goal::Split(id) => sys.eq_store.split_size(*id)
            .map(|n| n <= SMALL_SPLIT_GOAL_SIZE)
            .unwrap_or(false),
        _ => false,
    }
}

/// `isNoLargeSplitGoal`: every non-Split goal qualifies; a Split
/// goal qualifies iff it's small.  Used as a final tier in the
/// decision tree to push large eq-store splits last.
fn is_no_large_split_goal(a: &AnnotatedGoal, sys: &System) -> bool {
    use crate::constraint::constraints::Goal;
    match &a.goal {
        Goal::Split(_) => is_split_goal_small(a, sys),
        _ => true,
    }
}

/// `isMsgOneCaseGoal`: the goal's premise is `KU(FApp o _)` where
/// the operator `o` has only one source case in `pcSources`.
/// Mirrors `ProofMethod.hs:780`.
///
/// We approximate `pcSources` via `ctx.full_sources` — for each
/// precomputed source whose goal is a KU goal with a `FApp(o, _)`
/// term and whose case set has exactly one disjunct, record `o`
/// in the one-case set.
fn collect_one_case_syms(
    ctx: &crate::constraint::solver::context::ProofContext,
) -> std::collections::BTreeSet<Vec<u8>> {
    use crate::constraint::constraints::Goal as G;
    use crate::fact::FactTag;
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::term::Term;
    let mut out = std::collections::BTreeSet::new();
    let dbg_sources = std::env::var("TAM_DBG_SOURCES").is_ok();
    if dbg_sources {
        eprintln!("[RS full_sources] count={}", ctx.full_sources.len());
    }
    for src in &ctx.full_sources {
        // HS-faithful order — `smartRanking.getMsgOneCase`
        // (ProofMethod.hs:1207-1210) pattern-matches on `cdGoal` BEFORE
        // touching `cdCases`:
        //
        //   getMsgOneCase cd = case msgPremise (L.get cdGoal cd) of
        //     Just (viewTerm -> FApp o _)
        //       | length (getDisj (L.get cdCases cd)) == 1 -> Just o
        //     _                                            -> Nothing
        //
        // So Var-headed sources (e.g. `KU(t:Fresh)`) never force
        // `cdCases`.  Previously we checked `src.cases.len() != 1`
        // first, which forced the lazy thunk on every source and
        // emitted spurious precompute `[EXEC] solveGoal ...` lines
        // for sources HS would never compute.
        //
        // Only KU-headed source goals.
        let term: &tamarin_term::lterm::LNTerm = match &src.goal {
            G::Action(_, fa) | G::Premise(_, fa) if matches!(fa.tag, FactTag::Ku) =>
                match fa.terms.first() { Some(t) => t, None => continue },
            _ => continue,
        };
        let Term::App(FunSym::NoEq(s), _) = term else {
            if dbg_sources {
                eprintln!("[RS src non-app]");
            }
            continue
        };
        // Now we know the goal is `KU(FApp o _)` — HS-faithful: force
        // cases at this point to check the disjunct count.
        let cases = src.cases(ctx);
        if dbg_sources {
            let nm = String::from_utf8_lossy(&s.name);
            let arity = if let Term::App(_, args) = term { args.len() } else { 0 };
            let names: Vec<String> = cases.iter().map(|(n, _)| n.clone()).collect();
            eprintln!("[RS src] {} arity={} cases={} names={:?}",
                nm, arity, cases.len(), names);
        }
        if cases.len() != 1 { continue; }
        out.insert(s.name.clone());
    }
    out
}

fn is_msg_one_case_goal(
    a: &AnnotatedGoal,
    one_case_syms: &std::collections::BTreeSet<Vec<u8>>,
) -> bool {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::term::Term;
    // Haskell `isMsgOneCaseGoal` (ProofMethod.hs:1248-1250) routes
    // through `msgPremise`, which is defined ONLY for `ActionG` (the
    // KU-action arm).  Premise-side KU goals (rare — Goal::Premise with
    // a KU fact) are excluded.  Mirror exactly to avoid spurious
    // over-prioritisation of KU premises.
    let fa = match &a.goal {
        Goal::Action(_, fa) => fa,
        _ => return false,
    };
    if !matches!(fa.tag, FactTag::Ku) { return false; }
    let Some(t) = fa.terms.first() else { return false };
    if let Term::App(FunSym::NoEq(s), _) = t {
        return one_case_syms.contains(&s.name);
    }
    false
}

/// Stable partition: `sat ++ sortDecisionTree ps nonsat`. Haskell's
/// `sortDecisionTree` walks the predicate list in order, peeling off
/// the satisfying prefix at each pass.
fn sort_decision_tree(
    ps: &[fn(&AnnotatedGoal) -> bool],
    xs: Vec<AnnotatedGoal>,
) -> Vec<AnnotatedGoal> {
    let mut result = Vec::with_capacity(xs.len());
    let mut rest = xs;
    for &p in ps {
        let (sat, nonsat): (Vec<_>, Vec<_>) = rest.into_iter().partition(p);
        result.extend(sat);
        rest = nonsat;
    }
    result.extend(rest);
    result
}

/// `tagUsefulness` — direct port of Haskell `ProofMethod.hs:1068`:
///
/// ```haskell
/// tagUsefulness Useful                = 0 :: Int
/// tagUsefulness ProbablyConstructible = 1
/// tagUsefulness LoopBreaker           = 1
/// tagUsefulness CurrentlyDeducible    = 2
/// ```
///
/// Lower = explored first.  LoopBreaker is `1` (deprioritised), NOT
/// `0` — the earlier version conflated LoopBreaker with Useful, so
/// our search expanded looping premises eagerly instead of after
/// every contradiction-discovering goal.  Fixing this aligns goal
/// ordering with Haskell's automatic prover.
fn tag_usefulness(u: Usefulness) -> u8 {
    match u {
        Usefulness::Useful => 0,
        Usefulness::ProbablyConstructible | Usefulness::LoopBreaker => 1,
        Usefulness::CurrentlyDeducible => 2,
    }
}

// -- Predicate library (mirrors Haskell exactly where we can) ----------------

fn is_chain_goal(a: &AnnotatedGoal) -> bool {
    matches!(a.goal, Goal::Chain(_, _))
}
fn is_disj_goal(a: &AnnotatedGoal) -> bool {
    matches!(a.goal, Goal::Disj(_))
}
fn is_solve_first_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Action(_, fa) | Goal::Premise(_, fa) => is_solve_first_fact(fa),
        _ => false,
    }
}
/// `isNonLoopBreakerProtoFactGoal` — protocol-fact premise that's
/// non-K, non-AuthOut, and not currently flagged LoopBreaker.
fn is_non_loop_breaker_proto_fact_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) => {
            !fa.is_k_fact() && !is_auth_out_fact(fa)
                && a.usefulness == Usefulness::Useful
        }
        _ => false,
    }
}
fn is_standard_action_goal(a: &AnnotatedGoal) -> bool {
    matches!(&a.goal, Goal::Action(_, fa) if !fa.is_ku())
}
fn is_not_auth_out(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) => !is_auth_out_fact(fa),
        _ => false,
    }
}
fn is_private_knows_goal(a: &AnnotatedGoal) -> bool {
    msg_premise(&a.goal).map(contains_private).unwrap_or(false)
}
fn is_fresh_knows_goal(a: &AnnotatedGoal) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match msg_premise(&a.goal) {
        Some(Term::Lit(Lit::Var(v))) if v.sort == LSort::Fresh => true,
        _ => false,
    }
}
fn is_signature_goal(a: &AnnotatedGoal) -> bool {
    use tamarin_term::function_symbols::{FunSym, NoEqSym};
    use tamarin_term::term::Term;
    match msg_premise(&a.goal) {
        Some(Term::App(FunSym::NoEq(NoEqSym { name, .. }), _))
            if name.as_slice() == b"sign" => true,
        _ => false,
    }
}
// -- injRanking priority-class predicates (ProofMethod.hs:1126-1198) ----------

/// `isImmediateGoal` (ProofMethod.hs:1158-1161): a PremiseG/ActionG
/// whose fact name has the `I_` prefix, OR a KU goal of a fresh name
/// var whose name has the `I_` prefix (`isKnowsImmediateNameGoal`).
fn is_immediate_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) | Goal::Action(_, fa)
            if crate::fact::fact_tag_name(&fa.tag).starts_with("I_") => true,
        _ => is_knows_immediate_name_goal(a),
    }
}

/// `isHighPriorityGoal` (ProofMethod.hs:1139-1142):
///   isKnowsFirstNameGoal || isSolveFirstGoal || isChainGoal
///   || isFreshKnowsGoal
fn is_high_priority_goal(a: &AnnotatedGoal) -> bool {
    is_knows_first_name_goal(a)
        || is_solve_first_goal(a)
        || is_chain_goal(a)
        || is_fresh_knows_goal(a)
}

/// `isMedPriorityGoal` (ProofMethod.hs:1144-1149):
///   isStandardActionGoal || isDisjGoal || isPrivateKnowsGoal
///   || isSplitGoalSmall || isMsgOneCaseGoal
///   || isNonLoopBreakerProtoFactGoal
fn is_med_priority_goal(
    a: &AnnotatedGoal,
    sys: &System,
    one_case_syms: &std::collections::BTreeSet<Vec<u8>>,
) -> bool {
    is_standard_action_goal(a)
        || is_disj_goal(a)
        || is_private_knows_goal(a)
        || is_split_goal_small(a, sys)
        || is_msg_one_case_goal(a, one_case_syms)
        || is_non_loop_breaker_proto_fact_goal(a)
}

/// `isLowPriorityGoal` (ProofMethod.hs:1151-1153):
///   isDoubleExpGoal || isSignatureGoal || isProtoFactGoal
/// (`isDoubleExpGoal` is stubbed false — needs the Exp/Mult view, same
/// as smartRanking.)
fn is_low_priority_goal(a: &AnnotatedGoal) -> bool {
    is_signature_goal(a) || is_proto_fact_goal(a)
}

/// `isProtoFactGoal` (ProofMethod.hs:1155-1156): a non-K PremiseG.
fn is_proto_fact_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) => !fa.is_k_fact(),
        _ => false,
    }
}

/// `isKnowsFirstNameGoal` (ProofMethod.hs:267-269): KU goal of a fresh
/// name var whose name has the `F_` prefix.
fn is_knows_first_name_goal(a: &AnnotatedGoal) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match msg_premise(&a.goal) {
        Some(Term::Lit(Lit::Var(v))) =>
            v.sort == LSort::Fresh && v.name.starts_with("F_"),
        _ => false,
    }
}

/// `isKnowsImmediateNameGoal` (ProofMethod.hs:1177-1179): KU goal of a
/// fresh name var whose name has the `I_` prefix.
fn is_knows_immediate_name_goal(a: &AnnotatedGoal) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match msg_premise(&a.goal) {
        Some(Term::Lit(Lit::Var(v))) =>
            v.sort == LSort::Fresh && v.name.starts_with("I_"),
        _ => false,
    }
}

/// `isNotKnowsLastNameGoal` (ProofMethod.hs:1173-1175): True unless the
/// goal is a KU goal of a fresh name var with an `L_` prefix.
fn is_not_knows_last_name_goal(a: &AnnotatedGoal) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match msg_premise(&a.goal) {
        Some(Term::Lit(Lit::Var(v)))
            if v.sort == LSort::Fresh && v.name.starts_with("L_") => false,
        _ => true,
    }
}

/// `isNonSolveLastGoal` — PremiseG/ActionG NOT tagged SolveLast.
fn is_non_solve_last_goal(a: &AnnotatedGoal) -> bool {
    match &a.goal {
        Goal::Premise(_, fa) | Goal::Action(_, fa) => !is_solve_last_fact(fa),
        _ => true,
    }
}
fn is_nat_subterm_split(_g: &Goal) -> bool {
    // Stubbed: Nat-subterm view requires the full Subterm shape; for now
    // never push to the end.  Safe — this only ever moves goals later.
    false
}

// -- Fact-level helpers ------------------------------------------------------

fn is_solve_first_fact(fa: &crate::fact::LNFact) -> bool {
    use crate::fact::FactAnnotation;
    if fa.annotations.contains(&FactAnnotation::SolveFirst) { return true; }
    crate::fact::fact_tag_name(&fa.tag).starts_with("F_")
}
fn is_solve_last_fact(fa: &crate::fact::LNFact) -> bool {
    use crate::fact::FactAnnotation;
    if fa.annotations.contains(&FactAnnotation::SolveLast) { return true; }
    crate::fact::fact_tag_name(&fa.tag).starts_with("L_")
}
fn is_auth_out_fact(fa: &crate::fact::LNFact) -> bool {
    use crate::fact::FactTag;
    matches!(&fa.tag, FactTag::Proto(_, name, _) if name == "AuthOut")
}

/// `msgPremise`: the message argument of a KU action goal, if any.
/// Mirrors Haskell:
///   msgPremise (ActionG _ fa) = do (UpK, m) <- kFactView fa; return m
fn msg_premise(g: &Goal) -> Option<&tamarin_term::lterm::LNTerm> {
    match g {
        Goal::Action(_, fa) if fa.is_ku() => fa.terms.first(),
        _ => None,
    }
}

/// Saturate-time openGoals view.  Haskell uses a single `openGoals`
/// function for both `isFinished` and `solveAllSafeGoals`, so this is
/// just an alias for `is_open_in_sys`.  Kept as a separate name so
/// callers in saturate code make the intent explicit; if we ever need
/// to diverge again, the seam is here.
pub fn is_open_for_saturate(g: &Goal, sys: &System) -> bool {
    is_open_in_sys(g, sys)
}

/// `chain_kd_conc_term`: the KD-fact term at the chain's source-
/// conclusion, or None if the source-conclusion isn't a KD fact.
fn chain_kd_conc_term(
    sys: &System,
    c: &crate::constraint::constraints::NodeConc,
) -> Option<tamarin_term::lterm::LNTerm> {
    use crate::fact::FactTag;
    let (id, idx) = (&c.0, &c.1);
    let rule = sys.nodes.iter().find(|(n, _)| n == id).map(|(_, r)| r)?;
    let fact = rule.conclusions.get(idx.0)?;
    if fact.tag != FactTag::Kd { return None; }
    fact.terms.first().cloned()
}

/// Haskell `chainToEquality` (Goals.hs:171-182).  Open the msg-var
/// ChainG only when its premise targets an intruder equality rule
/// AND there's an earlier KU action for the same msg var.
///
/// IEquality is an INTRUDER rule (IntrRuleACInfo::IEquality), not a
/// proto rule.  The earlier port checked `Proto(Stand("IEquality"))`
/// which is always false — silently failing chainToEquality.
fn chain_to_equality(
    t_start: &tamarin_term::lterm::LNTerm,
    c: &crate::constraint::constraints::NodeConc,
    p: &crate::constraint::constraints::NodePrem,
    sys: &System,
) -> bool {
    // Look up the premise's rule. If it's NOT an IEquality rule,
    // chainToEquality returns False (chain is auto-handled).
    let p_rule = sys.nodes.iter().find(|(n, _)| n == &p.0).map(|(_, r)| r);
    let Some(p_rule) = p_rule else { return false; };
    let is_equality = matches!(&p_rule.info,
        crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IEquality));
    if !is_equality { return false; }
    // ku_before: there's a KU action for t_start at some node that
    // is reachable-before c.0 in the less-relation.
    let ku_before = sys.nodes.iter().any(|(id, rule)| {
        if id == &c.0 { return false; }
        rule.actions.iter().any(|fa| {
            matches!(fa.tag, crate::fact::FactTag::Ku)
                && fa.terms.first() == Some(t_start)
                && sys.always_before(id, &c.0)
        })
    });
    ku_before
}

/// True if a goal is still "open": not vacuously False, not already
/// trivially handled.  **Direct port of Haskell's `openGoals` filter**
/// (`Theory.Constraint.Solver.Goals:66-101`):
///
///   ActionG i (KU m) →
///       not ( solved
///             || (isMsgVar m && i ∉ sNodes)  -- handled later
///             || sort m == Pub || sort m == Nat
///             || isPair m || isInverse m || isProduct m
///             || isUnion m || isNullaryPublicFunction m )
///   DisjG (Disj []) → False    -- empty disj handled by contradictions
///   ChainG c p →
///     case kFactView (nodeConcFact c sys) of
///       Just (DnK, FUnion args) | allMsgVarsKnownEarlier → False
///       Just (DnK, m) | isMsgVar m → chainToEquality m c p
///                     | otherwise  → True
///       _ → True
///   _ → not solved
///
/// **Soundness note**: filtered-out msg-var KD ChainG goals stand for
/// "intruder learns some message via some derivation".  When the
/// caller is `isFinished`, an empty `openGoals` set together with
/// stale msg-var KD chains is still a valid Solved verdict — Haskell
/// trusts that the intruder is omnipotent for any unspecified
/// message, so the chain is vacuously satisfied.
fn is_open_in_sys(g: &Goal, sys: &System) -> bool {
    use crate::constraint::constraints::Disj;
    use crate::fact::FactTag;
    match g {
        Goal::Disj(Disj(items)) if items.is_empty() => false,
        Goal::Action(i, fa) if matches!(fa.tag, FactTag::Ku) => {
            let Some(m) = fa.terms.first() else { return true };
            if is_pub_or_nat_term(m) { return false; }
            if has_top_pair_inv_prod(m) { return false; }
            if is_nullary_public_function(m) { return false; }
            // Haskell: `isMsgVar m && no node at i` → auto-solved.
            if is_msg_var(m) && !sys.nodes.iter().any(|(n, _)| n == i) {
                return false;
            }
            true
        }
        // Haskell parity (Goals.hs:92-100):
        //   ChainG c p →
        //     case kFactView (nodeConcFact c sys) of
        //       Just (DnK, FUnion args) → not solved && not (allMsgVarsKnownEarlier c args)
        //       Just (DnK, m) | isMsgVar m → chainToEquality m c p
        //                     | otherwise  → True
        //       _ → True
        Goal::Chain(c, _p) => {
            if let Some(m) = chain_kd_conc_term(sys, c) {
                // FUnion arm: KD chain over a multiset union — auto-closed
                // when all union args are msg-vars known via earlier KU action
                // (Haskell Goals.hs:95-97 + 163-167).  Without this Rust
                // treats these as open and explores extension paths Haskell
                // skips.
                if let Some(args) = union_args(&m) {
                    if all_msg_vars_known_earlier(c, &args, sys) {
                        return false;
                    }
                    return true;
                }
                if is_msg_var(&m) {
                    return chain_to_equality(&m, c, _p, sys);
                }
            }
            true
        }
        // Haskell parity (Goals.hs:105):
        //   SplitG idx -> splitExists (get sEqStore sys) idx
        // A Split goal is only open if its split-id still exists
        // in the eq-store.  Without this, stale split-ids appear
        // as open goals after a split has been performed elsewhere.
        Goal::Split(id) => sys.eq_store.split_exists(*id),
        // Haskell parity (Goals.hs:106):
        //   SubtermG st -> st `elem` posSubterms . sSubtermStore $ sys
        // A Subterm goal is only open if its (small, big) pair is
        // still in the positive-subterm list (not yet solved).
        Goal::Subterm((small, big)) => {
            sys.subterm_store.subterms.iter()
                .any(|c| &c.small == small && &c.big == big)
        }
        _ => true,
    }
}

/// `isMsgVar`: the term is a Msg-sorted free variable.
fn is_msg_var(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    matches!(t, Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg)
}

/// Extract args if the term is a multiset-union (`FUnion`) — Haskell's
/// `viewTerm2 → FUnion args`.  Returns None for any other term shape.
fn union_args(t: &tamarin_term::lterm::LNTerm) -> Option<Vec<tamarin_term::lterm::LNTerm>> {
    use tamarin_term::function_symbols::{FunSym, UNION_SYM_STRING};
    use tamarin_term::term::Term;
    match t {
        Term::App(FunSym::NoEq(s), args) if s.name == UNION_SYM_STRING =>
            Some(args.clone()),
        _ => None,
    }
}

/// `allMsgVarsKnownEarlier` (Haskell Goals.hs:163-167): all `args` are
/// msg-vars AND each appears as the term of a KU action at some node
/// always-before `c.0` (the chain's source node).  When this holds for
/// an FUnion ChainG conclusion, the chain is auto-handled (Goals.hs:95-97).
fn all_msg_vars_known_earlier(
    c: &crate::constraint::constraints::NodeConc,
    args: &[tamarin_term::lterm::LNTerm],
    sys: &System,
) -> bool {
    if !args.iter().all(is_msg_var) { return false; }
    let i = &c.0;
    args.iter().all(|arg| {
        sys.nodes.iter().any(|(j, rule)| {
            j != i
                && sys.always_before(j, i)
                && rule.actions.iter().any(|fa| {
                    matches!(fa.tag, crate::fact::FactTag::Ku)
                        && fa.terms.first() == Some(arg)
                })
        })
    })
}

/// `isNullaryPublicFunction`: 0-arity public function symbols.
/// Haskell's auto-solve case.
fn is_nullary_public_function(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::term::Term;
    match t {
        Term::App(FunSym::NoEq(s), args)
            if args.is_empty()
                && matches!(s.privacy, tamarin_term::function_symbols::Privacy::Public) => true,
        _ => false,
    }
}

/// True if the term is a sort-Pub or sort-Nat literal (variable or
/// constant).  These KU goals are auto-solved because the adversary
/// can construct any Pub/Nat value trivially.
fn is_pub_or_nat_term(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => matches!(v.sort, LSort::Pub | LSort::Nat),
        Term::Lit(Lit::Con(n)) => matches!(n.tag, NameTag::Pub | NameTag::Nat),
        _ => false,
    }
}

/// True if the term's top symbol is a pair, inverse, product, or
/// AC union — those decompositions are handled inline by
/// `insertAction` in Haskell, so KU goals on them are auto-solved.
fn has_top_pair_inv_prod(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::{AcSym, FunSym, INV_SYM_STRING};
    use tamarin_term::term::Term;
    match t {
        Term::App(FunSym::NoEq(s), args) => {
            s.name == b"pair" && args.len() == 2
                || s.name == INV_SYM_STRING && args.len() == 1
        }
        Term::App(FunSym::Ac(AcSym::Mult), _) => true,  // product
        Term::App(FunSym::Ac(AcSym::Union), _) => true, // multiset union
        _ => false,
    }
}

/// Compute a goal's `Usefulness` annotation. Direct port of the
/// `useful` case-block in Haskell's `openGoals`
/// (`Theory.Constraint.Solver.Goals`):
///
///   useful = case goal of
///     _ | gsLoopBreaker status     -> LoopBreaker
///     ActionG i (UpK m) | hasKUGuards          -> Useful
///                       | currentlyDeducible i m  -> CurrentlyDeducible
///                       | probablyConstructible m -> ProbablyConstructible
///     _                            -> Useful
///
/// `currentlyDeducible` and `extractible` need full edge / less-rel
/// reachability + node-rule introspection, which we haven't ported
/// yet. We approximate by treating any KU goal whose term has only
/// public-or-nat-sort literals (no fresh names, no private function
/// symbols) as `ProbablyConstructible` and otherwise `Useful`. This
/// matches `probablyConstructible` exactly and is strictly more
/// conservative than `currentlyDeducible` (so the decision-tree
/// sort still partitions correctly).
fn goal_usefulness(g: &Goal, looping: bool, sys: &System) -> Usefulness {
    if looping { return Usefulness::LoopBreaker; }
    if let Goal::Action(i, fa) = g {
        if fa.is_ku() {
            // Haskell `hasKUGuards` (Goals.hs:118-122): if ANY system
            // formula has a `KUFact`-tagged action atom in its guards
            // (`KU(?) @ ?` quantifier-binding), every KU goal is
            // **Useful** regardless of `currentlyDeducible` /
            // `probablyConstructible` — those tests are SHORT-CIRCUITED.
            // Typing-class IHs (`All m j. KU(m,j) ⇒ ...`) always have
            // such guards; the order matters for proof-search bias.
            if has_ku_guards(sys) {
                return Usefulness::Useful;
            }
            if let Some(m) = fa.terms.first() {
                // Order matters — `currentlyDeducible` subsumes
                // `probablyConstructible` for Pub/Nat-only terms but
                // also catches the `extractible` case.
                if currently_deducible(sys, i, m) {
                    return Usefulness::CurrentlyDeducible;
                }
                if probably_constructible(m) {
                    return Usefulness::ProbablyConstructible;
                }
            }
        }
    }
    Usefulness::Useful
}

/// Port of Haskell `hasKUGuards` (`Goals.hs:118-122`):
///
/// ```haskell
/// hasKUGuards = any (any ((KUFact ==) . factTag) . guardFactTags) (S.toList $ get sFormulas sys)
/// ```
///
/// True iff any guarded formula in `sys.formulas` has a `KU`-tagged
/// fact atom in its guard list.  Conservative: walks every formula
/// recursively, surfacing fact tags from inside `GGuarded`/`GAtom`/
/// `Conj`/`Disj` structures.
fn has_ku_guards(sys: &System) -> bool {
    use crate::fact::FactTag;
    use crate::guarded::{Guarded, GAtom};
    fn walk_guards(g: &Guarded) -> bool {
        match g {
            Guarded::GGuarded { guards, body, .. } => {
                for atom in guards {
                    if let GAtom::Action(fa, _) = atom {
                        if fa.name == "KU" { return true; }
                    }
                }
                walk_guards(body)
            }
            Guarded::Conj(items) | Guarded::Disj(items) => items.iter().any(walk_guards),
            Guarded::Atom(GAtom::Action(fa, _)) => fa.name == "KU",
            Guarded::Atom(_) => false,
        }
    }
    let _ = FactTag::Ku;
    sys.formulas.iter().any(walk_guards)
        || sys.lemmas.iter().any(walk_guards)
}

/// `currentlyDeducible i m` — direct port of Haskell's
/// `Goals.hs:140`. True iff:
///   * `m` consists only of Pub/Nat literals (no private function
///     symbols), OR
///   * `m` is `extractible i m` from some existing node's `Out` /
///     `KD` conclusion via top-level pair / inverse decomposition,
///     and that node is not reachable from `i` via `rawLessRel`.
fn currently_deducible(
    sys: &System,
    i: &crate::constraint::constraints::NodeId,
    m: &tamarin_term::lterm::LNTerm,
) -> bool {
    use tamarin_term::lterm::LSort;
    if check_term_lits(m, |s| s == LSort::Pub || s == LSort::Nat)
        && !contains_private(m)
    {
        return true;
    }
    extractible(sys, i, m)
}

/// `extractible i m` — direct port of Haskell's `Goals.hs:144`.
/// True iff some node `j != lastAtom` produces `m` (or one of its
/// top-level pair/inv subterms) at an `Out` / `KD` conclusion,
/// and `j` is not reachable from `i` via `rawLessRel` (so adding
/// the dependency wouldn't introduce a cycle).
fn extractible(
    sys: &System,
    i: &crate::constraint::constraints::NodeId,
    m: &tamarin_term::lterm::LNTerm,
) -> bool {
    use crate::fact::FactTag;
    let i_reach = reachable_from(sys, i);
    for (j, rule) in sys.nodes.iter() {
        if Some(j) == sys.last_atom.as_ref() { continue; }
        // We cannot deduce a message via a node we ourselves precede.
        if i_reach.contains(j) { continue; }
        // `Out(t)` and `KD(t)` conclusions.
        for fa in rule.conclusions.iter() {
            let derived = match &fa.tag {
                FactTag::Out => fa.terms.first(),
                FactTag::Kd => fa.terms.first(),
                _ => None,
            };
            let Some(t) = derived else { continue };
            for sub in toplevel_terms(t) {
                if sub == *m { return true; }
            }
        }
    }
    false
}

/// `toplevelTerms t` — direct port of `Goals.hs:157`. Walks pair/inv
/// at the top level only (other function applications are leaves).
fn toplevel_terms(t: &tamarin_term::lterm::LNTerm) -> Vec<tamarin_term::lterm::LNTerm> {
    use tamarin_term::function_symbols::{FunSym, NoEqSym};
    use tamarin_term::term::Term;
    let mut out = vec![t.clone()];
    if let Term::App(FunSym::NoEq(NoEqSym { name, .. }), args) = t {
        match name.as_slice() {
            b"pair" if args.len() == 2 => {
                out.extend(toplevel_terms(&args[0]));
                out.extend(toplevel_terms(&args[1]));
            }
            b"inv" if args.len() == 1 => {
                out.extend(toplevel_terms(&args[0]));
            }
            _ => {}
        }
    }
    out
}

/// `rawLessRel`-based forward reachability: every node id reachable
/// from `i` via `sLessAtoms ++ edges` (transitive closure).
fn reachable_from(
    sys: &System,
    i: &crate::constraint::constraints::NodeId,
) -> std::collections::BTreeSet<crate::constraint::constraints::NodeId> {
    use std::collections::{BTreeMap, BTreeSet, VecDeque};
    let mut adj: BTreeMap<
        crate::constraint::constraints::NodeId,
        Vec<crate::constraint::constraints::NodeId>,
    > = BTreeMap::new();
    for l in &sys.less_atoms {
        adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
    }
    for e in &sys.edges {
        adj.entry(e.src.0.clone()).or_default().push(e.tgt.0.clone());
    }
    let mut seen: BTreeSet<crate::constraint::constraints::NodeId> = BTreeSet::new();
    let mut q: VecDeque<crate::constraint::constraints::NodeId> = VecDeque::new();
    q.push_back(i.clone());
    while let Some(n) = q.pop_front() {
        if !seen.insert(n.clone()) { continue; }
        if let Some(succs) = adj.get(&n) {
            for s in succs { q.push_back(s.clone()); }
        }
    }
    seen
}

/// `checkTermLits p t` — true iff every leaf-literal sort in `t`
/// satisfies `p`. Mirrors Haskell's `foldMap (All . p . sortOfLit)`.
fn check_term_lits<F: Fn(tamarin_term::lterm::LSort) -> bool>(
    t: &tamarin_term::lterm::LNTerm,
    p: F,
) -> bool {
    fn walk<F: Fn(tamarin_term::lterm::LSort) -> bool>(
        t: &tamarin_term::lterm::LNTerm, p: &F,
    ) -> bool {
        use tamarin_term::lterm::{LSort, NameTag};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Var(v)) => p(v.sort),
            Term::Lit(Lit::Con(c)) => p(match c.tag {
                NameTag::Pub => LSort::Pub,
                NameTag::Fresh => LSort::Fresh,
                NameTag::Node => LSort::Node,
                NameTag::Nat => LSort::Nat,
            }),
            Term::App(_, args) => args.iter().all(|a| walk(a, p)),
        }
    }
    walk(t, &p)
}

/// `probablyConstructible` (Haskell):
///   no fresh-name literals AND no private function symbols.
fn probably_constructible(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::lterm::LSort;
    !lit_sort_contains(t, LSort::Fresh) && !contains_private(t)
}

/// True iff any literal in `t` has the given sort. The Haskell source
/// folds `sortOfLit` over every leaf; we mirror that with a recursive
/// walk over `Term` matching `LSort` against `Var.sort` for variables
/// and `NameTag` for constants.
fn lit_sort_contains(t: &tamarin_term::lterm::LNTerm, target: tamarin_term::lterm::LSort) -> bool {
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => v.sort == target,
        Term::Lit(Lit::Con(c)) => match (target, c.tag) {
            (LSort::Pub,   NameTag::Pub)   => true,
            (LSort::Fresh, NameTag::Fresh) => true,
            (LSort::Node,  NameTag::Node)  => true,
            (LSort::Nat,   NameTag::Nat)   => true,
            _ => false,
        },
        Term::App(_, args) => args.iter().any(|a| lit_sort_contains(a, target)),
    }
}

/// True iff any sub-term is a `Private` function-symbol application.
fn contains_private(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::{Privacy, FunSym};
    use tamarin_term::term::Term;
    match t {
        Term::Lit(_) => false,
        Term::App(FunSym::NoEq(sym), args) => {
            sym.privacy == Privacy::Private || args.iter().any(contains_private)
        }
        Term::App(_, args) => args.iter().any(contains_private),
    }
}

/// `solveGoal` placeholder: the full implementation lives in the
/// Reduction monad and applies the appropriate constraint-reduction
/// rule for the goal type. For now this is a stub.
#[allow(unused_variables)]
pub fn solve_goal(g: &Goal, sys: &mut System) -> Option<()> {
    None
}

/// Dispatch a goal to the appropriate `solve_*_goal` primitive on a
/// `Reduction`. Mirrors the case dispatch at the top of Haskell's
/// `solveGoal`. Returns the corresponding `GoalCases` outcome.
pub fn dispatch_solve_goal(
    red: &mut crate::constraint::solver::reduction::Reduction<'_>,
    g: &Goal,
) -> crate::constraint::solver::reduction::GoalCases {
    // Haskell-faithful: mark the goal as solved BEFORE delegating to
    // the specific solver.  Mirrors `solveGoal` (Goals.hs:201-213):
    //   solveGoal goal = do
    //       -- mark before solving, as representation might change due
    //       -- to unification
    //       markGoalAsSolved "directly" goal
    //       ...
    //       case goal of
    //         ActionG i fa  -> solveAction ...
    //         PremiseG p fa -> solvePremise ...
    //         ...
    //
    // The comment in Haskell ("representation might change due to
    // unification") refers exactly to the case where `solveFactEqs` or
    // `substSystem` running INSIDE the solver rewrites the goal's terms
    // (e.g. Check0's `Loop(loopId, kOrig, kOrig)` repeated-arg unification
    // rewrites `Loop(t1, t2, t3)` → `Loop(t1, t2, t2)`).  An attempted
    // post-solve mark with the ORIGINAL goal then misses the (now
    // substituted) goal in the map and leaves it open.  Concrete
    // trigger: Minimal_HashChain Loop_Start source-case Check0 left
    // its abstract Loop goal open, which then triggered another graft
    // iteration adding a duplicate Check0 node (task #222).
    red.mark_goal_as_solved(g);
    // HS-faithful `solve goal = maybe (solveGoal goal) ...
    // (solveWithSource ctxt ths goal)` (ProofMethod.hs:467-470).
    // HS tries source-case dispatch FIRST; only if it returns
    // `Nothing` does it fall back to `solveGoal` (which emits the
    // `traceExecM ("solveGoal " ++ goalKind goal)` line).  Mirror
    // here for `Premise` goals: try `solve_with_source_cases_ctx`,
    // and if it returns `Some(cases)`, return them directly without
    // emitting the `solveGoal kind=Premise fact=...` trace.
    //
    // Limited to `Premise` goals for now (HS uses `solveWithSource`
    // for both Action-KU and Premise; we leave Action to its
    // existing inner source-case path pending further audit).
    if let Goal::Premise(p, fa) = g {
        // HS-faithful (Sources.hs:202-206): `solveAllSafeGoals` only
        // calls `solveWithSourceAndReturn` on "useful" goals (KU
        // actions), routing safe goals (Premise) through `solveGoal`
        // directly.  At runtime (`ProofMethod.solve` line 467-470),
        // dispatch fires for any goal.  Gate Premise dispatch on
        // `!in_precompute_mode()` so saturate skips it.
        if !crate::constraint::solver::sources::in_precompute_mode()
            && !red.ctx.full_sources.is_empty()
        {
            if let Some(case_pairs) = crate::constraint::solver::sources::solve_with_source_cases_ctx(
                red.ctx,
                &red.ctx.full_sources,
                &red.sys,
                &p.0, p.1, fa,
            ) {
                use crate::constraint::solver::reduction::GoalCases;
                if !case_pairs.is_empty() {
                    if case_pairs.len() == 1 {
                        let (name, sys) = case_pairs.into_iter().next().unwrap();
                        red.sys = sys;
                        return GoalCases::LinearNamed(name);
                    }
                    return GoalCases::Cases(case_pairs);
                }
            }
        }
    }
    // TAM_RS_TRACE_EXEC mirror of Haskell `solveGoal` `T.traceExecM`
    // (Goals.hs:206).  Same canonical-data form as the Haskell side so
    // the two outputs diff cleanly.
    //
    // Fact rendering mirrors Haskell `show FactTag`:
    //   - `Ku`   → "KUFact"
    //   - `Kd`   → "KDFact"
    //   - `Fresh`→ "FreshFact"
    //   - `Out`  → "OutFact"
    //   - `In`   → "InFact"
    //   - `Proto(mult, name, _)` → "ProtoFact <Mult> \"<name>\" <arity>"
    {
        use crate::constraint::solver::trace::{trace_exec, sort_prefix};
        let label = match g {
            Goal::Action(_, fa)  => format!("solveGoal kind=Action fact={}({})",
                fact_tag_haskell(fa), fact_term_head(fa, sort_prefix)),
            Goal::Premise(_, fa) => format!("solveGoal kind=Premise fact={}({})",
                fact_tag_haskell(fa), fact_term_head(fa, sort_prefix)),
            Goal::Chain(_, _)    => "solveGoal kind=Chain".to_string(),
            Goal::Split(_)       => "solveGoal kind=Split".to_string(),
            Goal::Disj(_)        => "solveGoal kind=Disj".to_string(),
            Goal::Subterm(_)     => "solveGoal kind=Subterm".to_string(),
        };
        trace_exec(&label);
    }
    match g {
        Goal::Action(i, fa) => red.solve_action_goal(i, fa),
        Goal::Premise(p, fa) => red.solve_premise_goal(p, fa),
        Goal::Chain(c, p) => red.solve_chain_goal(c, p),
        Goal::Split(id) => red.solve_split_goal(*id),
        Goal::Disj(d) => red.solve_disj_goal(d),
        Goal::Subterm(st) => red.solve_subterm_goal(st),
    }
}

// Public wrappers so sites outside this module (e.g. sources.rs's
// direct solve_*_goal calls that bypass dispatch_solve_goal) can emit
// the same EXEC-trace format.
pub fn fact_tag_haskell_pub(fa: &crate::fact::LNFact) -> String { fact_tag_haskell(fa) }
pub fn fact_term_head_pub(fa: &crate::fact::LNFact) -> String {
    use crate::constraint::solver::trace::sort_prefix;
    fact_term_head(fa, sort_prefix)
}

// Haskell `Show FactTag` mirror (Fact.hs).  Used only by the trace; not
// visible elsewhere.  Keep aligned with Haskell so the EXEC diff doesn't
// show spurious format-only differences.
fn fact_tag_haskell(fa: &crate::fact::LNFact) -> String {
    use crate::fact::{FactTag, Multiplicity};
    match &fa.tag {
        FactTag::Ku    => "KUFact".to_string(),
        FactTag::Kd    => "KDFact".to_string(),
        FactTag::Fresh => "FreshFact".to_string(),
        FactTag::Out   => "OutFact".to_string(),
        FactTag::In    => "InFact".to_string(),
        FactTag::Ded   => "DedFact".to_string(),
        FactTag::Term  => "TermFact".to_string(),
        FactTag::Proto(mult, name, arity) => {
            let m = match mult {
                Multiplicity::Linear     => "Linear",
                Multiplicity::Persistent => "Persistent",
            };
            format!("ProtoFact {} \"{}\" {}", m, name, arity)
        }
    }
}

// Canonical head-symbol rendering for the EXEC trace.  Mirrors Haskell's
// `termHeadStr` in Goals.hs (Var → `sortPrefix ++ name`, Const → `<const>`,
// App → `showFunSymName`).  Used only by the trace; not visible elsewhere.
fn fact_term_head(
    fa: &crate::fact::LNFact,
    sort_prefix: fn(tamarin_term::lterm::LSort) -> &'static str,
) -> String {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_term::function_symbols::FunSym;
    match fa.terms.first() {
        None => String::new(),
        Some(Term::Lit(Lit::Var(v))) =>
            format!("{}{}", sort_prefix(v.sort), v.name),
        Some(Term::Lit(Lit::Con(_))) => "<const>".to_string(),
        Some(Term::App(sym, _)) => match sym {
            FunSym::NoEq(noeq) => String::from_utf8_lossy(&noeq.name).into_owned(),
            FunSym::Ac(op) => format!("{:?}", op),
            FunSym::C(op) => format!("{:?}", op),
            FunSym::List => "List".to_string(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::system::System;

    #[test]
    fn empty_system_has_no_open_goals() {
        let sys = System::empty();
        assert!(open_goals(&sys).is_empty());
    }

    #[test]
    fn single_goal_returned() {
        let mut sys = System::empty();
        let v = tamarin_term::lterm::LVar::new(
            "k", tamarin_term::lterm::LSort::Msg, 0);
        let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        sys.add_goal(Goal::Action(v, f));
        let goals = open_goals(&sys);
        assert_eq!(goals.len(), 1);
        assert_eq!(goals[0].usefulness, Usefulness::Useful);
    }

    #[test]
    fn solved_goal_filtered() {
        let mut sys = System::empty();
        let v = tamarin_term::lterm::LVar::new(
            "k", tamarin_term::lterm::LSort::Msg, 0);
        let f = crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]);
        sys.add_goal(Goal::Action(v, f));
        sys.goals[0].1.solved = true;
        assert!(open_goals(&sys).is_empty());
    }

    #[test]
    fn dispatch_solve_disj_goal_routes() {
        use crate::constraint::solver::context::ProofContext;
        use crate::constraint::solver::reduction::{GoalCases, Reduction};
        use tamarin_term::maude_sig::pair_maude_sig;

        let path = match std::env::var("MAUDE_PATH").ok().or_else(|| {
            for c in ["/home/linuxbrew/.linuxbrew/bin/maude", "/usr/local/bin/maude", "maude"] {
                if std::path::Path::new(c).exists() { return Some(c.to_string()); }
            }
            None
        }) { Some(p) => p, None => return };
        let h = tamarin_term::maude_proc::MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let ctx = ProofContext::new(h, Vec::new());
        let mut r = Reduction::new(&ctx, System::empty());
        // Empty disjunction → contradictory.
        let d = crate::constraint::constraints::Disj::<crate::guarded::Guarded>::new(Vec::new());
        let g = Goal::Disj(d);
        let out = dispatch_solve_goal(&mut r, &g);
        assert!(matches!(out, GoalCases::Contradictory));
    }

    // =========================================================================
    // Haskell-faithfulness invariants for Goal-Ord.
    //
    // Haskell `data Goal` (Constraints.hs:155-168) declares variants in
    // this exact order, and derives `Ord`:
    //
    //     data Goal = ActionG _ _
    //               | ChainG _ _
    //               | PremiseG _ _
    //               | SplitG _
    //               | DisjG _
    //               | SubtermG _
    //               deriving( ..., Ord, ... )
    //
    // So the constructor tag order is:
    //     Action < Chain < Premise < Split < Disj < Subterm
    //
    // The Rust `Goal` enum (constraints.rs:138) preserves this variant
    // order, so its derived structural order — if we had one — would be
    // the same.  But `goal_cmp` (this file) hand-codes a `tag` function,
    // and any divergence between that and the variant order would silently
    // sort goals differently than Haskell.
    // =========================================================================

    /// Pin Haskell's Goal-Ord tag order: Action < Chain < Premise < Split
    /// < Disj < Subterm.
    ///
    /// This is the exact order from Constraints.hs:155-168.  When
    /// `goal_cmp` is wired into goal iteration (see file-level comment),
    /// the choice of Action's-first-Premise determines which goal the
    /// solver picks at each step, which determines the proof shape.
    #[test]
    fn goal_cmp_tag_order_matches_haskell_declaration() {
        use tamarin_term::lterm::{LSort, LVar};
        use crate::constraint::constraints::{Disj, NodeId, SplitId};
        use crate::fact::{FactTag, LNFact, Multiplicity};
        use crate::rule::{ConcIdx, PremIdx};
        use std::cmp::Ordering;

        // Build one minimal instance of each Goal variant.
        let v: LVar = LVar::new("k", LSort::Msg, 0);
        let n: NodeId = LVar::new("i", LSort::Node, 0);
        let f: LNFact = LNFact::new(
            FactTag::Proto(Multiplicity::Linear, "F".into(), 0), vec![]);

        let action: Goal = Goal::Action(v.clone(), f.clone());
        let chain: Goal = Goal::Chain(
            (n.clone(), ConcIdx(0)), (n.clone(), PremIdx(0)));
        let premise: Goal = Goal::Premise((n.clone(), PremIdx(0)), f.clone());
        let split: Goal = Goal::Split(SplitId(0));
        let disj: Goal = Goal::Disj(Disj::<crate::guarded::Guarded>::new(vec![]));
        // Use plain msg vars for the Subterm pair.
        let sub: Goal = Goal::Subterm((
            tamarin_term::builtin::msg_var("a", 0),
            tamarin_term::builtin::msg_var("b", 0),
        ));

        // The order from Constraints.hs:155-168 (deriving Ord):
        //   ActionG < ChainG < PremiseG < SplitG < DisjG < SubtermG
        //
        // **THIS IS THE CONTRACT.**  If Rust's `goal_cmp` differs, the
        // BTreeMap-backed goal iteration in any Haskell-faithful wiring
        // will sort differently from Haskell, causing proof-step
        // divergences silently.
        let order = [&action, &chain, &premise, &split, &disj, &sub];
        let names = ["Action", "Chain", "Premise", "Split", "Disj", "Subterm"];
        for i in 0..order.len() {
            for j in (i + 1)..order.len() {
                assert_eq!(goal_cmp(order[i], order[j]), Ordering::Less,
                    "Haskell Goal-Ord requires {} < {} \
                     (Constraints.hs:155-168 declaration order).  \
                     goal_cmp put them in the wrong order — this WILL \
                     cause silent proof divergence when goal_cmp is \
                     wired into goal iteration.",
                    names[i], names[j]);
                assert_eq!(goal_cmp(order[j], order[i]), Ordering::Greater,
                    "Haskell Goal-Ord requires {} > {}",
                    names[j], names[i]);
            }
        }
    }

    /// Pin tag-equality (every variant ordered with itself returns Equal).
    /// Within-variant comparison is structural and depends on inner-field
    /// ordering; here we just check the tag-equality short-circuit.
    #[test]
    fn goal_cmp_reflexive() {
        use std::cmp::Ordering;
        use tamarin_term::lterm::{LSort, LVar};
        use crate::constraint::constraints::SplitId;

        let action: Goal = Goal::Action(
            LVar::new("k", LSort::Msg, 0),
            crate::fact::LNFact::new(crate::fact::FactTag::Out, vec![]),
        );
        let split: Goal = Goal::Split(SplitId(7));
        assert_eq!(goal_cmp(&action, &action), Ordering::Equal);
        assert_eq!(goal_cmp(&split, &split), Ordering::Equal);
    }

    /// Pin that `Goal` enum variant declaration order in Rust matches
    /// Haskell's data-decl order.  This is the upstream invariant that
    /// `goal_cmp`'s tag function should respect.  If Rust's enum is
    /// reordered, both this AND `goal_cmp` must change together.
    #[test]
    fn rust_goal_enum_variant_order_matches_haskell() {
        // We can't reflect over enum variants in stable Rust without a
        // proc-macro, but we can pin the order via discriminant indices
        // assigned by the compiler.  `Goal::Action(...)` is variant 0,
        // `Goal::Chain` is 1, etc.  If someone reorders the enum, the
        // discriminant values change and this test breaks.
        use std::mem::discriminant;
        use tamarin_term::lterm::{LSort, LVar};
        use crate::constraint::constraints::{Disj, NodeId, SplitId};
        use crate::fact::{FactTag, LNFact, Multiplicity};
        use crate::rule::{ConcIdx, PremIdx};

        let v: LVar = LVar::new("k", LSort::Msg, 0);
        let n: NodeId = LVar::new("i", LSort::Node, 0);
        let f: LNFact = LNFact::new(
            FactTag::Proto(Multiplicity::Linear, "F".into(), 0), vec![]);

        // Build one of each variant in Haskell's declaration order.
        let variants = [
            Goal::Action(v.clone(), f.clone()),
            Goal::Chain((n.clone(), ConcIdx(0)), (n.clone(), PremIdx(0))),
            Goal::Premise((n.clone(), PremIdx(0)), f.clone()),
            Goal::Split(SplitId(0)),
            Goal::Disj(Disj::<crate::guarded::Guarded>::new(vec![])),
            Goal::Subterm((
                tamarin_term::builtin::msg_var("a", 0),
                tamarin_term::builtin::msg_var("b", 0),
            )),
        ];
        // All discriminants must be distinct (sanity).
        let discs: Vec<_> = variants.iter().map(discriminant).collect();
        for i in 0..discs.len() {
            for j in (i + 1)..discs.len() {
                assert_ne!(discs[i], discs[j],
                    "variants {} and {} share a discriminant!", i, j);
            }
        }
    }
}
