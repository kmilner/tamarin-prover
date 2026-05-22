//! Skeleton for the `System` sequent — the solver's working state.
//!
//! Port of `Theory.Constraint.System.System` (from the 1936-line
//! `Theory/Constraint/System.hs`). Many fields here are "morally"
//! placeholders (the Haskell record carries Maude-bound data we
//! haven't yet ported). The shape is close enough that incremental
//! population keeps the whole module compiling.

use crate::constraint::constraints::{Edge, Goal, LessAtom, NodeId};
use crate::guarded::Guarded;
use crate::rule::RuleACInst;
use crate::tools::{EquationStore, SubtermStore};

// =============================================================================
// Source kind / side annotations
// =============================================================================

/// Whether a system arose from raw or refined source-traces. Mirrors
/// Haskell's `SourceKind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum SourceKind { RawSources, RefinedSources }

/// Whether the system tracks the LHS or RHS of a diff theory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Side { LHS, RHS }

// =============================================================================
// System
// =============================================================================

/// A constraint-solver sequent. The solver mutates this incrementally
/// during proof search.
///
/// Storage choices: we use `Vec` for collections rather than
/// `BTreeSet`/`BTreeMap` because the underlying values
/// (`Edge`/`Goal`/`Guarded`/`RuleACInst`) don't all derive `Ord` /
/// `Hash` yet. Lookup is currently linear; once those derives land
/// we can swap to ordered containers without changing the public
/// surface.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct System {
    pub source_kind: Option<SourceKind>,
    pub side: Option<Side>,
    /// Node id → rule instance providing its conclusion.
    pub nodes: Vec<(NodeId, RuleACInst)>,
    /// Edges from conclusions to premises.
    pub edges: Vec<Edge>,
    /// `i < j` constraints with reason tags.
    pub less_atoms: Vec<LessAtom>,
    /// Open formula obligations (lemma negations, restrictions, etc.).
    pub formulas: Vec<Guarded>,
    /// Already-solved formulas (for memoisation).
    pub solved_formulas: Vec<Guarded>,
    /// Lemmas / safety assumptions added by `insert_lemma` (mirrors
    /// Haskell's `sLemmas`). These are treated as known-true.
    pub lemmas: Vec<Guarded>,
    /// Last-atom constraint, e.g. `last(i)` — at most one per system.
    pub last_atom: Option<NodeId>,
    /// Equation store.
    pub eq_store: EquationStore,
    /// Subterm store.
    pub subterm_store: SubtermStore,
    /// Open goals paired with their current status.
    pub goals: Vec<(Goal, GoalStatus)>,
    /// Next available `SplitId`.
    pub next_split: u64,
    /// Source-case names already grafted into this branch.  Mirrors
    /// Haskell's `filterCases` invariant in `solveAllSafeGoals`: once
    /// a precomputed case has been used to discharge a goal, it is
    /// removed from the available source list for the remainder of
    /// the search branch.  Without this, a chain-saturated case whose
    /// internal KU goals re-spawn at runtime will pick the same case
    /// again, looping until depth-limit.
    pub used_sources: Vec<String>,
    /// Set when `subst_system` detected a shape mismatch — i.e. two
    /// distinct rule instances collapsed to the same node id with
    /// disagreeing fact-list shapes.  This is the same Maude-witness
    /// conflation pattern as Fresh-consumer conflation, just at the
    /// rule level instead of the premise level.  Recorded as a flag
    /// (separately from the gfalse in formulas) so `is_finished` can
    /// route conflation-induced FormulasFalse → Unfinishable, while
    /// legitimate gfalse-in-formulas (e.g. from a body that genuinely
    /// simplifies to ⊥) still produces Contradictory.
    pub shape_mismatch_conflation: bool,
    /// Set when `solve_action_goal` (under TAM_APPLY_SOURCE) had to
    /// drop one or more source-cases via the Fresh-consumer conflation
    /// guard.  The dropped case may have been the actual witness path,
    /// so we can't trust an overall Contradictory rollup.  `is_finished`
    /// routes Contradictory→Unfinishable when this flag is set,
    /// preserving soundness on the new applySource path.
    pub lost_conflation_case_apply_source: bool,
    /// Set when a search branch consumed a source-case from a
    /// precomputed `Source` whose case enumeration was truncated by
    /// `TAM_MAX_CLOSURES_PER_SOURCE` (i.e. `Source.incomplete=true`).
    /// `is_finished` must route Solved→Sorry in this case — the
    /// dropped cases could contain attack witnesses we never enumerated.
    /// Without this, the cap is unsound (denning_sacco::sessionsmatch
    /// wrong-VERIFIED at cap=256).
    pub used_incomplete_source: bool,
    /// Provenance tracking (task #157): universals in `lemmas` that
    /// came from `[sources]`-tagged lemma bodies.  Haskell never adds
    /// these to `sLemmas` (only `[reuse]` lemmas go there via
    /// `gatherReusableLemmas`), so its runtime `insertImpliedFormulas`
    /// never fires them — they're only consulted via
    /// `refineWithSourceAsms` at precompute.  We add them to `lemmas`
    /// as a workaround for our weaker refine; tagging them here lets
    /// `insertImpliedFormulas` skip them at runtime (when
    /// `!in_precompute_mode`) while still firing them during refine's
    /// Step 1 simplify (where it's needed to drop typing-violating
    /// cases).  Matching Haskell's runtime behaviour eliminates the
    /// spurious `case case_1`/`case case_2` Disj-decomposition steps
    /// that appear in our proof trees for ~10 corpus lemmas.
    pub sources_lemma_universals: Vec<Guarded>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct GoalStatus {
    /// How many times the solver has applied a tactic to this goal.
    pub age: u64,
    /// Whether the goal is currently "loop-marked".
    pub looping: bool,
    /// Whether the goal is already solved (kept for replay).
    pub solved: bool,
}

impl System {
    pub fn empty() -> Self { Self::default() }

    /// Add an open goal, no-op if already present (compared by `Goal`
    /// equality).
    pub fn add_goal(&mut self, g: Goal) {
        if !self.goals.iter().any(|(existing, _)| existing == &g) {
            self.goals.push((g, GoalStatus::default()));
        }
    }

    /// `insertGoal` mirror with loop-breaker flag — direct port of
    /// Haskell's `insertGoal goal isLoopBreaker`. Marks the goal's
    /// `looping` field so the smart ranker can deprioritise it.
    pub fn add_goal_with_loop_flag(&mut self, g: Goal, looping: bool) {
        if let Some(slot) = self.goals.iter_mut().find(|(existing, _)| existing == &g) {
            // Existing goal — keep its prior `looping` state if already
            // set true (matches Haskell's monoidal status update).
            slot.1.looping = slot.1.looping || looping;
            return;
        }
        let mut st = GoalStatus::default();
        st.looping = looping;
        self.goals.push((g, st));
    }

    /// Insert a new node into the sequent. Replaces an existing entry
    /// for the same id.
    pub fn add_node(&mut self, id: NodeId, rule: RuleACInst) {
        if let Some(slot) = self.nodes.iter_mut().find(|(k, _)| k == &id) {
            slot.1 = rule;
        } else {
            self.nodes.push((id, rule));
        }
    }

    /// Add an edge if not already present.
    pub fn add_edge(&mut self, e: Edge) {
        if !self.edges.contains(&e) {
            crate::constraint::solver::trace::trace_exec("insertEdges n=1");
            self.edges.push(e);
        }
    }

    /// Add a `<` atom if not already present (equality ignores reason).
    /// Add a less-atom. Self-loops (a < a) are degenerate — they
    /// produce immediate contradictions via the cyclic check.  In
    /// most cases such a self-loop arises from subst_system collapsing
    /// two distinct nodes to the same id AFTER a less-atom between
    /// them was already recorded; the resulting `a < a` is a true
    /// contradiction.  We still add it (so contradictions catches
    /// it) but log under TAM_DBG_SELF_LOOP for diagnosis.
    pub fn add_less(&mut self, l: LessAtom) {
        if !self.less_atoms.iter().any(|x| x == &l) { self.less_atoms.push(l); }
    }

    /// `alwaysBefore i j`: True iff `i < j` in every model of the system.
    /// Mirrors Haskell's `Theory.Constraint.System.alwaysBefore`. Computed
    /// as transitive reachability over `rawLessRel = sLessAtoms ++ edges`.
    pub fn always_before(&self, i: &NodeId, j: &NodeId) -> bool {
        if i == j { return false; }
        // Build adjacency from less atoms + edges.
        let mut adj: std::collections::BTreeMap<NodeId, Vec<NodeId>>
            = std::collections::BTreeMap::new();
        for l in &self.less_atoms {
            adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
        }
        for e in &self.edges {
            adj.entry(e.src.0.clone()).or_default().push(e.tgt.0.clone());
        }
        // BFS from i until j.
        let mut frontier: std::collections::VecDeque<NodeId>
            = std::collections::VecDeque::new();
        let mut visited: std::collections::BTreeSet<NodeId>
            = std::collections::BTreeSet::new();
        frontier.push_back(i.clone());
        visited.insert(i.clone());
        while let Some(n) = frontier.pop_front() {
            if let Some(nbrs) = adj.get(&n) {
                for nb in nbrs {
                    if nb == j { return true; }
                    if visited.insert(nb.clone()) {
                        frontier.push_back(nb.clone());
                    }
                }
            }
        }
        false
    }

    /// `insertLemma`: flatten a top-level `Conj` into individual lemma
    /// entries. Mirrors the Haskell `insertLemma` recursion.
    pub fn insert_lemma(&mut self, l: Guarded) {
        match l {
            Guarded::Conj(items) => {
                for item in items { self.insert_lemma(item); }
            }
            other => {
                if !self.lemmas.contains(&other) { self.lemmas.push(other); }
            }
        }
    }

    pub fn insert_lemmas(&mut self, ls: Vec<Guarded>) {
        for l in ls { self.insert_lemma(l); }
    }
}

// =============================================================================
// `formulaToSystem` — port of the `Theory.Constraint.System.formulaToSystem`
// entry point used by `Theory.Proof.proveLemma`.
// =============================================================================

/// Build the initial constraint system that has to be proven to show
/// the given lemma formula holds modulo `restrictions`.
///
/// - `AllTraces` lemmas are *negated* (we look for a counterexample).
/// - `ExistsTrace` lemmas are kept as-is.
/// - Non-safety restrictions are conjoined into the formula.
/// - Safety restrictions are inserted as known-true lemmas.
pub fn formula_to_system(
    restrictions: Vec<Guarded>,
    source_kind: SourceKind,
    trace_quantifier: tamarin_parser::ast::TraceQuantifier,
    is_diff: bool,
    fm: &Guarded,
) -> System {
    use tamarin_parser::ast::TraceQuantifier;
    use crate::guarded::{gconj, gnot, is_safety_formula};

    let mut sys = System::empty();
    sys.source_kind = Some(source_kind);
    if is_diff {
        // Diff is not yet handled in our skeleton; record it via an
        // empty marker Side. Real diff support arrives later.
        sys.side = None;
    }

    // Partition restrictions into safety / non-safety.
    let (safety, other_restrictions): (Vec<Guarded>, Vec<Guarded>) =
        restrictions.into_iter().partition(is_safety_formula);

    // Negate AllTraces lemmas; keep ExistsTrace as-is.
    let gf1 = match trace_quantifier {
        TraceQuantifier::ExistsTrace => fm.clone(),
        TraceQuantifier::AllTraces => gnot(fm),
    };
    // Conjoin non-safety restrictions.
    let mut conj_items = vec![gf1];
    conj_items.extend(other_restrictions);
    let gf2 = gconj(conj_items);
    sys.formulas.push(gf2);
    // Safety restrictions are added as known-true lemmas.
    sys.insert_lemmas(safety);
    sys
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use crate::fact::LNFact;

    #[test]
    fn empty_system_is_default() {
        let s = System::empty();
        assert!(s.nodes.is_empty());
        assert!(s.edges.is_empty());
        assert!(s.goals.is_empty());
        assert_eq!(s.next_split, 0);
    }

    #[test]
    fn add_goal_idempotent() {
        let mut s = System::empty();
        let v = LVar::new("k", LSort::Msg, 0);
        let f = LNFact::new(crate::fact::FactTag::Out, vec![]);
        let g = Goal::Action(v, f);
        s.add_goal(g.clone());
        s.add_goal(g);
        assert_eq!(s.goals.len(), 1);
    }

    #[test]
    fn insert_lemma_flattens_top_level_conj() {
        let mut s = System::empty();
        // Use Atom-bearing lemmas so the smart Conj flattening doesn't
        // optimise them away. We just need two leaves that don't
        // recurse further into Conj.
        use tamarin_parser::ast::{Atom, SortHint, Term, VarSpec};
        let mkvar = |n: &str| Term::Var(VarSpec {
            name: n.to_string(), idx: 0, sort: SortHint::Node, typ: None,
        });
        let l1 = crate::guarded::Guarded::Atom(Atom::Last(mkvar("i")));
        let l2 = crate::guarded::Guarded::Atom(Atom::Last(mkvar("j")));
        s.insert_lemma(crate::guarded::Guarded::Conj(vec![l1.clone(), l2.clone()]));
        assert_eq!(s.lemmas.len(), 2);
        assert!(s.lemmas.contains(&l1));
        assert!(s.lemmas.contains(&l2));
    }

    #[test]
    fn formula_to_system_exists_trace_keeps_formula() {
        use tamarin_parser::ast::TraceQuantifier;
        let f = crate::guarded::gtrue();
        let sys = formula_to_system(
            Vec::new(),
            SourceKind::RawSources,
            TraceQuantifier::ExistsTrace,
            false,
            &f,
        );
        // ExistsTrace ⇒ formula kept as-is.
        assert_eq!(sys.formulas.len(), 1);
        assert_eq!(sys.formulas[0], f);
    }

    #[test]
    fn formula_to_system_all_traces_negates() {
        use tamarin_parser::ast::TraceQuantifier;
        // For AllTraces lemma `T`, the negation is `gfalse`.
        let f = crate::guarded::gtrue();
        let sys = formula_to_system(
            Vec::new(),
            SourceKind::RawSources,
            TraceQuantifier::AllTraces,
            false,
            &f,
        );
        assert_eq!(sys.formulas.len(), 1);
        assert_eq!(sys.formulas[0], crate::guarded::gfalse());
    }

    #[test]
    fn formula_to_system_partitions_safety_restrictions() {
        use tamarin_parser::ast::TraceQuantifier;
        let f = crate::guarded::gtrue();
        // gtrue is safety (no Ex, no free vars).
        // gfalse is also safety (Disj([])) — no Ex, no free vars.
        let restrictions = vec![
            crate::guarded::gtrue(),
            crate::guarded::gfalse(),
        ];
        let sys = formula_to_system(
            restrictions,
            SourceKind::RawSources,
            TraceQuantifier::ExistsTrace,
            false,
            &f,
        );
        // All restrictions are safety → all go into lemmas.
        assert_eq!(sys.formulas.len(), 1);
        // gtrue is `Conj []` which `insert_lemma` flattens to nothing
        // (no items inside the empty conjunction). gfalse stays.
        // Lemmas should contain at least the gfalse non-conj entry.
        assert!(sys.lemmas.contains(&crate::guarded::gfalse()));
    }
}
