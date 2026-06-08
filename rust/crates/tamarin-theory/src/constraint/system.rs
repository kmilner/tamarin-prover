//! Skeleton for the `System` sequent — the solver's working state.
//!
//! Port of `Theory.Constraint.System.System` (from the 1936-line
//! `Theory/Constraint/System.hs`). Many fields here are "morally"
//! placeholders (the Haskell record carries Maude-bound data we
//! haven't yet ported). The shape is close enough that incremental
//! population keeps the whole module compiling.

use std::cell::Cell;

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
#[derive(Debug, Default)]
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
    /// Monotonic goal-number counter (`_sNextGoalNr`,
    /// System.hs:394).  Advanced on every goal insertion (even when
    /// the goal already exists — HS's `insertGoalStatus`
    /// Reduction.hs:606-609 always `succ`s it).  Each new goal records
    /// the current value as its `GoalStatus.nr`.
    pub next_goal_nr: u64,
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
    /// Cached max free-var idx across the system.  `None` means
    /// "invalid — lazily recompute on next `bounds_max` call".
    /// Maintained incrementally on additive mutations and
    /// invalidated on mutations that could LOWER the max.
    ///
    /// Excluded from `PartialEq`/`Clone` semantics: two systems with
    /// the same content but different cache state are still equal,
    /// and cloning copies the cached value verbatim.
    ///
    /// Wrapped in `Cell` so `bounds_max(&System)` can populate it
    /// without requiring `&mut System` at every call site.
    pub max_var_idx_cache: Cell<Option<u64>>,
}

// Manual `Clone` — copies the cache value (NOT invalidates).  System
// gets cloned heavily (every prove-step grafts a child); a clone that
// invalidated the cache would defeat the optimisation.
impl Clone for System {
    fn clone(&self) -> Self {
        Self {
            source_kind: self.source_kind,
            side: self.side,
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
            less_atoms: self.less_atoms.clone(),
            formulas: self.formulas.clone(),
            solved_formulas: self.solved_formulas.clone(),
            lemmas: self.lemmas.clone(),
            last_atom: self.last_atom.clone(),
            eq_store: self.eq_store.clone(),
            subterm_store: self.subterm_store.clone(),
            goals: self.goals.clone(),
            next_goal_nr: self.next_goal_nr,
            next_split: self.next_split,
            used_sources: self.used_sources.clone(),
            shape_mismatch_conflation: self.shape_mismatch_conflation,
            lost_conflation_case_apply_source:
                self.lost_conflation_case_apply_source,
            used_incomplete_source: self.used_incomplete_source,
            sources_lemma_universals: self.sources_lemma_universals.clone(),
            max_var_idx_cache: Cell::new(self.max_var_idx_cache.get()),
        }
    }
}

// Manual `PartialEq` — ignores the cache.  Two systems with identical
// content but different cache state (e.g. one freshly cloned, one
// after `bounds_max` populated its cache) must compare equal — see
// `proof_method.rs:358` (`r.sys == cleanup(sys)`).
impl PartialEq for System {
    fn eq(&self, other: &Self) -> bool {
        self.source_kind == other.source_kind
            && self.side == other.side
            && self.nodes == other.nodes
            && self.edges == other.edges
            && self.less_atoms == other.less_atoms
            && self.formulas == other.formulas
            && self.solved_formulas == other.solved_formulas
            && self.lemmas == other.lemmas
            && self.last_atom == other.last_atom
            && self.eq_store == other.eq_store
            && self.subterm_store == other.subterm_store
            && self.goals == other.goals
            && self.next_goal_nr == other.next_goal_nr
            && self.next_split == other.next_split
            && self.used_sources == other.used_sources
            && self.shape_mismatch_conflation == other.shape_mismatch_conflation
            && self.lost_conflation_case_apply_source
                == other.lost_conflation_case_apply_source
            && self.used_incomplete_source == other.used_incomplete_source
            && self.sources_lemma_universals == other.sources_lemma_universals
    }
}

/// Canonicalize a Goal for dedup-comparison in `add_goal_with_loop_flag`.
/// For Disj goals, applies `normalize_bound_lvars` to the alternatives
/// so alpha-equivalent Disjs (re-fired across simplify iterations with
/// different freshen-shifted bound idxs) compare equal — mirroring HS's
/// DeBruijn-bound structural equality on the Map key.
///
/// Identity for non-Disj goals (their var idxs are semantically
/// significant — same NodeId means same node etc.).
pub fn canonical_goal_for_dedup(g: &Goal) -> Goal {
    match g {
        Goal::Disj(d) => {
            let canon_alts: Vec<crate::guarded::Guarded> = d.0.iter()
                .map(crate::guarded::normalize_bound_lvars)
                .collect();
            Goal::Disj(crate::constraint::constraints::Disj::new(canon_alts))
        }
        _ => g.clone(),
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct GoalStatus {
    /// How many times the solver has applied a tactic to this goal.
    pub age: u64,
    /// Whether the goal is currently "loop-marked".
    pub looping: bool,
    /// Whether the goal is already solved (kept for replay).
    pub solved: bool,
    /// Goal creation order (`_gsNr` in HS `GoalStatus`,
    /// System.hs:373).  Assigned from `System.next_goal_nr` at first
    /// insertion; on re-insertion of an existing goal HS keeps the
    /// `min` (so the original, smaller nr wins — see
    /// `combineGoalStatus`).  `goalNrRanking` (ProofMethod.hs:748-749
    /// `sortOn (fst . snd)`) orders goals by this number, NOT by Vec
    /// position.  This is the canonical tie-break within a heuristic
    /// priority class.
    pub nr: u64,
}

impl System {
    pub fn empty() -> Self { Self::default() }

    // ====== max_var_idx_cache maintenance ======

    /// Invalidate the cached max-var-idx hint.  Call on any mutation
    /// that could LOWER the max (substitution applied to the system,
    /// eq-store simp, node removal, ...).  Cheap (single `Cell::set`).
    #[inline]
    pub fn invalidate_max_var_idx_cache(&self) {
        self.max_var_idx_cache.set(None);
    }

    /// Bump the cache for a newly-added LVar.  No-op if invalidated.
    #[inline]
    pub fn bump_cache_lvar(&self, v: &tamarin_term::lterm::LVar) {
        if let Some(cur) = self.max_var_idx_cache.get() {
            if v.idx > cur {
                self.max_var_idx_cache.set(Some(v.idx));
            }
        }
    }

    /// Bump the cache by walking a term.
    #[inline]
    pub fn bump_cache_term(&self, t: &tamarin_term::lterm::LNTerm) {
        if let Some(cur) = self.max_var_idx_cache.get() {
            let mut m = cur;
            crate::constraint::solver::reduction::bm_term_pub(t, &mut m);
            if m != cur { self.max_var_idx_cache.set(Some(m)); }
        }
    }

    /// Bump the cache by walking a fact's terms.
    #[inline]
    pub fn bump_cache_fact(&self, fa: &crate::fact::LNFact) {
        if let Some(cur) = self.max_var_idx_cache.get() {
            let mut m = cur;
            crate::constraint::solver::reduction::bm_fact_pub(fa, &mut m);
            if m != cur { self.max_var_idx_cache.set(Some(m)); }
        }
    }

    /// Bump the cache by walking a rule's free vars.
    #[inline]
    pub fn bump_cache_rule(&self, r: &crate::rule::RuleACInst) {
        if let Some(cur) = self.max_var_idx_cache.get() {
            let mut m = cur;
            crate::constraint::solver::reduction::bm_rule_pub(r, &mut m);
            if m != cur { self.max_var_idx_cache.set(Some(m)); }
        }
    }

    /// Bump the cache by walking a guarded formula.
    #[inline]
    pub fn bump_cache_guarded(&self, f: &Guarded) {
        if let Some(cur) = self.max_var_idx_cache.get() {
            let n = crate::guarded::max_var_idx(f);
            if n > cur { self.max_var_idx_cache.set(Some(n)); }
        }
    }

    /// Bump the cache by walking a goal.
    #[inline]
    pub fn bump_cache_goal(&self, g: &Goal) {
        if self.max_var_idx_cache.get().is_none() { return; }
        match g {
            Goal::Action(i, fa) => {
                self.bump_cache_lvar(i);
                self.bump_cache_fact(fa);
            }
            Goal::Premise(p, fa) => {
                self.bump_cache_lvar(&p.0);
                self.bump_cache_fact(fa);
            }
            Goal::Chain(c, p) => {
                self.bump_cache_lvar(&c.0);
                self.bump_cache_lvar(&p.0);
            }
            Goal::Subterm((s, t)) => {
                self.bump_cache_term(s);
                self.bump_cache_term(t);
            }
            Goal::Disj(_) | Goal::Split(_) => {}
        }
    }

    /// Add an open goal, no-op if already present (compared by `Goal`
    /// equality).
    pub fn add_goal(&mut self, g: Goal) {
        // HS `insertGoalStatus` (Reduction.hs:606-609): advance the
        // counter on EVERY call, even when the goal already exists.
        let age = self.next_goal_nr;
        self.next_goal_nr = self.next_goal_nr.wrapping_add(1);
        if !self.goals.iter().any(|(existing, _)| existing == &g) {
            let mut st = GoalStatus::default();
            st.nr = age;
            self.bump_cache_goal(&g);
            self.goals.push((g, st));
        }
    }

    /// `insertGoal` mirror with loop-breaker flag — direct port of
    /// Haskell's `insertGoal goal isLoopBreaker`. Marks the goal's
    /// `looping` field so the smart ranker can deprioritise it.
    ///
    /// Haskell uses `M.insertWith combineGoalStatus`:
    ///   combineGoalStatus (GoalStatus s1 a1 l1) (GoalStatus s2 a2 l2) =
    ///     GoalStatus (s1 || s2) (min a1 a2) (l1 || l2)
    /// — so re-inserting a goal that was previously marked `solved` keeps
    /// it solved.
    ///
    /// For Disj goals specifically, HS uses DeBruijn-bound vars so
    /// alpha-equivalent Disjs are STRUCTURALLY IDENTICAL — the Map
    /// key match triggers `combineGoalStatus` and the prior `solved=True`
    /// is preserved.  Rust represents bound vars as `VarSpec` with
    /// freshen-shifted idxs, so alpha-equivalent re-firings would
    /// otherwise produce DISTINCT goal keys → new goals with
    /// `solved=False` accumulate.
    ///
    /// Concrete trigger: NSLPK3 line-105.  The 4 typing-lemma Disjs
    /// at parent path are re-fired across many proof-tree positions.
    /// HS recognises them as the same goal each time (DeBruijn match)
    /// and keeps the prior solved=True.  Rust loses track and ends up
    /// with 1 spurious open Disj at `/.../I_2`, which smartRanking
    /// then picks → line-105 `case case_1` (Disj) where HS picks
    /// `case I_1` (next Action).
    ///
    /// Fix: for Disj goals, compare against existing goals via
    /// alpha-canonicalised form (`normalize_bound_lvars`).  Mirrors
    /// HS's DeBruijn-based structural equality.
    pub fn add_goal_with_loop_flag(&mut self, g: Goal, looping: bool) {
        // HS `insertGoalStatus` (Reduction.hs:606-609) reads
        // `sNextGoalNr` then `succ`s it on EVERY call, including when
        // the goal key already exists (where `insertWith
        // combineGoalStatus` keeps the existing — smaller — nr).
        let age = self.next_goal_nr;
        self.next_goal_nr = self.next_goal_nr.wrapping_add(1);
        let canon_g = canonical_goal_for_dedup(&g);
        let is_new = !self.goals.iter().any(|(existing, _)|
            canonical_goal_for_dedup(existing) == canon_g);
        if std::env::var("TAM_RS_TRACE_GOAL_INSERT").is_ok() {
            let kindstr = match &g {
                Goal::Action(i, fa) => format!("Action {:?} {:?}", i, fa),
                Goal::Premise(p, fa) => format!("Premise {:?} {:?}", p, fa),
                Goal::Chain(c, p) => format!("Chain {:?}->{:?}", c, p),
                Goal::Split(sid) => format!("Split {:?}", sid),
                Goal::Disj(_) => "Disj".to_string(),
                Goal::Subterm(_) => "Subterm".to_string(),
            };
            eprintln!("[RS_GOAL_INSERT] gsNr={} isNew={} kind={}",
                age, is_new, kindstr);
        }
        if let Some(slot) = self.goals.iter_mut().find(|(existing, _)|
            canonical_goal_for_dedup(existing) == canon_g)
        {
            slot.1.looping = slot.1.looping || looping;
            // combineGoalStatus keeps `min` of the two nrs; the
            // existing one is always smaller, so leave it unchanged.
            return;
        }
        let mut st = GoalStatus::default();
        st.looping = looping;
        st.nr = age;
        self.bump_cache_goal(&g);
        self.goals.push((g, st));
    }

    /// Insert a new node into the sequent. Replaces an existing entry
    /// for the same id.
    pub fn add_node(&mut self, id: NodeId, rule: RuleACInst) {
        // DIAGNOSTIC: panic if an instance rule with user-named idx-0 vars
        // gets added.  Gated by env var so it doesn't affect production.
        // Honors TAM_DBG_PANIC_IDX0_RUNTIME_ONLY=1 to skip during precompute.
        if std::env::var("TAM_DBG_PANIC_IDX0").is_ok() {
            let in_precompute = crate::constraint::solver::sources::in_precompute_mode();
            let skip_during_precompute = std::env::var("TAM_DBG_PANIC_IDX0_RUNTIME_ONLY").is_ok();
            let active = !(skip_during_precompute && in_precompute);
            if active {
                use tamarin_term::lterm::HasFrees;
                let mut found_idx0: Option<tamarin_term::lterm::LVar> = None;
                rule.for_each_free(&mut |v| {
                    if v.idx == 0 && matches!(v.name.as_str(),
                        "ni" | "nr" | "m1" | "m2" | "s" | "R" | "ltkA" | "ltkI")
                        && found_idx0.is_none() {
                        found_idx0 = Some(v.clone());
                    }
                });
                if let Some(v) = found_idx0 {
                    panic!("[TAM_DBG_PANIC_IDX0] add_node: rule has idx-0 var {:?} (id={:?}, precompute={})",
                        v, id, in_precompute);
                }
            }
        }
        // DIAGNOSTIC: dump Serv_1 rule contents at the moment of add_node.
        if std::env::var("TAM_DBG_ADD_NODE_SERV1").is_ok() {
            let nm = crate::constraint::solver::reduction::rule_case_name(&rule);
            if nm == "Serv_1" {
                eprintln!("[add_node_serv1] adding Serv_1 at {}.{}", id.name, id.idx);
                for (i, p) in rule.premises.iter().enumerate() {
                    eprintln!("[add_node_serv1]   prem[{}]: {:?}", i,
                        format!("{:?}", p).chars().take(400).collect::<String>());
                }
                for (i, c) in rule.conclusions.iter().enumerate() {
                    eprintln!("[add_node_serv1]   conc[{}]: {:?}", i,
                        format!("{:?}", c).chars().take(400).collect::<String>());
                }
                // Walk the stack via env vars if we want to know where this is called from.
            }
        }
        // DIAGNOSTIC: trace every node addition with its id+rule_name.
        // Captures both pre-saturation (precompute) and runtime grafts.
        if std::env::var("TAM_DBG_TRACE_ADD_NODE").is_ok() {
            let rule_name = crate::constraint::solver::reduction::rule_case_name(&rule);
            // Also dump prem[1] term if id is j:N (R_1/I_1 candidates).
            if id.name == "j" {
                let prem1 = rule.premises.get(1)
                    .and_then(|p| p.terms.first())
                    .map(|t| format!("{:?}", t).chars().take(120).collect::<String>())
                    .unwrap_or_default();
                let prem0 = rule.premises.get(0)
                    .and_then(|p| p.terms.first())
                    .map(|t| format!("{:?}", t).chars().take(80).collect::<String>())
                    .unwrap_or_default();
                eprintln!("[ADD_NODE_J] id={}:{} rule={} prem[0]={} prem[1]={}",
                    id.name, id.idx, rule_name, prem0, prem1);
            } else {
                eprintln!("[ADD_NODE] id={:?}:{} rule={}", id.name, id.idx, rule_name);
            }
        }
        // DIAGNOSTIC: TAM_DBG_PANIC_ANY_IDX0_NODE — panic on ANY node added
        // with id idx 0 (excluding the very first node, which is legitimate).
        // Used to find the source of the idx-0 leak.  Set
        // TAM_DBG_PANIC_ANY_IDX0_NODE=1 to enable.
        if std::env::var("TAM_DBG_PANIC_ANY_IDX0_NODE").is_ok() && id.idx == 0 {
            let rule_name = crate::constraint::solver::reduction::rule_case_name(&rule);
            panic!("[TAM_DBG_PANIC_ANY_IDX0_NODE] add_node at idx 0: id={:?} rule={}",
                id, rule_name);
        }
        let pos = self.nodes.iter().position(|(k, _)| k == &id);
        if let Some(i) = pos {
            self.invalidate_max_var_idx_cache();
            self.nodes[i].1 = rule;
        } else {
            self.bump_cache_lvar(&id);
            self.bump_cache_rule(&rule);
            self.nodes.push((id, rule));
        }
    }

    /// Add an edge if not already present.  Low-level raw insert
    /// equivalent of HS `modM sEdges (S.insert e)`.  Does NOT emit
    /// `[EXEC] insertEdges n=K` — that trace is bound to HS's
    /// `insertEdgesLabeled` (Reduction.hs:299-307), which is the only
    /// path that traces.  Callers that mirror `insertEdgesLabeled`
    /// must use `Reduction::insert_edge_labeled` (which emits the
    /// trace + runs `solveFactEqs`); callers that mirror HS's raw
    /// `modM sEdges` (e.g. `exploitPrem InFact` /
    /// `exploitPrem FreshFact`) should use this directly.
    pub fn add_edge(&mut self, e: Edge) {
        if !self.edges.contains(&e) {
            self.bump_cache_lvar(&e.src.0);
            self.bump_cache_lvar(&e.tgt.0);
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
        if !self.less_atoms.iter().any(|x| x == &l) {
            self.bump_cache_lvar(&l.smaller);
            self.bump_cache_lvar(&l.larger);
            self.less_atoms.push(l);
        }
    }

    /// `alwaysBefore i j`: True iff `i < j` in every model of the system.
    /// Mirrors Haskell's `Theory.Constraint.System.alwaysBefore`. Computed
    /// as transitive reachability over
    ///   `rawLessRel = sLessAtoms ++ rawEdgeRel`
    /// where
    ///   `rawEdgeRel = sEdges ++ unsolvedChains` (`System.hs:1613-1616`).
    /// **Unsolved chain goals contribute (c.0, p.0) to the less-relation
    /// too** — HS treats an open chain as an implicit edge for purposes
    /// of cycle detection and ordering inference. Without this, RS's
    /// `cyclic` and `has_forbidden_chain` miss contradictions HS catches
    /// (root cause of the StatVerif KU(pcs) over-saturation).
    pub fn always_before(&self, i: &NodeId, j: &NodeId) -> bool {
        if i == j { return false; }
        // Build adjacency from less atoms + edges + unsolved chains.
        let mut adj: std::collections::BTreeMap<NodeId, Vec<NodeId>>
            = std::collections::BTreeMap::new();
        for l in &self.less_atoms {
            adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
        }
        for e in &self.edges {
            adj.entry(e.src.0.clone()).or_default().push(e.tgt.0.clone());
        }
        // HS-faithful `unsolvedChains` contribution to rawEdgeRel
        // (`System.hs:1613-1616`).
        for (g, st) in &self.goals {
            if st.solved { continue; }
            if let crate::constraint::constraints::Goal::Chain(c, p) = g {
                adj.entry(c.0.clone()).or_default().push(p.0.clone());
            }
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
                if !self.lemmas.contains(&other) {
                    self.bump_cache_guarded(&other);
                    self.lemmas.push(other);
                }
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
    if std::env::var("TAM_DBG_FORMULA_TO_SYS").is_ok() {
        eprintln!("[formula_to_system] tq={:?} fm = {:?}", trace_quantifier, fm);
        eprintln!("[formula_to_system] tq={:?} gf1 = {:?}", trace_quantifier, gf1);
    }
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
        let l1 = crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&Atom::Last(mkvar("i"))));
        let l2 = crate::guarded::Guarded::Atom(crate::guarded::atom_to_gatom_free(&Atom::Last(mkvar("j"))));
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
