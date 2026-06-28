//! The `System` sequent — the solver's working state.
//!
//! Port of `Theory.Constraint.System.System` (from the 1936-line
//! `Theory/Constraint/System.hs`). The fields are live solver state:
//! the equation/subterm stores, source-kind/side annotations,
//! conflation-soundness flags and the goal/node/edge collections are
//! all read and mutated by the constraint solver during proof search.

use std::cell::Cell;
use std::sync::Arc;

use crate::constraint::constraints::{Edge, Goal, LessAtom, NodeId};
use crate::guarded::Guarded;
use crate::rule::RuleACInst;
use crate::tools::{EquationStore, SubtermStore};

// =============================================================================
// Prebuilt always-before adjacency
// =============================================================================

/// A prebuilt `alwaysBefore` adjacency map (`rawLessRel`), produced by
/// [`System::build_always_before_adj`] and queried by
/// [`System::always_before_with`]. Hoisting this build out of nested loops
/// turns the per-call O(less+edges+chains) map rebuild into a single build
/// per pass; the queries are pure BFS lookups. The relation is invariant
/// across the inner loops (the system is not mutated mid-pass), so the
/// hoisted result is identical to rebuilding the adjacency on every query.
#[derive(Debug, Clone, Default)]
pub struct PrebuiltAdj {
    adj: std::collections::BTreeMap<NodeId, Vec<NodeId>>,
}

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
/// Storage choices: we use `Vec` for most collections rather than
/// `BTreeSet`/`BTreeMap` because some underlying values
/// (`Goal`/`Guarded`/`RuleACInst`) don't yet derive `Ord`/`Hash`
/// (`Edge` already does). `nodes`/`goals` are `Arc<Vec<..>>` for
/// copy-on-write sharing (see field docs). Lookup is currently
/// linear; once the remaining derives land we can swap to ordered
/// containers without changing the public surface.
#[derive(Debug, Default)]
pub struct System {
    pub source_kind: Option<SourceKind>,
    pub side: Option<Side>,
    /// Node id → rule instance providing its conclusion.
    ///
    /// Wrapped in `Arc` for copy-on-write structural sharing: cloning a
    /// `System` (which happens at every proof branch / source-case fork)
    /// only bumps the refcount instead of deep-copying every
    /// `RuleACInst` (the biggest payload — many `LNFact`s / `LNTerm`s).
    /// Mutations go through `Arc::make_mut`, which clones the inner
    /// `Vec` only when the `Arc` is actually shared.  Reads via `Deref`
    /// are unchanged.  `Arc`'s `PartialEq` forwards to the inner `Vec`
    /// (content comparison, not pointer identity), so equality
    /// semantics — critical for goal/case dedup — are preserved.
    pub nodes: Arc<Vec<(NodeId, RuleACInst)>>,
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
    ///
    /// `Arc`-wrapped for copy-on-write structural sharing (see `nodes`).
    /// Cloned at every proof fork; mutated through `eq_store_mut`.
    pub eq_store: Arc<EquationStore>,
    /// Subterm store.
    ///
    /// `Arc`-wrapped for copy-on-write structural sharing (see `nodes`).
    /// Cloned at every proof fork; mutated through `subterm_store_mut`.
    pub subterm_store: Arc<SubtermStore>,
    /// Open goals paired with their current status.
    ///
    /// `Arc`-wrapped for copy-on-write structural sharing (see `nodes`).
    /// Cloned at every proof fork; mutated through `goals_mut`.
    pub goals: Arc<Vec<(Goal, GoalStatus)>>,
    /// Monotonic goal-number counter (`_sNextGoalNr`,
    /// System.hs:394).  Advanced on every goal insertion (even when
    /// the goal already exists — HS's `insertGoalStatus`
    /// Reduction.hs:516-521 always `succ`s it).  Each new goal records
    /// the current value as its `GoalStatus.nr`.
    pub next_goal_nr: u64,
    /// Source-case names already grafted into this branch.  Mirrors
    /// Haskell's `filterCases` invariant in `solveAllSafeGoals`: once
    /// a precomputed case has been used to discharge a goal, it is
    /// removed from the available source list for the remainder of
    /// the search branch.  Without this, a chain-saturated case whose
    /// internal KU goals re-spawn at runtime will pick the same case
    /// again, looping until depth-limit.
    pub used_sources: Vec<String>,
    /// Provenance tracking: universals in `lemmas` that
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
            used_sources: self.used_sources.clone(),
            sources_lemma_universals: self.sources_lemma_universals.clone(),
            max_var_idx_cache: Cell::new(self.max_var_idx_cache.get()),
        }
    }
}

// Manual `PartialEq` — ignores the cache.  Two systems with identical
// content but different cache state (e.g. one freshly cloned, one
// after `bounds_max` populated its cache) must compare equal — see
// `proof_method.rs`'s cleanup-equality check (`let cleaned_input =
// cleanup(sys); ... if cleaned[0] == cleaned_input { return None; }`).
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
            && self.used_sources == other.used_sources
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
    /// Whether the goal is currently "loop-marked".
    pub looping: bool,
    /// Whether the goal is already solved (kept for replay).
    pub solved: bool,
    /// Goal creation order (`_gsNr` in HS `GoalStatus`,
    /// System.hs:373).  Assigned from `System.next_goal_nr` at first
    /// insertion; on re-insertion of an existing goal HS keeps the
    /// `min` (so the original, smaller nr wins — see
    /// `combineGoalStatus`).  `goalNrRanking` (ProofMethod.hs:593-594
    /// `sortOn (fst . snd)`) orders goals by this number, NOT by Vec
    /// position.  This is the canonical tie-break within a heuristic
    /// priority class.
    pub nr: u64,
}

// --- Cached debug env flags for the goal insertion hot path -------
// `add_goal`/`add_goal_with_loop_flag` insert goals per KU-decomposition /
// conjoinSystem.  These diagnostic env vars are constant for the
// process, so cache each behind a `OnceLock<bool>` (mirroring
// `reduction::bounds_max_verify_enabled`) instead of an env-lock +
// `String` alloc per insertion.
#[inline]
fn dbg_insert_goal() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("TAM_RS_DBG_INSERT_GOAL").is_ok())
}
#[inline]
fn dbg_insert_goal_include_precompute() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("TAM_RS_DBG_INSERT_GOAL_INCLUDE_PRECOMPUTE").is_ok())
}
#[inline]
fn trace_goal_insert() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("TAM_RS_TRACE_GOAL_INSERT").is_ok())
}

impl System {
    pub fn empty() -> Self { Self::default() }

    /// The rule instance at node `v`, if present. Port of HS `nodeRuleSafe`
    /// (System.hs:917): `M.lookup v sNodes`.
    pub fn node_rule_safe(&self, v: &NodeId) -> Option<&RuleACInst> {
        self.nodes.iter().find(|(id, _)| id == v).map(|(_, r)| r)
    }

    /// All `In`- and protocol-premise terms in the system, as
    /// `(node, premise, term-index, term)`. Port of HS `allPrems`
    /// (System.hs:894).
    pub fn all_prems(&self) -> Vec<(NodeId, crate::rule::PremIdx, usize, tamarin_term::lterm::LNTerm)> {
        let mut out = Vec::new();
        for (i, ru) in self.nodes.iter() {
            for (j, fa) in ru.enumerate_premises() {
                if let Some(ms) = crate::fact::proto_or_in_fact_view(fa) {
                    for (k, m) in ms.into_iter().enumerate() {
                        out.push((i.clone(), j, k, m));
                    }
                }
            }
        }
        out
    }

    /// All unsolved destruction chains, as `(NodeConc, NodePrem)`. Port of HS
    /// `unsolvedChains` (System.hs:1601).
    pub fn unsolved_chains(&self) -> Vec<(crate::constraint::constraints::NodeConc, crate::constraint::constraints::NodePrem)> {
        use crate::constraint::constraints::Goal;
        let mut out = Vec::new();
        for (g, status) in self.goals.iter() {
            if status.solved { continue; }
            if let Goal::Chain(from, to) = g {
                out.push((from.clone(), to.clone()));
            }
        }
        out
    }

    /// All unsolved premise goals, as `(NodePrem, LNFact)`. Port of HS
    /// `unsolvedPremises` (System.hs:1505).
    pub fn unsolved_premises(&self) -> Vec<(crate::constraint::constraints::NodePrem, crate::fact::LNFact)> {
        use crate::constraint::constraints::Goal;
        let mut out = Vec::new();
        for (g, status) in self.goals.iter() {
            if status.solved { continue; }
            if let Goal::Premise(premidx, fa) = g {
                out.push((premidx.clone(), fa.clone()));
            }
        }
        out
    }

    /// Copy-on-write mutable access to `nodes`.  Clones the inner `Vec`
    /// only if the `Arc` is shared with another `System` (refcount > 1);
    /// otherwise hands out a `&mut` to the existing storage.  Use this
    /// for any in-place mutation of the node list.
    #[inline]
    pub fn nodes_mut(&mut self) -> &mut Vec<(NodeId, RuleACInst)> {
        Arc::make_mut(&mut self.nodes)
    }

    /// Copy-on-write mutable access to `goals` (see `nodes_mut`).
    #[inline]
    pub fn goals_mut(&mut self) -> &mut Vec<(Goal, GoalStatus)> {
        Arc::make_mut(&mut self.goals)
    }

    /// Copy-on-write mutable access to `eq_store` (see `nodes_mut`).
    #[inline]
    pub fn eq_store_mut(&mut self) -> &mut EquationStore {
        Arc::make_mut(&mut self.eq_store)
    }

    /// Copy-on-write mutable access to `subterm_store` (see `nodes_mut`).
    #[inline]
    pub fn subterm_store_mut(&mut self) -> &mut SubtermStore {
        Arc::make_mut(&mut self.subterm_store)
    }

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
        // HS has a single goal entry point: `insertGoal goal False`
        // (Reduction.hs:523-524). `add_goal` is exactly that — defer to
        // `add_goal_with_loop_flag` with `looping = false` so both
        // entry points share one counter-advance / dedup / push path.
        self.add_goal_with_loop_flag(g, false);
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
        // HS `insertGoalStatus` (Reduction.hs:516-521) reads
        // `sNextGoalNr` then `succ`s it on EVERY call, including when
        // the goal key already exists (where `insertWith
        // combineGoalStatus` keeps the existing — smaller — nr).
        let age = self.next_goal_nr;
        self.next_goal_nr = self.next_goal_nr.wrapping_add(1);
        if dbg_insert_goal() {
            let in_pre = crate::constraint::solver::sources::in_precompute_mode()
                || crate::constraint::solver::sources::in_initial_source_cases();
            let want_pre = dbg_insert_goal_include_precompute();
            if !in_pre || want_pre {
                let tag = if in_pre { "<precompute>" } else { "<proof>" };
                eprintln!("[RS_INS_GOAL] lemma={} gsNr={} solved=false loops={} goal={:?}", tag, age, looping, g);
            }
        }
        let canon_g = canonical_goal_for_dedup(&g);
        // Single dedup scan: locate the existing slot (if any) once and
        // derive `is_new` from it, instead of running the same O(n)
        // `canonical_goal_for_dedup` comparison twice (once for the
        // trace, once for the find) on the goal-insertion hot path.
        //
        // `canonical_goal_for_dedup` is identity (`g.clone()`) for every
        // non-Disj variant, so we only need to canonicalise an existing
        // entry when it is itself a `Disj` (and only then can it match a
        // `Disj` `canon_g`; under `Goal`'s derived `PartialEq` distinct
        // variants never compare equal). For the common non-Disj case
        // this compares `existing == &canon_g` directly, avoiding one
        // full `Goal` clone per existing goal per insertion.
        let slot_idx = self.goals.iter().position(|(existing, _)| {
            if matches!(existing, Goal::Disj(_)) {
                canonical_goal_for_dedup(existing) == canon_g
            } else {
                *existing == canon_g
            }
        });
        if trace_goal_insert() {
            let kindstr = match &g {
                Goal::Action(i, fa) => format!("Action {:?} {:?}", i, fa),
                Goal::Premise(p, fa) => format!("Premise {:?} {:?}", p, fa),
                Goal::Chain(c, p) => format!("Chain {:?}->{:?}", c, p),
                Goal::Split(sid) => format!("Split {:?}", sid),
                Goal::Disj(_) => "Disj".to_string(),
                Goal::Subterm(_) => "Subterm".to_string(),
            };
            eprintln!("[RS_GOAL_INSERT] gsNr={} isNew={} kind={}",
                age, slot_idx.is_none(), kindstr);
        }
        if let Some(idx) = slot_idx {
            let slot = &mut self.goals_mut()[idx];
            slot.1.looping = slot.1.looping || looping;
            // combineGoalStatus keeps `min` of the two nrs; the
            // existing one is always smaller, so leave it unchanged.
            return;
        }
        let st = GoalStatus { looping, nr: age, ..Default::default() };
        self.bump_cache_goal(&g);
        self.goals_mut().push((g, st));
    }

    /// Insert a new node into the sequent. Replaces an existing entry
    /// for the same id.
    pub fn add_node(&mut self, id: NodeId, rule: RuleACInst) {
        let pos = self.nodes.iter().position(|(k, _)| k == &id);
        if let Some(i) = pos {
            self.invalidate_max_var_idx_cache();
            self.nodes_mut()[i].1 = rule;
        } else {
            self.bump_cache_lvar(&id);
            self.bump_cache_rule(&rule);
            self.nodes_mut().push((id, rule));
        }
    }

    /// Add an edge if not already present.  Low-level raw insert
    /// equivalent of HS `modM sEdges (S.insert e)`.  Does NOT emit the
    /// Rust-only `[EXEC] insertEdges n=K` trace — that is added by
    /// `Reduction::insert_edge_labeled`, the Rust wrapper around HS's
    /// `insertEdges` (Reduction.hs:278-281, which runs `solveFactEqs`).
    /// Callers that mirror HS's `insertEdges` must use
    /// `Reduction::insert_edge_labeled` (emits the trace + runs
    /// `solveFactEqs`); callers that mirror HS's raw `modM sEdges`
    /// (e.g. `exploitPrem InFact` / `exploitPrem FreshFact`) should use
    /// this directly.
    pub fn add_edge(&mut self, e: Edge) {
        if !self.edges.contains(&e) {
            self.bump_cache_lvar(&e.src.0);
            self.bump_cache_lvar(&e.tgt.0);
            self.edges.push(e);
        }
    }

    /// Add a `<` atom if not already present (equality ignores reason).
    /// Self-loops (a < a) are degenerate — they produce immediate
    /// contradictions via the cyclic check.  In most cases such a
    /// self-loop arises from subst_system collapsing two distinct
    /// nodes to the same id AFTER a less-atom between them was already
    /// recorded; the resulting `a < a` is a true contradiction.  We
    /// still add it so the contradiction check catches it.
    pub fn add_less(&mut self, l: LessAtom) {
        if !self.less_atoms.iter().any(|x| x == &l) {
            self.bump_cache_lvar(&l.smaller);
            self.bump_cache_lvar(&l.larger);
            self.less_atoms.push(l);
        }
    }

    /// Build the `alwaysBefore` adjacency map (`rawLessRel`) underpinning
    /// `alwaysBefore i j` ("True iff `i < j` in every model of the
    /// system"), mirroring Haskell's `Theory.Constraint.System.alwaysBefore`.
    /// `alwaysBefore` is transitive reachability over
    ///   `rawLessRel = sLessAtoms ++ rawEdgeRel`
    /// where
    ///   `rawEdgeRel = sEdges ++ unsolvedChains` (`System.hs`).
    /// **Unsolved chain goals contribute (c.0, p.0) to the less-relation
    /// too** — HS treats an open chain as an implicit edge for purposes
    /// of cycle detection and ordering inference. Without this, RS's
    /// `cyclic` and `has_forbidden_chain` miss contradictions HS catches
    /// (root cause of the StatVerif KU(pcs) over-saturation).
    ///
    /// Hoist this build out of loops via [`always_before_with`] so the
    /// relation is built once per pass and queried many times. The
    /// relation depends only on `&self`, never on the `i`/`j` query
    /// arguments.
    pub fn build_always_before_adj(&self) -> PrebuiltAdj {
        let mut adj: std::collections::BTreeMap<NodeId, Vec<NodeId>>
            = std::collections::BTreeMap::new();
        for l in &self.less_atoms {
            adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
        }
        for e in &self.edges {
            adj.entry(e.src.0.clone()).or_default().push(e.tgt.0.clone());
        }
        // HS-faithful `unsolvedChains` contribution to rawEdgeRel
        // (`System.hs`).
        for (g, st) in self.goals.iter() {
            if st.solved { continue; }
            if let crate::constraint::constraints::Goal::Chain(c, p) = g {
                adj.entry(c.0.clone()).or_default().push(p.0.clone());
            }
        }
        PrebuiltAdj { adj }
    }

    /// `alwaysBefore i j` against a prebuilt adjacency map (see
    /// [`build_always_before_adj`](Self::build_always_before_adj)). The BFS
    /// reachability over `rawLessRel` is the `alwaysBefore` query itself;
    /// hoisting the adjacency build out is a pure refactor.
    pub fn always_before_with(&self, adj: &PrebuiltAdj, i: &NodeId, j: &NodeId) -> bool {
        // DELIBERATE deviation from HS `alwaysBefore`: HS's
        // `reachableSet [i] lessRel` seeds the visited set with `i`
        // itself (Data/DAG/Simple.hs:76-79), so `alwaysBefore sys i i`
        // is `True`.  We short-circuit `i == j` to `false`.  This is
        // caller-safe: every live caller already filters equal nodes
        // before reaching here (Less/EqE simplify guards, the
        // `simpInjectiveFactEq` `i /= j` filter, contradictions.rs's
        // `id == c.0` skip), exactly as HS does, so the `i == i => true`
        // result is never observable in either codebase.
        if i == j { return false; }
        let adj = &adj.adj;
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
    // HS stores `_sDiffSystem = isdiff` on its `System` record
    // (System.hs:821-824/396).  The Rust `System` has no such field —
    // `side` encodes LHS/RHS, not diff — so diff-mode is carried on
    // `ProofContext.is_diff` (context.rs:54) instead.  Nothing about
    // `is_diff` is recorded on the System here.
    let _ = is_diff;

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
