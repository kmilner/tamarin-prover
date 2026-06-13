//! Solver context — port of the `ProofContext` data type from
//! `Theory.Constraint.System`.
//!
//! The Haskell `ProofContext` is a fat record carrying every piece of
//! per-theory information the solver needs:
//!
//! - The underlying signature (with Maude handle).
//! - The protocol rules and their AC variants.
//! - Sources / case-distinctions used to bias goal solving.
//! - Heuristic / tactic configuration.
//! - Whether to use induction, whether diff mode is on, etc.
//!
//! For the Rust port we expose a minimal subset: just the `MaudeHandle`
//! and the rules. As more solver components land we'll grow the
//! context to match.

use tamarin_term::maude_proc::{MaudeHandle, MaudePool};

use crate::rule::IntrRuleAC;
use crate::theory::OpenProtoRule;

/// Minimum-viable context for the solver loop.
#[derive(Debug)]
pub struct ProofContext {
    pub maude: MaudeHandle,
    /// Optional pool of additional Maude subprocesses used at rayon
    /// parallel sites (rule-variant closure, saturate refinement) to
    /// avoid serialising every worker on the single `maude`'s internal
    /// IPC mutex.  `None` means "use the single `maude` only" (the
    /// original behaviour; byte-identical to `--processors=1`).
    ///
    /// HS uses a single Maude per ClosedTheory; this pool is a
    /// Rust-specific implementation improvement that doesn't change
    /// semantics — workers acquire a pool member at task start and
    /// reads/writes its own subprocess for the task's duration.  Each
    /// pool member's `with_fresh_counter_from(avoid_max)` still gives
    /// HS-faithful per-call witness allocation.
    pub maude_pool: Option<std::sync::Arc<MaudePool>>,
    /// All protocol rules in scope, including their AC variants.
    pub rules: Vec<OpenProtoRule>,
    /// Special intruder rules — `Coerce`, `PubConstr`, `FreshConstr`,
    /// `ISend`, `IRecv` (and `IEquality` in diff mode). These let the
    /// solver discharge `KU(_)` / `KD(_)` goals that arise from
    /// `In(_)`-fact reasoning.
    pub intruder_rules: Vec<IntrRuleAC>,
    /// Precomputed unique sources — for each fact tag with exactly
    /// one producing rule, we cache the producer name. Lets goal
    /// solving short-circuit candidate enumeration.
    pub unique_sources: Vec<crate::constraint::solver::sources::UniqueSource>,
    /// Whether the solver should attempt induction at the start of a
    /// proof. Mirrors Haskell's `pcUseInduction` flag.
    pub use_induction: UseInduction,
    /// Whether this is a diff-mode proof.
    pub is_diff: bool,
    /// Set of fact tags whose instances we know to be uniquely
    /// identified by their first argument (the "injective" facts).
    /// Mirrors Haskell's `pcInjectiveFactInsts`.
    pub injective_fact_insts: Vec<(crate::fact::FactTag,
        Vec<crate::tools::injective_fact_instances::MonotonicBehaviour>)>,
    /// Precomputed source-case enumerations.  For each non-special
    /// protocol-fact tag, holds the disjunction of derivation cases
    /// computed once at theory-load time.  `solve_premise_goal`
    /// consults this cache before enumerating rules — finite, fixed
    /// cases let the search graft a precomputed subsystem rather than
    /// re-deriving it (and recursing through copy-rules ad infinitum).
    pub full_sources: Vec<crate::constraint::solver::sources::Source>,
    /// Set when the current proof is for an exists-trace lemma.
    /// Used by `is_finished` to decide whether the Fresh-conflation
    /// case-drop should convert Contradictory→Unfinishable: for
    /// exists-trace lemmas the dropped case might have been the
    /// witness path (sound only via Unfinishable); for all-traces
    /// lemmas the drop is harmless (no witness to lose).  Defaults
    /// to false; set by `prove_lemma` based on the lemma's
    /// trace-quantifier attribute.
    pub is_exists_trace: bool,
    /// Theory-level restrictions (safety formulas), in guarded form.
    /// Mirrors Haskell's `pcRestrictions` — passed to `initialSource`
    /// so each precomputed source-case starts from a system with the
    /// restrictions installed as `sLemmas`.  Without this, restrictions
    /// like `True_is_true` never fire during precompute saturation,
    /// leaving spurious cases (e.g. Responder for `KU(senc)` in
    /// Pattern_matching::Responder_secrecy) that Haskell would have
    /// dropped via the restriction's implied-formula propagation.
    pub restrictions: Vec<crate::guarded::Guarded>,
    /// Pending typing assumptions (from `[sources]`-tagged lemmas)
    /// applied during `ensure_saturated`'s refinement step.  Set by
    /// `prove_lemma` before any source-case access; refinement is
    /// deferred to keep `ensure_saturated`'s trace emissions
    /// interleaved with the lemma proof's first source-case access
    /// (HS-faithful: `refineWithSourceAsms` operates on lazy `Source`
    /// thunks; its work only fires when a downstream consumer forces
    /// a `cdCases` thunk).
    pub typing_assumptions: Vec<crate::guarded::Guarded>,
    /// `pcTrueSubterm` — True iff every destructor rule has its
    /// RHS as a proper subterm of its LHS (`all isSubtermRule $
    /// filter isDestrRule $ intruder_rules`).  Mirrors Haskell's
    /// `_pcTrueSubterm` (System.hs:763) and gates the
    /// `has_impossible_chain` analysis: when True, only the chain-end
    /// root symbol is checked against the chain-start's possible
    /// decomposition root syms (a STRICTER test that fires more often);
    /// when False, all possible subterm syms of the chain-end are
    /// checked for intersection (a more LENIENT test).
    pub pc_true_subterm: bool,
    /// The goal ranking list for this lemma, mirroring HS's
    /// `Heuristic ProofContext = Heuristic [GoalRanking ProofContext]`
    /// (System.hs:527).  `None` ⇒ HS's `defaultHeuristic False`
    /// (`[SmartRanking False]`).  Resolved per-lemma in `prove_lemma`
    /// (per-lemma `[heuristic=..]` overrides the theory-level directive,
    /// matching `apDefaultHeuristic <|> pcHeuristic`).
    /// Round-robin scheduling: depth d → `rankings[d % n]`
    /// (ProofMethod.hs:802-811).
    pub heuristic: Option<Vec<crate::constraint::solver::goals::GoalRanking>>,
    /// The name of the lemma being proved.  Passed as `argv[1]` to
    /// the oracle script (HS `L.get pcLemmaName ctxt`, ProofMethod.hs:829).
    pub lemma_name: String,
    /// Path to the theory file being proved.  Used to resolve the
    /// oracle script path as `takeDirectory theory_file </> oracle_rel_path`
    /// (HS Parser.hs:304, System.hs:574-575).  Stored as the absolute
    /// path passed to `--prove`.
    pub theory_file: String,
    /// `saturate_state` — gates the lazy `ensure_saturated()` call.
    /// HS's `saturateSources` is lazy in `cdCases`: it only emits
    /// `[EXEC] solveGoal / exploitPrems / ...` traces when a consumer
    /// pattern-matches on a source's `cdCases` (forcing the thunk).
    /// To match, we defer the saturate run from `ProofContext::new`
    /// to the first `Source::cases(ctx)` call.  Sets to `Done` once
    /// run; subsequent calls no-op.
    pub(crate) saturate_state: std::sync::Mutex<SaturateState>,
    /// Cached saturation limit (from `IntegerParameters::default()`).
    pub(crate) saturation_limit: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SaturateState { Pending, InProgress, Done }

impl Clone for ProofContext {
    fn clone(&self) -> Self {
        let state = *self.saturate_state.lock().unwrap();
        ProofContext {
            maude: self.maude.clone(),
            maude_pool: self.maude_pool.clone(),
            rules: self.rules.clone(),
            intruder_rules: self.intruder_rules.clone(),
            unique_sources: self.unique_sources.clone(),
            use_induction: self.use_induction,
            is_diff: self.is_diff,
            injective_fact_insts: self.injective_fact_insts.clone(),
            full_sources: self.full_sources.clone(),
            is_exists_trace: self.is_exists_trace,
            restrictions: self.restrictions.clone(),
            typing_assumptions: self.typing_assumptions.clone(),
            pc_true_subterm: self.pc_true_subterm,
            heuristic: self.heuristic.clone(),
            lemma_name: self.lemma_name.clone(),
            theory_file: self.theory_file.clone(),
            saturate_state: std::sync::Mutex::new(state),
            saturation_limit: self.saturation_limit,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseInduction { UseInduction, AvoidInduction }

impl ProofContext {
    pub fn new(maude: MaudeHandle, rules: Vec<OpenProtoRule>) -> Self {
        Self::new_with_restrictions(maude, rules, Vec::new())
    }

    /// Cheap-ish clone with `maude` replaced.  Used at the rayon
    /// parallel sites where each worker wants its own subprocess
    /// (acquired from `maude_pool`) for the duration of one task,
    /// so workers don't serialise on a single Maude's IPC mutex.
    ///
    /// Most fields are `Arc`-of-Vec-friendly already (`MaudeHandle`,
    /// `Source`'s lazy cell, etc.), so the deep clone is cheap in
    /// practice; the heavy `Vec`s (rules, full_sources) are O(n) but
    /// only happen once per parallel task, not once per Maude call.
    ///
    /// The new context drops `maude_pool` (set to None) — a worker
    /// holding a pooled handle should NOT recursively borrow more
    /// pool members from inside the same task; doing so could
    /// deadlock if the pool is smaller than the rayon worker count.
    pub fn with_swapped_maude(&self, maude: MaudeHandle) -> Self {
        let mut c = self.clone();
        c.maude = maude;
        c.maude_pool = None;
        c
    }

    /// HS-faithful lazy `saturateSources` (Sources.hs:373).  Runs at
    /// most once per `ProofContext`: forces `initial_source_cases`
    /// for each source in `full_sources`, then iterates
    /// `saturate_sources_with_chain_fold` to convergence.  Subsequent
    /// calls no-op via the `saturate_state` flag.
    ///
    /// Triggered by `Source::cases(ctx)` on first force.  Trivial
    /// protocols whose lemma proofs never pattern-match on source
    /// cases (e.g. Var-headed `KU(t:Fresh)` source on an existence
    /// lemma) never call this, so zero saturate-time `[EXEC]` lines
    /// fire — matching HS's lazy-thunk behaviour.
    pub fn ensure_saturated(&self) {
        {
            let mut state = self.saturate_state.lock().unwrap();
            match *state {
                SaturateState::Done => return,
                SaturateState::InProgress => {
                    // Re-entrant call from inside saturate's own
                    // source-case grafting.  Return without re-running
                    // — the caller sees the partially-populated cells,
                    // matching HS's lazy fix-point semantics where
                    // iteration N forces iteration N-1's cached value.
                    return;
                }
                SaturateState::Pending => {
                    *state = SaturateState::InProgress;
                }
            }
        }
        // Pre-populate every source's cell with `Some(vec![])` BEFORE
        // running `initial_source_cases` on any of them.  This breaks
        // the recursion: when `initial_source_cases` for source A
        // calls `solve_with_source_cases_action` against source B
        // (forcing B.cases() recursively), B's cell is already
        // `Some(empty)`, so the recursive call returns empty rather
        // than re-entering `initial_source_cases` for B.  After this
        // pass we run the second pass that fills each cell with the
        // actual unsaturated `initialSource` cases — HS's `mapM`
        // over the lazy list under the iterative fix-point.
        for src in &self.full_sources {
            if src.cases_cell.lock().unwrap().is_none() {
                src.cases_set(Vec::new());
            }
        }
        for src in &self.full_sources {
            let init = crate::constraint::solver::sources::initial_source_cases_pub(
                &src.goal, self);
            src.cases_set(init);
        }
        // HS-faithful `saturate_sources_with_simp` (mirrors HS's
        // `saturateSources` driven by `solveAllSafeGoals` as the
        // proofStep).  Trace work-count closes from ~10-60× off
        // (with the chain-fold shortcut) to ~3-10× off.
        //
        // The chain-fold path (`saturate_sources_with_chain_fold`)
        // collapses HS's per-step `insertEdges`/`solveTermEqs`/
        // `exploitPrems` work into a single graft operation,
        // producing the same final case set with far fewer trace
        // events — efficient but not HS-faithful.  We use simp here
        // and investigate the resulting verdict regressions
        // (currently 7 exists-trace lemmas where Rust falsifies and
        // HS verifies) as separate missing-HS-behaviour bugs rather
        // than reverting to the trace-divergent chain-fold path.
        let raw: Vec<crate::constraint::solver::sources::Source> =
            self.full_sources.iter().cloned().collect();
        let saturated = crate::constraint::solver::sources::saturate_sources_with_simp_public(
            raw, self.saturation_limit, self);
        // HS-faithful: apply `refineWithSourceAsms` AFTER saturate.
        // HS does this lazily — `refineWithSourceAsms` produces
        // updated `Source` thunks that only fire their inner saturate
        // when forced.  We approximate by running both inside
        // `ensure_saturated` (which itself is lazy at the first
        // `cases(ctx)` call), so the refinement traces still
        // interleave with the lemma proof's first source-case access
        // rather than firing during `prove_lemma` setup.
        let refined = if self.typing_assumptions.is_empty() {
            saturated
        } else {
            crate::constraint::solver::sources::refine_with_source_asms(
                saturated, &self.typing_assumptions, self)
        };
        // Match saturated sources back to originals BY GOAL.  Saturate
        // may drop sources whose cases all `mzero` during `refineSource`
        // (HS's `runReduction proofStep ctxt se fs` returns Disj.empty),
        // so the saturated list can be SHORTER than `full_sources`.  A
        // positional `zip` here was a bug: it wrote saturated[0] (e.g.
        // KU(t:Fresh)'s cases) onto full_sources[0] (Premise(A)),
        // corrupting unrelated sources.  HS keeps `cdGoal` stable across
        // saturate iters (only `cdCases` changes), so `cdGoal` is the
        // join key.
        for orig in &self.full_sources {
            let sat = refined.iter().find(|s| s.goal == orig.goal);
            match sat {
                Some(s) => orig.cases_set(s.cases_or_empty()),
                // No matching saturated source — saturate dropped it
                // entirely (all branches contradicted).  HS's
                // `saturateSources` would leave the source with the
                // initial cases in this case (its `solver` returns
                // `(False, [])` on every iter, so `cdCases` stays
                // unchanged from `initialSource`'s output).  Mirror by
                // leaving the cell as-set by `initial_source_cases`
                // earlier in `ensure_saturated` — no overwrite.
                None => {}
            }
        }
        if std::env::var("TAM_DBG_SAT_FINAL").is_ok() {
            use crate::constraint::constraints::Goal;
            for src in &self.full_sources {
                let tag = match &src.goal {
                    Goal::Premise(_, f) => format!("Premise({:?})", f.tag),
                    Goal::Action(_, f) => {
                        let head = f.terms.first().map(|t| match t {
                            tamarin_term::term::Term::App(n, args) =>
                                format!("App({:?},{})", n, args.len()),
                            tamarin_term::term::Term::Lit(_) => "Lit".to_string(),
                        }).unwrap_or_else(|| "no_terms".to_string());
                        format!("Action({:?},{})", f.tag, head)
                    }
                    _ => continue,
                };
                for (name, sys) in src.cases_or_empty() {
                    eprintln!("[SAT_FINAL] src={} case={} nodes={:?} edges={} goals_solved={} goals_open={}",
                        tag, name,
                        sys.nodes.iter().map(|(id, r)|
                            format!("{:?}={}", id,
                                crate::constraint::solver::reduction::rule_case_name(r)))
                            .collect::<Vec<_>>(),
                        sys.edges.len(),
                        sys.goals.iter().filter(|(_, st)| st.solved).count(),
                        sys.goals.iter().filter(|(_, st)| !st.solved).count());
                    for e in &sys.edges {
                        eprintln!("[SAT_FINAL]   edge {:?}.{:?} → {:?}.{:?}",
                            e.src.0, e.src.1, e.tgt.0, e.tgt.1);
                    }
                    for (g, st) in sys.goals.iter() {
                        eprintln!("[SAT_FINAL]   goal solved={} {:?}",
                            st.solved, format!("{:?}", g).chars().take(120).collect::<String>());
                    }
                }
            }
        }
        *self.saturate_state.lock().unwrap() = SaturateState::Done;
    }

    /// Variant that accepts the theory-level restrictions.  Mirrors
    /// Haskell's `precomputeSources parameters ctxt restrictions`
    /// which threads restrictions into each `initialSource`'s system
    /// via `insertLemmas`.  Restrictions then fire on rule actions
    /// during saturate, dropping cases that violate them — e.g.
    /// `True_is_true` on Responder's `IsTrue(z)` action drops the
    /// Responder case for `KU(senc(...))` in Pattern_matching.
    pub fn new_with_restrictions(
        maude: MaudeHandle,
        rules: Vec<OpenProtoRule>,
        restrictions: Vec<crate::guarded::Guarded>,
    ) -> Self {
        Self::new_with_restrictions_and_pool(maude, None, rules, restrictions)
    }

    /// Like [`new_with_restrictions`] but also installs a
    /// `MaudePool` on the constructed context so the precompute /
    /// saturate phase (which happens INSIDE this constructor via
    /// `precompute_full_sources`) can dispatch work across the pool
    /// rather than serialising on the single shared Maude.
    ///
    /// Callers without a pool should keep calling
    /// `new_with_restrictions` — the precompute will use the single
    /// `maude` for every parallel task, which is correct (just
    /// contended).
    pub fn new_with_restrictions_and_pool(
        maude: MaudeHandle,
        maude_pool: Option<std::sync::Arc<MaudePool>>,
        mut rules: Vec<OpenProtoRule>,
        restrictions: Vec<crate::guarded::Guarded>,
    ) -> Self {
        // Inherit the maude signature from the handle so we can
        // synthesise per-symbol construction rules.
        let sig = maude.maude_sig();
        // Order: subterm rules FIRST, then special rules.  Mirrors
        // Haskell's `addMessageDeductionRuleVariants` (TheoryLoader.hs:784-789):
        //     rules = subtermIntruderRules False msig
        //          ++ specialIntruderRules False
        //          ++ ...
        // The ORDER MATTERS for solveAction's `disjunctionOfList rules` —
        // a `KU(aenc(t1,t2))` goal is matched against c_aenc BEFORE
        // coerce, producing cdCases = [c_aenc, coerce] instead of
        // [coerce, c_aenc].  This downstream determines which case
        // applies first in the proof renderer (e.g. NSPK3 injective_agree
        // picks `case c_aenc` like Haskell does).
        let mut intruder_rules = crate::intruder_rules::subterm_intruder_rules(false, &sig);
        // HS-faithful: run `closeIntrRule` over EACH intr rule BEFORE
        // `special_intruder_rules` are appended.  Mirrors Haskell
        // `Rule.closeRuleCache` (lib/theory/src/Rule.hs:160):
        //     intrRulesAC = concat $ map (closeIntrRule hnd) intrRules
        //
        // `closeIntrRule` does two things:
        //   (a) For `DestrRule subterm=True` it computes the per-rule
        //       `paciRemainingApplications` budget (number of consecutive
        //       chain applications) — previously every RS destructor had
        //       budget `-1`.
        //   (b) For `DestrRule subterm=False` (convergent-equation
        //       destructors like `d_0_comb` in issue216) it invokes
        //       `variantsIntruder` to enumerate Maude variants and add
        //       them to the pool.  Without this, the chain pool for
        //       issue216 has `nRules=6` instead of HS's `nRules=9`, and
        //       all 4 issue216 lemmas fail to close.
        //
        // Per HS, `closeIntrRule` runs AFTER `minimizeIntruderRules`
        // (already done inside `subterm_intruder_rules`) and BEFORE the
        // `special_intruder_rules` append (since HS appends specials
        // separately in `addMessageDeductionRuleVariants`).
        let dbg_close = std::env::var("TAM_RS_DBG_CLOSE_INTR").is_ok();
        if dbg_close {
            eprintln!("[close_intr] BEFORE: {} intr rules", intruder_rules.len());
            for r in &intruder_rules {
                if let crate::rule::IntrRuleACInfo::DestrRule(n, b, st, c) = &r.info {
                    eprintln!("  destr: {} budget={} subterm={} const={}",
                        String::from_utf8_lossy(n), b, st, c);
                }
            }
        }
        intruder_rules = intruder_rules.into_iter()
            .flat_map(|ir| crate::intruder_rules::close_intr_rule(&maude, &ir))
            .collect();
        if dbg_close {
            eprintln!("[close_intr] AFTER: {} intr rules", intruder_rules.len());
            for r in &intruder_rules {
                if let crate::rule::IntrRuleACInfo::DestrRule(n, b, st, c) = &r.info {
                    use tamarin_term::pretty::pretty_lnterm;
                    let prems_s: Vec<String> = r.premises.iter().flat_map(|f|
                        f.terms.iter().map(|t| pretty_lnterm(t))
                    ).collect();
                    let concs_s: Vec<String> = r.conclusions.iter().flat_map(|f|
                        f.terms.iter().map(|t| pretty_lnterm(t))
                    ).collect();
                    eprintln!("  destr: {} b={} st={} const={}\n    prems={:?}\n    concs={:?}",
                        String::from_utf8_lossy(n), b, st, c, prems_s, concs_s);
                }
            }
        }
        intruder_rules.extend(crate::intruder_rules::special_intruder_rules(false));
        // HS-faithful: theory-specific intruder rules (Nat, MSet, Xor) —
        // port of `Main.TheoryLoader.addMessageDeductionRuleVariants`
        // (src/Main/TheoryLoader.hs:786-789):
        //
        // ```haskell
        // rules =
        //   subtermIntruderRules False msig
        //   ++ specialIntruderRules False
        //   ++ (if enableNat  msig then natIntruderRules     else [])
        //   ++ (if enableMSet msig then multisetIntruderRules else [])
        //   ++ (if enableXor  msig then xorIntruderRules     else [])
        // ```
        //
        // For multiset: adds `_union` destructor (`KD(x++y) → KD(x)`,
        // subterm=True, budget=0) and `_union` constructor.  Without these,
        // the precomputed `KU(t)` source-cases miss the chain-extension
        // path through union-decomposition, causing `hasImpossibleChain`
        // to fire on legitimate chains from `KD(t1++t2)` to `KD(t1)`.
        // Root cause of the `minimal_multiset::Reachable`/`issue519` cluster.
        if sig.enable_mset {
            intruder_rules.extend(crate::intruder_rules::multiset_intruder_rules());
        }
        // XOR intruder rules — port of HS `xorIntruderRules`
        // (IntruderRules.hs:345-349) wired in `addMessageDeduction
        // RuleVariants` (TheoryLoader.hs:790).  Two destructor rules
        // for XOR cancellation (KD(x⊕y) ∧ KU(y⊕z) → KD(x⊕z) and
        // KD(x⊕y) ∧ KU(y) → KD(x)), one constructor (KU(x⊕y) from
        // KU(x), KU(y)), plus the `zero` constructor.  Without
        // these every XOR-using theory was unsound: the canonical
        // adversary attack `(x⊕y) ⊕ y = x` was unreachable, so
        // `xor.spthy::Secret` and all `recentalive_tag`-style lemmas
        // wrongly verified.  Mirrors HS's enableXor branch.
        if sig.enable_xor {
            intruder_rules.extend(crate::intruder_rules::xor_intruder_rules());
        }
        // DH / BP intruder variants — port of HS
        // `Main.TheoryLoader.addMessageDeductionRuleVariants`
        // (src/Main/TheoryLoader.hs:776-791):
        //
        // ```haskell
        // addMessageDeductionRuleVariants thy0
        //   | enableBP msig = addIntruderVariants
        //                       [mkDhIntruderVariants, mkBpIntruderVariants]
        //   | enableDH msig = addIntruderVariants [mkDhIntruderVariants]
        //   | otherwise     = thy
        // ```
        //
        // HS's `mkDhIntruderVariants` (TheoryLoader.hs:766-769)
        // parses the PRE-COMPUTED `data/intruder_variants_dh.spthy`
        // (Template-Haskell `embedFile`), not the runtime
        // `dhIntruderRules` generator.  HS's `Main.Mode.Intruder.run`
        // is what PRODUCES that cache file in the first place
        // (Main/Mode/Intruder.hs:48), but the production theory-load
        // path always reads the cache.
        //
        // Switching from the runtime generator (previous commit
        // `2f715f4e`) to the cached-file parser
        // (`mk_dh_intruder_variants` / `mk_bp_intruder_variants` from
        // `crate::intruder_variants`) makes us mechanism-identical to
        // HS.  The runtime generator (`dh_intruder_rules`) is retained
        // as the regenerator (callable when one wants to refresh the
        // cache from local Maude); a bridge test in
        // `intruder_variants.rs` flags any divergence.
        //
        // Ordering matches HS exactly: DH BEFORE BP, both AFTER
        // subterm + special rules.  When BP is enabled HS adds DH
        // FIRST (the list `[mkDhIntruderVariants, mkBpIntruderVariants]`
        // — TheoryLoader.hs:777).
        if sig.enable_bp {
            intruder_rules.extend(
                crate::intruder_variants::mk_dh_intruder_variants(&sig)
            );
            intruder_rules.extend(
                crate::intruder_variants::mk_bp_intruder_variants(&sig)
            );
        } else if sig.enable_dh {
            intruder_rules.extend(
                crate::intruder_variants::mk_dh_intruder_variants(&sig)
            );
        }
        // Detect injective fact instances ahead of time — mirrors
        // Haskell's `pcInjectiveFactInsts` precomputation.
        let proto_rules: Vec<crate::rule::ProtoRuleE> = rules.iter()
            .map(|r| r.rule.clone())
            .collect();
        let injective_fact_insts =
            crate::tools::injective_fact_instances::simple_injective_fact_instances(
                &proto_rules, &sig.reducible_fun_syms);
        // Compute loop-breakers and annotate the protocol rules in
        // place — direct port of Haskell's `useAutoLoopBreakersAC`
        // (`Theory.Tools.LoopBreakers`).  Edge `R_from → R_to.prem`
        // exists iff some conclusion of `R_from` is Maude AC-unifiable
        // with `R_to.prem`.  Loop-breaker analysis runs on
        // `(rule_name, prem_idx)` pairs.
        annotate_loop_breakers(&mut rules, &maude);
        // Compute rule variants — direct port of Haskell's
        // `variantsProtoRule` over every protocol rule.  For rules
        // containing reducible (destructor) sub-terms, Maude produces
        // multiple narrowing variants; we pre-apply each variant's
        // substitution to the rule's facts so the solver can enumerate
        // destructor-narrowed instances without further Maude calls.
        //
        // Without this, chain-fold for `KU(t:Fresh)` over a rule like
        // `Responder: ... --[ ]-> [Out(snd(sdec(msg, key)))]` cannot
        // find the narrowed instance `msg → senc(pair(_, t), key)`
        // ⇒ `Out(t)`, leaving exists-trace lemmas that need this path
        // unprovable (e.g. T&D::Public_part_public).
        let dbg_variants = std::env::var("TAM_DBG_VARIANTS").is_ok();
        // Pre-filter rules that can't have non-trivial variants: only
        // rules containing a *reducible* (destructor) function symbol
        // in some fact term could narrow. Skipping non-destructor
        // rules avoids ~N Maude round-trips at theory-load time.
        let reducible_syms: std::collections::BTreeSet<_> =
            sig.reducible_fun_syms.iter().cloned().collect();
        let term_has_reducible = |t: &tamarin_term::lterm::LNTerm| -> bool {
            fn rec(
                t: &tamarin_term::lterm::LNTerm,
                rs: &std::collections::BTreeSet<tamarin_term::function_symbols::FunSym>,
            ) -> bool {
                use tamarin_term::term::Term;
                match t {
                    Term::Lit(_) => false,
                    Term::App(f, args) => {
                        rs.contains(f) || args.iter().any(|a| rec(a, rs))
                    }
                }
            }
            rec(t, &reducible_syms)
        };
        // Rules with destructors anywhere — conclusions, premises,
        // ACTIONS, or new_vars — benefit from rule-variant plumbing.
        // Haskell's `variantsProtoRule` abstracts every reducible-
        // headed subterm in `prems ++ concs ++ acts ++ nvs` into a
        // fresh `z` var and computes the disjunction of
        // substitutions Maude returns from its variant narrowing
        // (RuleVariants.hs:93-99).
        //
        // The conclusions-only filter we had here used to be enough
        // because chain-fold was the only path that needed
        // destructor-narrowed alternatives.  But rules like
        // `--[ Equality(verify(sig, ...), true) ]->` (issue193,
        // TLS_Handshake) have reducible terms in their ACTIONS:
        // without variant expansion, the equality restriction
        // `All x y. Equality(x,y) ⇒ x=y` instantiates to
        // `Eq(verify(sig:Msg, ...), true)` which Maude
        // `unify in MSG` (AC-only, no [variant] eqs) reports as
        // unifiable-free → `eq_store.is_false` → false contradiction.
        // With variants, the action is abstracted to
        // `Equality(z, true)` and the variant subst {z → true,
        // sig → revealSign(...)} provides the closing witness case.
        let rule_has_reducible = |r: &crate::rule::ProtoRuleE| -> bool {
            r.conclusions.iter()
                .chain(r.premises.iter())
                .chain(r.actions.iter())
                .any(|f| f.terms.iter().any(|t| term_has_reducible(t)))
                || r.new_vars.iter().any(|t| term_has_reducible(t))
        };
        // Rule-variant plumbing: enabled by default to match Haskell's
        // `variantsProtoRule` behaviour. Broadens search for protocols
        // with destructors in conclusions (e.g. T&D::Responder), which
        // is required to find destructor-narrowed exists-trace
        // witnesses (e.g. T&D::Public_part_public). The cost is extra
        // case-splitting on typing/secrecy lemmas in the same
        // protocols, which can exhaust the per-lemma deadline on
        // budget-tight harnesses. Set TAM_DISABLE_VARIANTS=1 to fall
        // back to raw (variant-free) rules for performance debugging.
        let var_disabled = std::env::var("TAM_DISABLE_VARIANTS").is_ok();
        // Compute variants up front but DON'T install them yet — we want
        // precompute_full_sources/precompute_sources to see only the raw
        // rules. Installing variants at precompute time multiplies the
        // [sources]-typing case enumeration by N variants per
        // destructor rule, which causes typing/secrecy lemmas in
        // destructor-using protocols (NSLPK3 types, T&D type_assertion,
        // JCS12 typing_assertion, etc.) to blow past the search budget.
        // Variants are installed *after* source precomputation but
        // *before* `saturate_sources_with_chain_fold`, so chain-fold —
        // which is the only path that actually needs destructor-
        // narrowed alternatives — can still enumerate them.
        let mut computed_variants: Vec<(usize, Vec<crate::rule::ProtoRuleAC>)> =
            Vec::new();
        let mut computed_variant_substs:
            Vec<(usize, Vec<tamarin_term::subst_vfresh::LNSubstVFresh>)> = Vec::new();
        let mut computed_abstracted_rules:
            Vec<(usize, crate::rule::ProtoRuleE, Vec<tamarin_term::subst_vfresh::LNSubstVFresh>)>
            = Vec::new();
        // SplitG variants is the Haskell-faithful path
        // (`someRuleACInst` + `solveRuleConstraints` from Rule.hs:933 /
        // Reduction.hs:766-774).  Always on — there is no legacy fallback.
        //
        // HS-faithful (RuleVariants.hs:75-129): `variantsProtoRule` runs
        // UNCONDITIONALLY for every closed protocol rule.  For rules with no
        // reducible-headed sub-terms, the variant disjunction collapses to
        // `Disj [emptySubstVFresh]` (the `trueDisj` constant at
        // RuleVariants.hs:158); `someRuleACInst` (Rule.hs:940-955) then
        // returns `Just (Disj [emptySubstVFresh])` for EVERY ProtoRule, so
        // `solveRuleConstraints (Just trueDisj)` (Reduction.hs:967-979) still
        // calls `insertGoal (SplitG splitId) False` — bumping `sNextGoalNr`
        // by 1 at every `labelNodeId` call regardless of whether the rule has
        // any destructors.  Skipping the variant-substs computation for
        // non-destructor rules under-bumped that counter and desynchronised
        // RS's gsNr trace from HS's at every destructor-free `labelNodeId`
        // (e.g. Yubikey.spthy::Server, Yubikey.spthy::Setup), which the
        // smart-rank tie-breaker then resolved differently.
        if !var_disabled {
            for (idx, o) in rules.iter().enumerate() {
                if !o.variants.is_empty() { continue; }
                // Pre-applied variant *rules* (legacy path) and the
                // abstracted-rule form only make sense when the rule has
                // reducible-headed sub-terms — otherwise they degenerate to
                // duplicates of the canonical rule.
                let has_reducible = rule_has_reducible(&o.rule);
                if has_reducible {
                    if let Ok(vs) = crate::tools::rule_variants::expand_rule_variants(
                        &maude, &o.rule, &reducible_syms) {
                        if !vs.is_empty() {
                            if dbg_variants {
                                eprintln!("[VARIANTS] rule={:?} expanded into {} variants",
                                    o.rule.info.name, vs.len());
                                for (i, v) in vs.iter().enumerate() {
                                    eprintln!("  [{}] concs: {:?}", i,
                                        v.conclusions.iter()
                                            .map(|c| format!("{:?}={:?}", c.tag, c.terms))
                                            .collect::<Vec<_>>());
                                }
                            }
                            let lb = o.loop_breakers.clone();
                            let mut vs = vs;
                            for v in vs.iter_mut() {
                                v.info.loop_breakers = lb.clone();
                            }
                            computed_variants.push((idx, vs));
                        }
                    }
                }
                // Compute the variant substitutions in their raw form
                // (Haskell `RuleACConstrs = Disj LNSubstVFresh`) — these
                // will be installed as a SplitG goal at search time via
                // `solve_rule_constraints`, mirroring Haskell's
                // `solveRuleConstraints` (Reduction.hs:766-774).
                //
                // HS-faithful: ALWAYS attempt the computation, even for
                // non-destructor rules where the result is `[emptySubstVFresh]`
                // (`trueDisj`, RuleVariants.hs:158).  The downstream
                // `solve_rule_constraints` path treats `Some([empty])` as a
                // trivial-but-real Split that bumps `next_goal_nr` and lets
                // simp's `simp_singleton` fold the disj — matching HS's
                // `insertGoal (SplitG _) False ; simp _ _ eqs` order.
                if let Ok(substs) = crate::tools::rule_variants::variant_substs_for_rule(
                    &maude, &o.rule) {
                    if !substs.is_empty() {
                        computed_variant_substs.push((idx, substs));
                    }
                }
                // Compute the abstracted-rule + variant disjunction
                // (Haskell-faithful `variantsProtoRule` with `abstrRule`).
                // Reducible-headed sub-terms in the rule's facts are
                // replaced by fresh `z_i` vars, and the variant
                // disjunction is keyed by those.  Without this, the
                // canonical rule's destructor restrictions fire on
                // un-narrowed forms and contradict before the SplitG
                // can resolve.  Only meaningful when the rule has
                // reducible-headed sub-terms.
                if has_reducible {
                    if let Ok(Some((abstr, av_substs))) =
                        crate::tools::rule_variants::abstract_rule_and_variants(
                            &maude, &o.rule)
                    {
                        computed_abstracted_rules.push((idx, abstr, av_substs));
                    }
                }
            }
        }
        // `pcTrueSubterm` — `all isSubtermRule $ filter isDestrRule $
        // intruder_rules`.  Mirrors `ClosedTheory.getProofContext`
        // (`lib/theory/src/ClosedTheory.hs:112`).  When the destructor
        // set contains only subterm-rules (sdec / fst / snd / etc., as
        // opposed to constant-RHS rules like `isPair → true`), the
        // strict variant of `hasImpossibleChain` applies.
        let pc_true_subterm = intruder_rules.iter()
            .filter(|r| crate::rule::is_destr_rule_info(&r.info))
            .all(|r| crate::rule::is_subterm_rule_info(&r.info));
        if std::env::var("TAM_RS_DBG_PC_TRUE_SUBTERM").is_ok() {
            eprintln!("[pc_true_subterm] = {}", pc_true_subterm);
            for r in &intruder_rules {
                if crate::rule::is_destr_rule_info(&r.info) {
                    eprintln!("  destr: {:?} subterm={}",
                        crate::rule::rule_name_string(&crate::rule::Rule::new(
                            crate::rule::RuleInfo::Intr(r.info.clone()),
                            vec![], vec![], vec![])),
                        crate::rule::is_subterm_rule_info(&r.info));
                }
            }
        }
        let mut ctx = ProofContext {
            maude,
            maude_pool,
            rules,
            intruder_rules,
            unique_sources: Vec::new(),
            use_induction: UseInduction::AvoidInduction,
            is_diff: false,
            injective_fact_insts,
            full_sources: Vec::new(),
            is_exists_trace: false,
            restrictions,
            typing_assumptions: Vec::new(),
            pc_true_subterm,
            heuristic: None,
            lemma_name: String::new(),
            theory_file: String::new(),
            saturate_state: std::sync::Mutex::new(SaturateState::Pending),
            saturation_limit: std::env::var("TAM_SATURATION_LIMIT").ok()
                .and_then(|s| s.parse::<usize>().ok())
                .unwrap_or_else(|| crate::constraint::solver::sources::IntegerParameters::default()
                    .saturation_limit as usize),
        };
        // Precompute unique sources from the protocol rules.
        let params = crate::constraint::solver::sources::IntegerParameters::default();
        ctx.unique_sources = crate::constraint::solver::sources::precompute_sources(
            &params, &ctx);
        // Precompute full source-case enumerations.  Runs *after*
        // `unique_sources` so per-tag expansion can use the unique-
        // source cache; runs with an empty `full_sources` itself so
        // there's no recursive lookup during precomputation. Saturates
        // the cases via `saturate_sources` so recursive Loop-style
        // chains fold into a finite enumeration of self-contained
        // sub-systems.
        // Install rule variants BEFORE precompute. Haskell's precompute
        // uses the full variant-expanded rule set so cases with chain
        // edges across reducible-headed conclusions (like
        // `Receiver0b → Receiver0b_check` where `verify(...) = true`)
        // already have the variant subst applied. Enable by default;
        // TAM_NO_PRECOMPUTE_VARIANTS=1 forces the legacy
        // (variants-after-precompute) behaviour for diagnostics.
        let precompute_with_variants = std::env::var("TAM_NO_PRECOMPUTE_VARIANTS").is_err();
        if precompute_with_variants {
            for (idx, vs) in &computed_variants {
                if let Some(o) = ctx.rules.get_mut(*idx) {
                    o.variants = vs.clone();
                }
            }
        }
        // Install the raw variant substitutions in their disjunction form.
        // These are consumed by `solve_rule_constraints` at search time.
        // The legacy pre-applied `variants` field above remains populated
        // alongside for backward compatibility with `rule_insts_with`'s
        // current expansion logic — callers can opt into the SplitG path
        // by reading `variant_substs` instead.
        for (idx, substs) in &computed_variant_substs {
            if let Some(o) = ctx.rules.get_mut(*idx) {
                o.variant_substs = substs.clone();
            }
        }
        // Install abstracted rules + their variant disjunctions.
        // Overrides `variant_substs` with the abstraction-composed
        // disjunction (whose domain is the abstracted rule's fresh
        // z_i vars) — `canonical_rule_inst` checks `abstracted_rule`
        // first when present.
        for (idx, abstr, av_substs) in &computed_abstracted_rules {
            if let Some(o) = ctx.rules.get_mut(*idx) {
                o.abstracted_rule = Some(abstr.clone());
                o.variant_substs = av_substs.clone();
            }
        }
        let raw_sources = crate::constraint::solver::sources::precompute_full_sources(&ctx);
        if !precompute_with_variants {
            for (idx, vs) in computed_variants {
                if let Some(o) = ctx.rules.get_mut(idx) {
                    o.variants = vs;
                }
            }
        }
        // Chain-fold saturator: lightweight order-sorted aligner
        // for Proto-premise grafting + Maude-backed intruder-chain
        // folding (Out / KD premises) so `coerce → irecv →
        // <protocol>` chains collapse into a single saturated
        // `case <protocol>`, matching Haskell's
        // `solveAllSafeGoals`-driven saturation.
        //
        // This EXPOSES bugs in `refine_with_source_asms`'s typing
        // refinement (task #99): typing-style lemmas that were
        // previously sorrying now produce wrong verdicts because
        // the grafted protocol-rule producers interact with
        // incomplete typing-pruning logic.  The exposed bugs are
        // real and the saturation is correct per Haskell; the right
        // fix is to strengthen the refinement, not hide the
        // exposure behind a weaker saturator.  See
        // project_rust_proof_diff.md / project_rust_chain_fold.md.
        // HS-faithful lazy precompute: `saturateSources` (Sources.hs:373)
        // is *lazy in cdCases* — its `refineSource ctxt solver`
        // applications produce `Source`s whose updated `cdCases` is
        // itself a thunk that forces only when a consumer pattern-
        // matches on `(name, sys) <- get cdCases th` in a Disj-monad
        // bind.  For protocols where the lemma proof never forces a
        // particular source's `cdCases` (e.g. `Heard`-style existence
        // lemmas on a Var-headed `KU(t:Fresh)` source — HS's
        // `getMsgOneCase` short-circuits on the goal-shape pattern
        // before touching `cdCases`), the thunk never runs and zero
        // saturate-time `[EXEC] solveGoal / exploitPrems / ...` lines
        // are emitted.
        //
        // The eager Rust `saturate_sources_with_chain_fold` call here
        // would walk every source's cases regardless, defeating
        // laziness.  Skipping it leaves `ctx.full_sources` as the
        // unsaturated raw sources from `precompute_full_sources`;
        // each `Source::cases(ctx)` call still runs `initial_source_cases`
        // which does the per-source `initialSource` work but NOT the
        // cross-source chain-fold saturation.  For trivial protocols
        // this is sufficient (HS's saturate is also lazy for them);
        // for protocols that need saturated chains, this is a
        // regression that future work will close by porting saturate
        // itself in a lazy form.
        // HS-faithful lazy saturate: defer the
        // `saturate_sources_with_chain_fold` call to the first
        // `Source::cases(ctx)` call via `ProofContext::ensure_saturated`.
        // `ctx.full_sources` holds the unsaturated raw sources from
        // `precompute_full_sources` (each with `cases_cell = None`).
        // No `[EXEC] solveGoal / exploitPrems / ...` lines fire here —
        // they only fire when a lemma proof forces a source's cases
        // via pattern-matching on its `cdCases` (HS-faithful).
        ctx.full_sources = raw_sources;
        // No saturation here — `ctx.full_sources` holds unsaturated
        // raw sources.  `prove_lemma` calls `ctx.ensure_saturated()`
        // AFTER assigning `ctx.typing_assumptions` so that
        // `refine_with_source_asms` runs with the lemma's [sources]
        // assumptions in hand.  Matches HS's `refineWithSourceAsms`
        // timing where `[Saturating Sources] Done` fires after
        // assumptions are applied.
        // No post-saturate drop pass — Haskell doesn't have one.
        // Haskell relies on saturate-time `contradictoryIf` inside
        // `solveAllSafeGoals` (Sources.hs:118-133) + runtime
        // contradiction detection during proof search.  Set
        // `TAM_ENABLE_DROP_CONTRADICTORY=1` to re-enable the Rust
        // workaround for measurement.
        if std::env::var("TAM_ENABLE_DROP_CONTRADICTORY").is_ok() {
            let prev_full = std::mem::take(&mut ctx.full_sources);
            ctx.full_sources = crate::constraint::solver::sources::drop_contradictory_cases(
                prev_full, &ctx);
        }
        ctx
    }
}

/// Mutate `rules` in place, populating each rule's
/// `info.loop_breakers` from the dataflow relation.  Mirrors Haskell's
/// `useAutoLoopBreakersAC`:
///
/// 1. Build a dataflow over-approximation:
///        (ruFrom, (ruTo, premIdx))
///    where some conclusion of `ruFrom` has the same fact tag as the
///    `premIdx`-th premise of `ruTo`.
/// 2. Lift to the premise-solving relation by pairing every `(ruTo,
///    premIdx)` with every premise of `ruFrom`:
///        ((ruTo, premIdx), (ruFrom, fromPrem))
/// 3. `dfs_loop_breakers` returns the set of `(rule_name, prem_idx)`
///    targets to mark — the premises whose goals should be tagged
///    loop-breaker.
pub fn annotate_loop_breakers(
    rules: &mut [OpenProtoRule],
    maude: &tamarin_term::maude_proc::MaudeHandle,
) {
    use crate::rule::PremIdx;
    use crate::rule::ProtoRuleName;

    // Helper: stable string key for a rule by its `ProtoRuleName`.
    fn rule_key(r: &OpenProtoRule) -> String {
        match &r.rule.info.name {
            ProtoRuleName::Stand(s) => format!("S:{}", s),
            ProtoRuleName::Fresh => "Fresh".to_string(),
        }
    }
    // Indexed view.
    let keys: Vec<String> = rules.iter().map(rule_key).collect();

    // HS `premSolvingRelAC` builds the dataflow relation over `instances`:
    //   `instances ru fa = [ apply (subst `freshToFreeAvoiding` fa) fa
    //                       | subst <- eVariants ru ]`   (LoopBreakers.hs:55-57)
    // where `eVariants ru` is the rule's AC-VARIANT disjunction
    // (`variantsProtoRule`).  For a rule whose conclusion carries a
    // reducible/DH-laden term (e.g. GDH RecvOthers concludes
    // `!AO(.., 'g'^y^~esk)`), a variant substitution expands that term to a
    // syntactic-AC form (`z.1 = 'g'^(~esk*y)`) that Maude's plain `unify`
    // can solve against another rule's premise (`!AO(.., 'g'^y)`).  Unifying
    // the RAW E-rule facts instead — as RS did — sends the local `unifyRaw`
    // (and Maude) `exp(exp('g',y),esk) =? exp('g',y')`, a NESTED-exp
    // narrowing problem the AC unifier rejects, so the dataflow edge (and
    // hence the loop-breaker cycle) is never found.
    //
    // `populate_rule_variants` (run.rs) already computed and stored each
    // rule's variant disjunction (keyed by the *abstracted* rule's fresh
    // z-vars) on every `OpenProtoRule` BEFORE `annotate_loop_breakers`
    // runs, so reuse `o.variant_substs`/`o.abstracted_rule` rather than
    // recomputing via the narrowing-only `variant_substs_for_rule` (which
    // misses DH `exp`/`mult` variant expansion).  When variants are empty
    // (no reducible sub-terms, or this is the precompute call before
    // population) `instances` yields the bare fact, preserving prior
    // behaviour.
    let variant_substs: Vec<&Vec<tamarin_term::subst_vfresh::LNSubstVFresh>> =
        rules.iter().map(|o| &o.variant_substs).collect();

    // `instances ru fa`: apply each variant subst (as a free subst via
    // `freshToFreeAvoiding`) to `fa`.  Empty variant list ⇒ `[fa]`.
    let instances = |rule_idx: usize, fa: &crate::fact::LNFact| -> Vec<crate::fact::LNFact> {
        use tamarin_term::lterm::HasFrees;
        let substs = variant_substs[rule_idx];
        if substs.is_empty() || substs.iter().all(|s| s.is_empty()) {
            return vec![fa.clone()];
        }
        substs.iter().map(|s| {
            // HS `apply (subst `freshToFreeAvoiding` fa) fa`: rename the
            // VFresh range vars to fresh free vars avoiding `fa`'s frees,
            // then apply.  We seed the witness counter above the max idx
            // appearing in `fa` (the avoid set), matching HS's
            // `evalFreshAvoiding (frees fa)`.
            let mut avoid_max: u64 = 0;
            fa.for_each_free(&mut |v| { if v.idx + 1 > avoid_max { avoid_max = v.idx + 1; } });
            let mut next = avoid_max;
            let free = s.fresh_to_free(|_| { let i = next; next += 1; i });
            crate::fact::LNFact {
                tag: fa.tag.clone(),
                annotations: fa.annotations.clone(),
                terms: fa.terms.iter()
                    .map(|t| tamarin_term::subst::apply_vterm(&free, t.clone()))
                    .collect(),
            }
        }).collect()
    };

    // Build the prem-solving relation, mirroring HS's `premSolvingRelAC`
    // (`LoopBreakers.hs:35-58`) EXACTLY, including iteration nesting —
    // `dfsLoopBreakers` walks the relation in list order, so the order
    // determines which node becomes each DFS root and therefore which
    // breakers are picked.
    //
    // HS structure:
    //   dataflowRelAC: ruFrom <- rules; ruTo <- rules;
    //                  (premIdx,premFa0) <- ePrems ruTo; [unifiable];
    //                  return (ruFrom, (ruTo, premIdx))
    //   premSolvingRelAC: (toRu=ruFrom, from=(ruTo,premIdx)) <- dataflowRelAC;
    //                     (toPrem,_) <- ePrems toRu;
    //                     return (from, (toRu, toPrem))
    //                   = ((ruTo,premIdx), (ruFrom,toPrem))
    //
    // So the nesting is: ruFrom (outer) → ruTo → premIdx(of ruTo) →
    // toPrem(of ruFrom, innermost).  Each emitted element's FIRST
    // component is (ruTo, premIdx); the relation appears grouped by
    // ruFrom because that's the outermost loop.
    // HS enumerates premises/conclusions of the AC rule, i.e. the
    // *abstracted* rule (whose reducible-headed sub-terms are replaced by
    // the fresh z-vars the variant substs are keyed on).  Use
    // `abstracted_rule` when present, falling back to the raw E-rule.
    let ac_rules: Vec<&crate::rule::ProtoRuleE> = rules.iter()
        .map(|o| o.abstracted_rule.as_ref().unwrap_or(&o.rule))
        .collect();
    let mut relation: Vec<((String, PremIdx), (String, PremIdx))> = Vec::new();
    for (i_from, _ru_from) in rules.iter().enumerate() {
        let ru_from_ac = ac_rules[i_from];
        for (i_to, _ru_to) in rules.iter().enumerate() {
            let ru_to_ac = ac_rules[i_to];
            for (to_prem_idx, prem_fa) in ru_to_ac.enumerate_premises() {
                // Skip K-facts and built-ins — they're handled by intruder
                // rules and never participate in protocol-rule loops.
                if !matches!(prem_fa.tag, crate::fact::FactTag::Proto(_, _, _)) {
                    continue;
                }
                // Haskell `LoopBreakers.hs:48`:
                //   `guard $ not (isNoSourcesFact premFa0)`
                if prem_fa.is_no_sources() {
                    continue;
                }
                // Haskell `LoopBreakers.hs:49-53`: edge exists iff some
                // conclusion of `ruFrom` is AC-UNIFIABLE with this premise
                // (not merely same-tag).  Tag-only matching over-approximates
                // and adds spurious self-edges (e.g. `I_m0`'s `St_I(<'m2'>)`
                // conclusion vs its own `St_I('m0')` premise share a tag but
                // do NOT unify), which fabricate extra cycles and over-mark
                // loop breakers.  Use real Maude unifiability, mirroring HS.
                //
                // HS `dataflowRelAC` (LoopBreakers.hs:49-53):
                //   guard $ or $ do
                //     premFa <- instances ruTo premFa0
                //     concFa <- instances ruFrom =<< (snd <$> eConcs ruFrom)
                //     let concFaFresh = rename concFa `evalFresh` avoid premFa
                //     return $ unifiableLNFacts concFaFresh premFa
                // i.e. iterate the VARIANT INSTANCES of both the premise and
                // each conclusion, rename the conclusion away from the
                // premise's frees, and check Maude AC-unifiability.
                let prem_insts = instances(i_to, prem_fa);
                let conc_unifies = ru_from_ac.conclusions.iter().any(|c0| {
                    if c0.tag != prem_fa.tag { return false; }
                    instances(i_from, c0).iter().any(|conc| {
                        prem_insts.iter().any(|prem| {
                            let mut fresh = tamarin_term::lterm::avoid(prem);
                            let conc_fresh =
                                tamarin_term::lterm::rename(conc.clone(), &mut fresh);
                            crate::rule::unifiable_ln_facts(maude, &conc_fresh, prem)
                                .unwrap_or(false)
                        })
                    })
                });
                if !conc_unifies { continue; }
                for (from_prem_idx, _) in ru_from_ac.enumerate_premises() {
                    relation.push((
                        (keys[i_to].clone(), to_prem_idx),
                        (keys[i_from].clone(), from_prem_idx),
                    ));
                }
            }
        }
    }
    // Run DFS loop-breaker selection.
    let breakers: Vec<(String, PremIdx)> =
        crate::tools::loop_breakers::dfs_loop_breakers(&relation);
    // Annotate each rule's `loop_breakers` with the picked premises.
    for (k, ru) in keys.iter().zip(rules.iter_mut()) {
        ru.loop_breakers = breakers.iter()
            .filter(|(rk, _)| rk == k)
            .map(|(_, p)| *p)
            .collect();
    }
}
