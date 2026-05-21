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

use tamarin_term::maude_proc::MaudeHandle;

use crate::rule::IntrRuleAC;
use crate::theory::OpenProtoRule;

/// Minimum-viable context for the solver loop.
#[derive(Clone, Debug)]
pub struct ProofContext {
    pub maude: MaudeHandle,
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseInduction { UseInduction, AvoidInduction }

impl ProofContext {
    pub fn new(maude: MaudeHandle, rules: Vec<OpenProtoRule>) -> Self {
        Self::new_with_restrictions(maude, rules, Vec::new())
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
        intruder_rules.extend(crate::intruder_rules::special_intruder_rules(false));
        // Detect injective fact instances ahead of time — mirrors
        // Haskell's `pcInjectiveFactInsts` precomputation.
        let proto_rules: Vec<crate::rule::ProtoRuleE> = rules.iter()
            .map(|r| r.rule.clone())
            .collect();
        let injective_fact_insts =
            crate::tools::injective_fact_instances::simple_injective_fact_instances(
                &proto_rules);
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
        if !var_disabled {
            for (idx, o) in rules.iter().enumerate() {
                if !o.variants.is_empty() { continue; }
                if !rule_has_reducible(&o.rule) { continue; }
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
                // Compute the variant substitutions in their raw form
                // (Haskell `RuleACConstrs = Disj LNSubstVFresh`) — these
                // will be installed as a SplitG goal at search time via
                // `solve_rule_constraints`, mirroring Haskell's
                // `solveRuleConstraints` (Reduction.hs:766-774).
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
                // can resolve.
                if let Ok(Some((abstr, av_substs))) =
                    crate::tools::rule_variants::abstract_rule_and_variants(
                        &maude, &o.rule)
                {
                    computed_abstracted_rules.push((idx, abstr, av_substs));
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
        let mut ctx = ProofContext {
            maude,
            rules,
            intruder_rules,
            unique_sources: Vec::new(),
            use_induction: UseInduction::AvoidInduction,
            is_diff: false,
            injective_fact_insts,
            full_sources: Vec::new(),
            is_exists_trace: false,
            restrictions,
            pc_true_subterm,
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
        ctx.full_sources = crate::constraint::solver::sources::saturate_sources_with_chain_fold(
            raw_sources, params.saturation_limit as usize, &ctx);
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
fn annotate_loop_breakers(
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

    // Build the prem-solving relation as ((to_key, to_prem), (from_key, from_prem)).
    let mut relation: Vec<((String, PremIdx), (String, PremIdx))> = Vec::new();
    for (i_to, ru_to) in rules.iter().enumerate() {
        for (to_prem_idx, prem_fa) in ru_to.rule.enumerate_premises() {
            // Skip K-facts and built-ins — they're handled by intruder
            // rules and never participate in protocol-rule loops.
            if !matches!(prem_fa.tag, crate::fact::FactTag::Proto(_, _, _)) {
                continue;
            }
            // Haskell `LoopBreakers.hs:48`:
            //   `guard $ not (isNoSourcesFact premFa0)`
            // Premises tagged `[no_precomp]` are dropped from the
            // dataflow relation entirely.  Without this, no_precomp
            // premises get spurious loop-breaker marks, deprioritising
            // goals that Haskell intends to be solved eagerly.
            if prem_fa.is_no_sources() {
                continue;
            }
            for (i_from, ru_from) in rules.iter().enumerate() {
                // Haskell `LoopBreakers.hs:53` calls
                // `unifiableLNFacts concFaFresh premFa` (Maude AC-
                // unifiability).  Calling Maude N×M times during
                // precompute OOMs on large protocols (NSPK3, Minimal_*).
                // Stick with fast-path tag equality for now; deeper
                // Maude-AC dedup is a follow-up that would need a
                // unification cache keyed by `(tag, normalized-shape)`.
                let conc_match = ru_from.rule.conclusions.iter()
                    .any(|c| c.tag == prem_fa.tag);
                if !conc_match { continue; }
                let _ = maude;
                for (from_prem_idx, _) in ru_from.rule.enumerate_premises() {
                    relation.push((
                        (keys[i_to].clone(), to_prem_idx),
                        (keys[i_from].clone(), from_prem_idx),
                    ));
                }
                let _ = i_from;
            }
            let _ = i_to;
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
