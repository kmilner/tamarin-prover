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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UseInduction { UseInduction, AvoidInduction }

impl ProofContext {
    pub fn new(maude: MaudeHandle, mut rules: Vec<OpenProtoRule>) -> Self {
        // Inherit the maude signature from the handle so we can
        // synthesise per-symbol construction rules.
        let sig = maude.maude_sig();
        let mut intruder_rules = crate::intruder_rules::special_intruder_rules(false);
        // Subterm-rule expansion: combines `constructionRules` and
        // `destructionRules` over the signature's `stRules`.  Mirrors
        // Haskell's `subtermIntruderRules diff maudeSig`.  Without
        // this, `[builtins: symmetric-encryption]` etc. theories never
        // emit decryption destructors and the intruder can't analyse
        // received ciphertexts.
        intruder_rules.extend(crate::intruder_rules::subterm_intruder_rules(false, &sig));
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
        // (`Theory.Tools.LoopBreakers`).  We approximate the dataflow
        // relation using fact-tag matching (no Maude AC unification);
        // a rule R_from feeds R_to.premIdx if some conclusion of
        // R_from has the same tag as the premise.  Loop-breaker
        // analysis runs on `(rule_name, prem_idx)` pairs.
        annotate_loop_breakers(&mut rules);
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
            }
        }
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
fn annotate_loop_breakers(rules: &mut [OpenProtoRule]) {
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
            for (i_from, ru_from) in rules.iter().enumerate() {
                let conc_match = ru_from.rule.conclusions.iter()
                    .any(|c| c.tag == prem_fa.tag);
                if !conc_match { continue; }
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
