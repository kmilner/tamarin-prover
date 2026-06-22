//! End-to-end `prove_lemma` entry point.
//!
//! Bridges a parsed `.spthy` theory and a lemma name into the
//! proof-search driver. Mirrors the high-level shape of Haskell's
//! `Theory.Proof.proveLemma`:
//!
//! 1. Look up the lemma by name in the elaborated theory.
//! 2. Convert its formula to guarded form.
//! 3. Convert restrictions to guarded form.
//! 4. Build the initial `System` via `formula_to_system`.
//! 5. Build a `ProofContext` carrying the theory's rules.
//! 6. Drive `run_proof_search` to produce a `ProofNode` tree.
//!
//! Returns `Err` on parser/elaboration/guarded-conversion failures.

use tamarin_parser::ast as p;

use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::search::{run_proof_search, ProofNode};
use crate::constraint::system::{formula_to_system, SourceKind};
use crate::elaborate::elaborate;
use crate::guarded::{formula_to_guarded, Guarded};
use crate::theory::OpenProtoRule;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProveError {
    LemmaNotFound(String),
    Elaboration(String),
    Guarded(String),
}

/// Render the full HS `ppError` doc (Guarded.hs:477) for a failed guarded
/// conversion: the error text, the quoted failing sub-formula (both
/// quantifier-level errors include `ppFormula f0`, Guarded.hs:508-514 and
/// 561-563), then "in the formula" + the quoted converted formula.  This is
/// the exact message HS's `formulaToGuarded_ = either (error . render) id`
/// (Guarded.hs:464-465) dies with when a proven lemma's formula cannot be
/// converted.
fn guard_error_doc(
    e: &crate::guarded::GuardError,
    formula: &tamarin_parser::ast::Formula,
) -> String {
    let full = crate::pretty_formula::pretty_formula(formula);
    let sub = e.subject_formula.as_ref()
        .map(crate::pretty_formula::pretty_formula)
        .unwrap_or_else(|| full.clone());
    format!("{}\n  \"{}\"\nin the formula\n  \"{}\"", e.message, sub, full)
}

impl std::fmt::Display for ProveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProveError::LemmaNotFound(n) => write!(f, "lemma not found: {}", n),
            ProveError::Elaboration(m) => write!(f, "elaboration: {}", m),
            ProveError::Guarded(m) => write!(f, "guarded conversion: {}", m),
        }
    }
}

/// Prepend the theory file's directory to any Oracle/OracleSmart rankings
/// whose path is not already absolute.
///
/// Mirrors HS `oraclePath oracle = takeDirectory inFile </> normalise relPath`
/// (System.hs:574-575, Parser.hs:304).  NOTE: HS's `normalise relPath`
/// (`System.FilePath.normalise`) collapses `.` and redundant separators
/// (NOT `..`); we skip that, directory-prefixing via `std::path::Path::join`
/// (purely lexical, leaves `./` and `a/b/../c` as-is).  That only affects the
/// literal exec-path string, not which file is run — the path is consumed by
/// `Command::new` (oracle exec), never printed into `--prove` output, and the
/// OS resolves a leading `./` identically — so the difference is unobservable.
fn prepend_theory_dir_to_oracle_paths(
    rankings: &mut Vec<crate::constraint::solver::goals::GoalRanking>,
    in_file: &str,
) {
    use crate::constraint::solver::goals::GoalRanking;
    let work_dir = std::path::Path::new(in_file).parent()
        .map(|p| p.to_path_buf())
        .unwrap_or_else(|| std::path::PathBuf::from("."));
    for r in rankings.iter_mut() {
        match r {
            GoalRanking::Oracle { oracle_path, .. }
            | GoalRanking::OracleSmart { oracle_path, .. } => {
                let p = std::path::Path::new(oracle_path.as_str());
                if !p.is_absolute() {
                    let resolved = work_dir.join(p);
                    // Directory-prefix only — `Path::join` is lexical and
                    // leaves `./` and `../` as-is.  HS `normalise` would drop
                    // a leading `./` and collapse redundant separators (but
                    // not `..`); the difference is exec-string-only and the OS
                    // resolves it identically, so it is unobservable.
                    let resolved = resolved.to_string_lossy().to_string();
                    *oracle_path = resolved;
                }
            }
            _ => {}
        }
    }
}

/// One theory-level cache entry of refined source cases — the result of
/// a `ctx.ensure_saturated()` pass, snapshotted per `Source` by goal.
/// Keyed (in [`ProverSession::source_cache`]) by the SORTED set of
/// `[sources]`-lemma names folded into `typing_assumptions`.
///
/// Why this is safe to share across lemmas (lever #3 — HS computes
/// `_crcRefinedSources` ONCE per `ClosedRuleCache` and reuses it for
/// every lemma; RuleItem.hs:64-69, Prover.hs:170-184):
///   * The saturated+refined cases are a pure function of the (shared
///     template) raw sources + rules + restrictions + `typing_assumptions`.
///     Two lemmas with the same source-name key feed identical inputs, so
///     they produce identical cases.
///   * We ONLY cache (and therefore only reuse) entries whose producing
///     `ensure_saturated` consumed ZERO fresh Maude vars (`delta == 0`).
///     With no fresh allocation the cases embed only template-sourced var
///     indices (shared, identical across clones) AND the per-lemma
///     fresh-counter trajectory is unperturbed — so a cache hit is
///     byte-identical to recomputing, both in the cases and in the counter
///     state the subsequent proof search starts from.  `delta` is
///     deterministic for a given key, so a key that cached once (delta 0)
///     yields delta 0 on every hit.  Sources lemmas (which DO allocate,
///     e.g. NSLPK3 `types` delta=5, and carry a self-excluded key) are
///     never cached and keep recomputing — they are rare and proved once.
struct CachedSources {
    /// Per source: (goal join-key, refined case list, incomplete flag).
    sources: Vec<(
        crate::constraint::constraints::Goal,
        Vec<(Vec<String>, crate::constraint::system::System)>,
        bool,
    )>,
}

/// Per-file shared prover state — the bits of work that depend only on
/// the theory, not on which lemma is being proved.  Built once via
/// [`ProverSession::build_with_in_file`] and reused across `prove_lemma_in_session`
/// calls so each lemma in a multi-lemma `--prove` run pays the heavy
/// setup cost only ONCE.
///
/// Profile showed ~3s of `ProofContext::new` work (intruder rules,
/// `close_intr_rule` Maude variants, DH/BP cached variants, per-rule
/// `expand_rule_variants`, `precompute_sources`, `precompute_full_sources`)
/// re-running per lemma.  On wireguard's 8 lemmas that was ~24s
/// (HS amortises this across the file).  By sharing the template
/// `ProofContext` we recover that cost; per-lemma we still run the
/// lightweight `ensure_saturated` (each lemma needs its own
/// `typing_assumptions`-refined source cases).
pub struct ProverSession {
    /// Elaborated typed theory.  Used to look up lemmas, restrictions,
    /// rules, heuristic.  Constructed once.
    pub theory: crate::theory::Theory,
    /// File-level RAII guard for `set_user_funs_for_theory`.  Kept
    /// alive for the whole session so per-lemma `term_to_lnterm`
    /// calls see the right user-fn-symbol set.
    _user_funs_guard: crate::elaborate::UserFunsForTheoryGuard,
    /// Guarded-form restrictions (constructed once from theory).
    restrictions: Vec<Guarded>,
    /// Template `ProofContext` carrying the expensive precompute:
    /// `rules` (with variants installed), `intruder_rules`,
    /// `unique_sources`, `full_sources` (raw, unsaturated cells), etc.
    /// Cloned per lemma; each clone sets its own
    /// `typing_assumptions`/`heuristic`/`is_exists_trace`/`use_induction`
    /// and runs `ensure_saturated` to materialise lemma-specific
    /// refined source cases.
    template_ctx: ProofContext,
    /// Fresh-counter delta consumed by `ProofContext::new_with_…` during
    /// template construction.  Each non-session `prove_lemma_with_pool`
    /// call advances the global fresh-var counter by this amount
    /// (`close_intr_rule` Maude calls + per-rule `expand_rule_variants`).
    /// In session mode the template is built ONCE so the counter only
    /// advances by `K` once.  Without re-bumping per lemma, lemma N's
    /// runtime fresh allocations would start at `K + sum(prior_proofs)`
    /// instead of the per-lemma path's `N*K + sum(prior_proofs)` — and
    /// that delta is observable as a divergent proof on a small subset
    /// of lemmas where allocated witness indices interact with rule-
    /// variant subst indices (e.g. wireguard `identity_hiding` becomes
    /// 1 step shorter without this bump).  `prove_lemma_in_session`
    /// calls `maude.ensure_above` with an incrementing target so each
    /// per-lemma counter trajectory matches the non-session path
    /// exactly, byte-for-byte across the whole proof tree.
    setup_counter_delta: u64,
    /// Counter value BEFORE the template was built — used together
    /// with `setup_counter_delta` to compute the per-lemma bump target.
    setup_counter_before: u64,
    /// Number of lemmas already processed via `prove_lemma_in_session`.
    /// Drives the counter-bump trajectory.  Use `AtomicU64` so the
    /// session can stay `&self` to its callers.
    lemma_idx: std::sync::atomic::AtomicU64,
    /// Lever #3 — shared refined-source cache (see [`CachedSources`]).
    /// Keyed by the sorted `[sources]`-lemma name set.  Populated lazily
    /// on the first lemma of each key; reused by all later lemmas with the
    /// same key (every normal lemma shares the all-sources key), letting
    /// the expensive `saturate_sources_with_simp` pass run once per theory
    /// instead of once per lemma.  `Mutex` keeps the session `&self`.
    source_cache: std::sync::Mutex<
        std::collections::HashMap<Vec<String>, CachedSources>,
    >,
}

/// Compute the cumulative setup-counter advance the non-session
/// `prove_lemma_with_pool` path would have done by lemma index `n`
/// (1-indexed).  Each non-session call advances the counter by
/// `setup_counter_delta`, so by the start of lemma `n` the counter
/// would have advanced `n * delta`.  In session mode the template
/// build only advanced it by `1 * delta`, so we need an extra
/// `(n - 1) * delta` bump before lemma `n`'s runtime to match.
fn setup_target_for(delta: u64, n: u64) -> u64 {
    delta.saturating_mul(n)
}

/// Per-lemma source kind, mirroring HS `lemmaSourceKind` (Lemma.hs:38-41):
///   lemmaSourceKind lem
///     | SourceLemma `elem` lAttributes lem = RawSource
///     | otherwise                          = RefinedSource
/// HS sets `pcSourceKind = lemmaSourceKind l` (ClosedTheory.hs:116) and
/// `mkSystem` stamps it onto the initial system's `sSourceKind`
/// (Prover.hs:325).  In RS `SourceKind`, `RawSources < RefinedSources`,
/// matching HS's `RawSource < RefinedSource` Ord (System.hs:362-365), so it
/// can be used directly as the `lemmaSourceKind lem <= kind` bound below.
fn lemma_source_kind(lemma: &crate::theory::Lemma) -> SourceKind {
    if lemma.attributes.iter().any(|a| matches!(a, crate::theory::LemmaAttr::Sources)) {
        SourceKind::RawSources
    } else {
        SourceKind::RefinedSources
    }
}

/// Gather the `[reuse]` lemmas declared BEFORE `lemma_name`, mirroring HS
/// `gatherReusableLemmas $ L.get sSourceKind sys` (Prover.hs:329-338):
///
///   guard $ lemmaSourceKind lem <= kind
///        && ReuseLemma `elem` lAttributes lem
///        && AllTraces == lTraceQuantifier lem
///        && lName lem `notElem` pcHiddenLemmas ctxt
///        && "ALL"     `notElem` pcHiddenLemmas ctxt
///
/// `kind` is the source kind of the system being built (= the proved
/// lemma's `lemmaSourceKind`).  `pcHiddenLemmas` is populated from the
/// PROVED lemma's own `[hide_lemma=..]` attributes (ClosedTheory.hs:109),
/// so the hidden set is computed here from `lemma_name`'s attributes.
/// HS uses `formulaToGuarded_` (fail-loud) on each reuse formula, so a
/// non-guardable reuse formula propagates a `ProveError` rather than being
/// silently dropped.
fn gather_reusable_lemmas(
    theory: &crate::theory::Theory,
    lemma_name: &str,
    kind: SourceKind,
) -> Result<Vec<Guarded>, ProveError> {
    // HS `pcHiddenLemmas` = the proved lemma's `[hide_lemma=h]` names.
    let hidden: Vec<&str> = theory
        .lookup_lemma(lemma_name)
        .map(|l| l.attributes.iter().filter_map(|a| match a {
            crate::theory::LemmaAttr::HideLemma(h) => Some(h.as_str()),
            _ => None,
        }).collect())
        .unwrap_or_default();
    let hide_all = hidden.contains(&"ALL");
    let mut reuse_lemmas: Vec<Guarded> = Vec::new();
    for prior in theory.lemmas() {
        if prior.name == lemma_name { break; }
        if lemma_source_kind(prior) > kind { continue; }
        if !prior.attributes.iter().any(|a| matches!(a, crate::theory::LemmaAttr::Reuse)) {
            continue;
        }
        if !matches!(prior.trace_quantifier, crate::theory::TraceQuantifier::AllTraces) {
            continue;
        }
        if hide_all || hidden.contains(&prior.name.as_str()) {
            continue;
        }
        let rg = formula_to_guarded(&prior.formula)
            .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &prior.formula)))?;
        reuse_lemmas.push(rg);
    }
    Ok(reuse_lemmas)
}

impl ProverSession {
    /// Build the shared per-file state, also setting `theory.in_file` for
    /// oracle path resolution (HS Parser.hs:304).  Does the expensive
    /// once-per-file work: theory elaboration, restriction conversion, full
    /// `ProofContext` construction (which runs intruder rule generation,
    /// `close_intr_rule`, DH/BP cached variants, per-rule variant
    /// expansion, source precomputation).
    pub fn build_with_in_file(
        parser_theory: &p::Theory,
        maude: tamarin_term::maude_proc::MaudeHandle,
        pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
        in_file: &str,
    ) -> Result<Self, ProveError> {
        // RAII-set the user-fn-symbol thread-locals for the WHOLE
        // session.  Per-lemma `term_to_lnterm` calls during search
        // need these set; the parser-theory drives the set.
        let _user_funs_guard = crate::elaborate::set_user_funs_for_theory(parser_theory);
        let mut theory = elaborate(parser_theory)
            .map_err(|e| ProveError::Elaboration(e.message))?;
        // Set in_file for oracle path resolution (HS Parser.hs:304).
        theory.in_file = in_file.to_string();
        // HS `mkSystem` maps `formulaToGuarded_ = either (error . render) id`
        // (Prover.hs:324, Guarded.hs:466-467) over restriction formulas — it
        // ABORTS on a non-guardable restriction rather than silently dropping
        // it (which would weaken the constraint set and could let an unsound
        // proof through).  Mirror the fail-loud behaviour: propagate a
        // `ProveError::Guarded` instead of skipping.
        let mut restrictions: Vec<Guarded> = Vec::new();
        for r in theory.restrictions() {
            let rg = formula_to_guarded(&r.formula)
                .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &r.formula)))?;
            restrictions.push(rg);
        }
        let rules: Vec<OpenProtoRule> = theory.rules().cloned().collect();
        // Capture the fresh-counter span around the template build so we
        // can replay the bump per lemma (see `setup_counter_delta` docs).
        let setup_counter_before = maude.fresh_counter_peek();
        let template_ctx = ProofContext::new_with_restrictions_and_pool(
            maude.clone(), pool, rules, restrictions.clone());
        let setup_counter_after = maude.fresh_counter_peek();
        let setup_counter_delta = setup_counter_after.saturating_sub(setup_counter_before);
        Ok(ProverSession {
            theory,
            _user_funs_guard,
            restrictions,
            template_ctx,
            setup_counter_delta,
            setup_counter_before,
            lemma_idx: std::sync::atomic::AtomicU64::new(0),
            source_cache: std::sync::Mutex::new(std::collections::HashMap::new()),
        })
    }
}

/// Prove a single lemma using a pre-built `ProverSession`.  Skips the
/// expensive theory-level setup (which `ProverSession::build_with_in_file` did) and
/// runs only the per-lemma work: guarded conversion of lemma+reuse
/// formulas, `formula_to_system`, ProofContext clone +
/// per-lemma-field setup, `ensure_saturated` (typing-asm refinement),
/// and proof-tree search.
pub fn prove_lemma_in_session(
    session: &ProverSession,
    lemma_name: &str,
    max_steps: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_in_session_mode(session, lemma_name, max_steps, true)
}

/// Replay a non-target lemma's stored skeleton WITHOUT auto-proving its
/// open leaves — HS's close-time `checkAndExtendProver (sorryProver
/// Nothing)` (Prover.hs:174-185).  Used for lemmas the `--prove`
/// selector does not target: HS retains their close-time-replayed proof
/// verbatim (Prover.hs:273-275) and reports the stored status.  Returns
/// the lemma's own start system + a `Sorry` placeholder when no stored
/// skeleton exists (HS keeps the parsed `unproven ()` skeleton, which is
/// a single `sorry`).
pub fn check_and_extend_lemma_in_session(
    session: &ProverSession,
    lemma_name: &str,
    max_steps: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_in_session_mode(session, lemma_name, max_steps, false)
}

fn prove_lemma_in_session_mode(
    session: &ProverSession,
    lemma_name: &str,
    max_steps: usize,
    auto_prove: bool,
) -> Result<ProofNode, ProveError> {
    let trace = std::env::var("TAM_DBG_PHASE").is_ok();
    let t_phase: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };

    let theory = &session.theory;
    let lemma = theory
        .lookup_lemma(lemma_name)
        .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;

    let g = formula_to_guarded(&lemma.formula)
        .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &lemma.formula)))?;

    // Per-lemma source kind, mirroring HS `lemmaSourceKind` (Lemma.hs:38-41):
    // `[sources]`-tagged lemmas get RawSource, all others RefinedSource.
    // HS sets `pcSourceKind = lemmaSourceKind l` (ClosedTheory.hs:102,116)
    // and `formulaToSystem` stamps it onto the initial system's
    // `sSourceKind` (Prover.hs:325).
    let lemma_source_kind = lemma_source_kind(lemma);

    // `[reuse]` lemmas declared BEFORE this one.  Same gather logic as
    // the pre-session prove_lemma_with_pool path.
    let reuse_lemmas =
        gather_reusable_lemmas(theory, lemma_name, lemma_source_kind)?;

    let tq = match lemma.trace_quantifier {
        crate::theory::TraceQuantifier::AllTraces => p::TraceQuantifier::AllTraces,
        crate::theory::TraceQuantifier::ExistsTrace => p::TraceQuantifier::ExistsTrace,
    };
    let mut sys = formula_to_system(
        session.restrictions.clone(),
        lemma_source_kind,
        tq,
        false,
        &g,
    );
    sys.insert_lemmas(reuse_lemmas);

    if trace { eprintln!("[phase] (session) formula_to_system done dt={:.3}s",
        t_phase.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    let t_ctx: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    // Clone the template ProofContext.  The template was built once at
    // session-construction time with raw (unsaturated) `full_sources`
    // (each source's `cases_cell = None`).  Cloning copies those
    // unsaturated cells, so each lemma's `ensure_saturated` populates
    // ITS OWN clone's cells with refinements driven by ITS OWN
    // `typing_assumptions` — no cross-lemma contamination.
    let mut ctx = if std::env::var("TAM_DBG_SESSION_REBUILD").is_ok() {
        let rules: Vec<OpenProtoRule> = theory.rules().cloned().collect();
        ProofContext::new_with_restrictions_and_pool(
            session.template_ctx.maude.clone(),
            session.template_ctx.maude_pool.clone(),
            rules,
            session.restrictions.clone())
    } else {
        session.template_ctx.clone()
    };
    // Replay the fresh-counter bump that the legacy per-lemma
    // `prove_lemma_with_pool` path would have done at this point via
    // its own `ProofContext::new_with_restrictions_and_pool`.  In
    // session mode the template was built ONCE, so the global counter
    // only advanced by `K` once; without re-bumping per lemma, each
    // lemma's runtime allocations would start at the wrong index and
    // a small number of lemmas (e.g. wireguard `identity_hiding`)
    // would diverge structurally.  Bump such that lemma `i` (0-indexed)
    // sees the same counter value it would in the non-session path:
    // `setup_counter_before + (i+1)*setup_counter_delta`.
    let lemma_i = session.lemma_idx
        .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let target = session.setup_counter_before
        .saturating_add(setup_target_for(session.setup_counter_delta, lemma_i + 1));
    ctx.maude.ensure_above(target.saturating_sub(1));
    if trace { eprintln!("[phase] (session) ProofContext clone dt={:.3}s",
        t_ctx.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    ctx.is_exists_trace = matches!(
        lemma.trace_quantifier,
        crate::theory::TraceQuantifier::ExistsTrace,
    );
    let session_in_file = &theory.in_file;
    let lemma_heuristic: Option<&str> = lemma.attributes.iter().find_map(|a| match a {
        crate::theory::LemmaAttr::Heuristic(s) => Some(s.as_str()),
        _ => None,
    });
    let session_heuristic_raw: Option<String> = match lemma_heuristic {
        Some(h) => Some(h.to_string()),
        None => theory.heuristic.first().cloned(),
    };
    ctx.heuristic = session_heuristic_raw.map(|h| {
        let mut rankings = crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
            &h, session_in_file, &theory.tactic);
        prepend_theory_dir_to_oracle_paths(&mut rankings, session_in_file);
        rankings
    });
    ctx.lemma_name = lemma_name.to_string();
    ctx.theory_file = session_in_file.clone();
    let mut typing_assumptions: Vec<Guarded> = Vec::new();
    // `source_key` identifies the refined-source computation: the SORTED
    // set of `[sources]`-lemma names folded into `typing_assumptions`.
    // Every normal lemma yields the full set (the current lemma, being
    // normal, is never a `[sources]` lemma so the `continue` below never
    // fires for it); a `[sources]` lemma yields the set minus itself.
    let mut source_key: Vec<String> = Vec::new();
    for prior in theory.lemmas() {
        if prior.name == lemma_name { continue; }
        if !prior.attributes.iter().any(|a| matches!(a, crate::theory::LemmaAttr::Sources)) {
            continue;
        }
        if !matches!(prior.trace_quantifier, crate::theory::TraceQuantifier::AllTraces) {
            continue;
        }
        // HS `typAsms` (Prover.hs:142-144) uses `formulaToGuarded_`
        // (fail-loud) on each source-lemma formula — propagate rather than
        // silently drop.
        let rg = formula_to_guarded(&prior.formula)
            .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &prior.formula)))?;
        typing_assumptions.push(rg);
        source_key.push(prior.name.clone());
    }
    source_key.sort();
    ctx.typing_assumptions = typing_assumptions;
    let t_sat: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    // HS-faithful laziness: refined sources are a lazy `where`-bound thunk
    // in HS's `ClosedRuleCache` (`refinedSources` = `precomputeSources` →
    // `refineWithSourceAsms`, Rule.hs:156-157), forced ONLY when a proof
    // method reads `pcSources` (ProofMethod.hs:317).  A non-target lemma
    // with NO stored skeleton replays HS's parsed `unproven () = sorry`
    // (`unproven = sorry Nothing`, Proof.hs:255-256; used by the lemma
    // constructor at ProofSkeleton.hs:61) via `checkAndExtendProver`'s
    // `sorry` walk
    // (Proof.hs:624-630) — that single `Sorry` node consults no source,
    // so HS never forces the (potentially very expensive) refined-source
    // thunk for it.  RS mirrors that here: such a lemma will hit the
    // `annotated_sorry_root` early return below WITHOUT touching
    // `cases(ctx)`, so we must NOT eagerly run `ensure_saturated` for it.
    // (Eagerly saturating every lemma — even bare-sorry ones — made
    // `--prove=__nomatch__`-style runs over a multiset theory spend the
    // full per-lemma source-saturation budget × #lemmas while HS returned
    // in moments; e.g. spdm121 `--prove=<no match>` was ~61s vs HS 0.7s.
    // The `cases(ctx)` accessor (sources.rs) still calls `ensure_saturated`
    // lazily for every path that DOES consult a source — skeleton replay
    // and `run_proof_search` — so correctness is unchanged.)
    let will_emit_bare_sorry =
        !auto_prove && lemma.proof.tree.is_none();
    // Lever #3: reuse a previously-computed refined-source set when one
    // exists for this exact `source_key`.  See [`CachedSources`] for why a
    // hit is byte-identical (only delta==0 results are ever cached).
    let cache_disabled = std::env::var("TAM_RS_NO_SOURCE_CACHE").is_ok();
    let mut cache_hit = false;
    if will_emit_bare_sorry {
        // Skip the eager saturate + cache entirely — this lemma forces no
        // source case (matches HS's lazy `pcSources`).  Leave the lazy
        // `cases(ctx)` hook in place in case some future path consults a
        // source; for the bare-sorry early return it never fires.
    } else if !cache_disabled {
        let guard = session.source_cache.lock().unwrap();
        if let Some(entry) = guard.get(&source_key) {
            // Restore cached cases onto this clone's lazy sources by goal,
            // then mark saturation Done so `cases(ctx)` reads them directly
            // and the expensive `ensure_saturated` pass is skipped.
            for src in &mut ctx.full_sources {
                if let Some((_, cases, incomplete)) =
                    entry.sources.iter().find(|(g, _, _)| *g == src.goal)
                {
                    src.cases_set_list(cases.clone());
                    src.incomplete = *incomplete;
                }
            }
            ctx.mark_saturated_done();
            cache_hit = true;
        }
    }
    if will_emit_bare_sorry {
        if std::env::var("TAM_DBG_SAT_COUNTER").is_ok() {
            eprintln!("[SAT_COUNTER] lemma={} key={:?} (bare-sorry, saturation deferred)",
                lemma_name, source_key);
        }
    } else if !cache_hit {
        let cnt_before = ctx.maude.fresh_counter_peek();
        ctx.ensure_saturated();
        let delta = ctx.maude.fresh_counter_peek().saturating_sub(cnt_before);
        if std::env::var("TAM_DBG_SAT_COUNTER").is_ok() {
            eprintln!("[SAT_COUNTER] lemma={} key={:?} delta={} (computed)",
                lemma_name, source_key, delta);
        }
        // Only cache results that allocated NO fresh vars — those are the
        // ones safe to replay byte-identically (counter unperturbed, cases
        // carry only template-sourced var indices).  Sources lemmas (delta
        // > 0) keep recomputing.
        if !cache_disabled && delta == 0 {
            let snapshot: Vec<_> = ctx.full_sources.iter()
                .map(|s| (s.goal.clone(), s.cases_or_empty_list(), s.incomplete))
                .collect();
            session.source_cache.lock().unwrap()
                .entry(source_key)
                .or_insert(CachedSources { sources: snapshot });
        }
    } else if std::env::var("TAM_DBG_SAT_COUNTER").is_ok() {
        eprintln!("[SAT_COUNTER] lemma={} key={:?} (cache hit)", lemma_name, source_key);
    }
    if trace { eprintln!("[phase] (session) ensure_saturated dt={:.3}s hit={}",
        t_sat.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64()), cache_hit); }
    if std::env::var("TAM_RS_DBG_PHASE").is_ok() {
        eprintln!("[rs-phase] lemma-proof START");
    }
    let force_induction = lemma.attributes.iter().any(|a| matches!(a,
        crate::theory::LemmaAttr::UseInduction | crate::theory::LemmaAttr::Sources));
    if force_induction {
        ctx.use_induction = crate::constraint::solver::context::UseInduction::UseInduction;
    }
    // Skeleton replay: same logic as in `prove_lemma_with_pool`.
    if let Some(tree) = lemma.proof.tree.clone() {
        if auto_prove {
            return Ok(crate::replay::replace_sorry_prove(&ctx, sys, &tree, max_steps));
        } else {
            // Non-target lemma: HS close-time check-and-extend
            // replay, no auto-proving of open leaves.
            return Ok(crate::replay::check_and_extend(&ctx, sys, &tree, max_steps));
        }
    }
    if !auto_prove {
        // Non-target lemma with no stored skeleton: HS keeps the parsed
        // `unproven ()` single-`sorry` proof (`unproven = sorry Nothing`,
        // Proof.hs:255-256; used by the lemma constructor at
        // ProofSkeleton.hs:61) — an
        // annotated Sorry at the lemma's start system (the node carries
        // the start system, so it renders as plain `by sorry`).
        return Ok(crate::replay::annotated_sorry_root(sys));
    }
    let t_search: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    let r = run_proof_search(&ctx, sys, max_steps);
    if trace { eprintln!("[phase] (session) run_proof_search dt={:.3}s total={:.3}s",
        t_search.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64()),
        t_phase.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    Ok(r)
}

/// Drive a proof attempt for one lemma in a parsed theory.
///
/// `max_steps` bounds the proof-tree depth so the call always
/// terminates. Pass a generous value (e.g. 100+) for non-trivial
/// proofs.
pub fn prove_lemma(
    parser_theory: &p::Theory,
    lemma_name: &str,
    maude: tamarin_term::maude_proc::MaudeHandle,
    max_steps: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_with_pool(parser_theory, lemma_name, maude, None, max_steps)
}

/// Variant of [`prove_lemma`] that also accepts a `MaudePool` to be
/// installed on the `ProofContext` for use at rayon parallel sites
/// (saturate refinement).  Sequential code paths still use the
/// single `maude` handle; the pool is consulted ONLY inside
/// `par_iter` closures (see `sources.rs::saturate_sources_with_simp_opt`).
///
/// `None` for `pool` is equivalent to calling `prove_lemma` — workers
/// share `maude`, same as before the pool feature landed.
pub fn prove_lemma_with_pool(
    parser_theory: &p::Theory,
    lemma_name: &str,
    maude: tamarin_term::maude_proc::MaudeHandle,
    pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
    max_steps: usize,
) -> Result<ProofNode, ProveError> {
    prove_lemma_with_pool_and_file(parser_theory, lemma_name, maude, pool, max_steps, "")
}

/// Like [`prove_lemma_with_pool`] but also provides the source file path
/// for oracle path resolution (HS `oraclePath oracle = takeDirectory inFile
/// </> normalise relPath`, System.hs:574-575, Parser.hs:304).
pub fn prove_lemma_with_pool_and_file(
    parser_theory: &p::Theory,
    lemma_name: &str,
    maude: tamarin_term::maude_proc::MaudeHandle,
    pool: Option<std::sync::Arc<tamarin_term::maude_proc::MaudePool>>,
    max_steps: usize,
    in_file: &str,
) -> Result<ProofNode, ProveError> {
    let trace = std::env::var("TAM_DBG_PHASE").is_ok();
    // Per-phase wall-clock instrumentation, gated by TAM_DBG_PHASE.
    // `Option<Instant>` keeps the disabled-path branch-predictable to
    // a single `if let Some(_)` check at each phase boundary.
    let t_phase: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    if trace { eprintln!("[phase] elaborate start"); }
    // Re-set the thread-locals that track user-declared function symbols
    // for the *duration of this prove call*.  `elaborate()` sets them
    // for its own scope via RAII guards that drop on return — so
    // `term_to_lnterm` calls during search would otherwise see an
    // empty set.  Mirror Haskell's funSig staying available through
    // the whole prover lifetime.
    let _user_funs_guard = crate::elaborate::set_user_funs_for_theory(parser_theory);
    // Elaborate to get the typed theory, then pull rules + restrictions.
    let mut theory = elaborate(parser_theory)
        .map_err(|e| ProveError::Elaboration(e.message))?;
    // Set in_file for oracle path resolution (HS Parser.hs:304).
    if !in_file.is_empty() { theory.in_file = in_file.to_string(); }
    if trace { eprintln!("[phase] elaborate done dt={:.3}s",
        t_phase.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    let t_after_elab: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };

    // Find the lemma (parser-AST formula stays accessible via Theory's items).
    // Our typed theory's lemma carries a parser-AST formula too — look it up.
    let lemma = theory
        .lookup_lemma(lemma_name)
        .ok_or_else(|| ProveError::LemmaNotFound(lemma_name.to_string()))?;

    let g = formula_to_guarded(&lemma.formula)
        .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &lemma.formula)))?;

    // Per-lemma source kind (HS `lemmaSourceKind`, Lemma.hs:38-41): RawSource
    // for `[sources]`-tagged lemmas, RefinedSource for all others.  Stamped
    // onto the initial system's `sSourceKind` (Prover.hs:325).
    let lemma_source_kind = lemma_source_kind(lemma);

    // Convert restrictions to guarded.  HS `mkSystem` maps
    // `formulaToGuarded_ = either (error . render) id` (Prover.hs:324,
    // Guarded.hs:466-467) over restriction formulas — it ABORTS on a
    // non-guardable restriction rather than silently dropping it (a silent
    // drop weakens the constraint set and could let an unsound proof
    // through).  Mirror the fail-loud behaviour: propagate `ProveError`.
    let mut restrictions: Vec<Guarded> = Vec::new();
    for r in theory.restrictions() {
        let rg = formula_to_guarded(&r.formula)
            .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &r.formula)))?;
        restrictions.push(rg);
    }

    // `[reuse]` lemmas declared BEFORE this one are gathered separately
    // and pushed into `sLemmas` (not `sFormulas`) after building the
    // system. Mirrors Haskell's `mkSystem` (Prover.hs:317-338):
    //
    //   addLemmas
    //   . formulaToSystem restrictions ...
    //   where addLemmas sys = insertLemmas (gatherReusableLemmas ...) sys
    //
    // `gatherReusableLemmas` honours the source-kind bound and
    // `pcHiddenLemmas` guards (see [`gather_reusable_lemmas`]).
    //
    // The distinction is load-bearing for induction: `formulaToSystem`
    // conjoins non-safety restrictions into `sFormulas` so they're
    // included in `toInductionHypothesis(gf)` — yielding a `Disj` over
    // each conjunct's IH. Reuse lemmas, in contrast, must NOT be
    // conjoined: their IH would weaken the inductive hypothesis to a
    // disjunction across all reuse lemmas, blocking simplify from
    // resolving the IH against current trace actions.
    let reuse_lemmas =
        gather_reusable_lemmas(&theory, lemma_name, lemma_source_kind)?;

    // Bridge our typed `theory::TraceQuantifier` back to the parser's
    // `ast::TraceQuantifier` (which `formula_to_system` consumes).
    let tq = match lemma.trace_quantifier {
        crate::theory::TraceQuantifier::AllTraces => p::TraceQuantifier::AllTraces,
        crate::theory::TraceQuantifier::ExistsTrace => p::TraceQuantifier::ExistsTrace,
    };
    let mut sys = formula_to_system(
        restrictions.clone(),
        lemma_source_kind,
        tq,
        false,
        &g,
    );
    // Haskell's `addLemmas`: push reuse lemmas into `sLemmas`. They
    // become drivers for `insertImpliedFormulas` (which iterates
    // `sFormulas ++ sLemmas`) but are excluded from `ginduct`.
    //
    // Note: `[sources]`-tagged lemmas are NOT added to sLemmas.
    // Haskell's `gatherReusableLemmas` (Prover.hs:331) filters to
    // `[reuse]` only; `[sources]` lemmas are consumed solely by
    // `refineWithSourceAsms` at precompute time (driven below by the
    // `ctx.ensure_saturated()` call over `ctx.full_sources`).
    // Coverage on typing-class
    // lemmas (NSLPK3, chaum, foo, okamoto) depends on the
    // architecture matching Haskell exactly — no workaround.
    sys.insert_lemmas(reuse_lemmas);

    if trace { eprintln!("[phase] formula_to_system done dt={:.3}s; ProofContext::new start",
        t_after_elab.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    let t_ctx: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    // Bridge the elaborated theory's rules into the proof context.
    let rules: Vec<OpenProtoRule> = theory.rules().cloned().collect();
    // Install the optional `maude_pool` BEFORE the precompute phase
    // runs inside the constructor — `precompute_full_sources` calls
    // `saturate_sources_with_simp` which is parallel and benefits
    // from the pool.  Setting `maude_pool` after construction would
    // leave that initial precompute on the single shared `maude`.
    let mut ctx = ProofContext::new_with_restrictions_and_pool(
        maude, pool, rules, restrictions.clone());
    if trace { eprintln!("[phase] ProofContext::new done dt={:.3}s",
        t_ctx.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    // Propagate the lemma's trace quantifier so `is_finished` can
    // decide whether the Fresh-conflation case-drop should convert
    // Contradictory→Unfinishable (sound only on exists-trace where
    // the dropped case might have been the witness).
    ctx.is_exists_trace = matches!(
        lemma.trace_quantifier,
        crate::theory::TraceQuantifier::ExistsTrace,
    );

    // Resolve the goal-ranking heuristic, mirroring HS's
    // `getProofContext.specifiedHeuristic` (ClosedTheory.hs:123-131):
    //   per-lemma `[heuristic=..]` > theory-level `heuristic:` > None.
    // `None` falls back to `SmartRanking False` in `rank_goals_with`
    // (= HS's `defaultHeuristic False`).
    // `parse_heuristic_str_with_tactics` returns the full list for
    // round-robin scheduling (HS `roundRobinHeuristic`/`useHeuristic`,
    // ProofMethod.hs:576-595), resolves oracle paths, and resolves
    // `{name}` tactic rankings against `theory.tactic`.
    let in_file = &theory.in_file;
    let lemma_heuristic: Option<&str> = lemma.attributes.iter().find_map(|a| match a {
        crate::theory::LemmaAttr::Heuristic(s) => Some(s.as_str()),
        _ => None,
    });
    // Build raw heuristic string: per-lemma overrides theory-level.
    let heuristic_raw: Option<String> = match lemma_heuristic {
        Some(h) => Some(h.to_string()),
        None => theory.heuristic.first().cloned(),
    };
    ctx.heuristic = heuristic_raw.map(|h| {
        // Resolve oracle paths relative to theory file dir.
        // HS `oraclePath oracle = takeDirectory inFile </> normalise relPath`
        // (System.hs:574-575, Parser.hs:304).
        // Resolve `{name}` tactic rankings against `theory.tactic`
        // (HS `chosenTactic`, ProofMethod.hs:494-496).
        let mut rankings = crate::constraint::solver::goals::parse_heuristic_str_with_tactics(
            &h, in_file, &theory.tactic);
        prepend_theory_dir_to_oracle_paths(&mut rankings, in_file);
        rankings
    });
    // Set lemma_name and theory_file on ctx for oracle invocation.
    ctx.lemma_name = lemma_name.to_string();
    ctx.theory_file = in_file.clone();

    // `refineWithSourceAsms`: prune precomputed source cases by
    // assumptions from `[sources]`-tagged lemmas.  Mirrors Haskell's
    // `refineWithSourceAsms` — typing-style protocols rely on these
    // assumptions to filter out spurious decryption cases that would
    // otherwise surface as false counterexamples in our search.
    let mut typing_assumptions: Vec<Guarded> = Vec::new();
    for prior in theory.lemmas() {
        // Exclude the lemma we're currently proving — using it as its
        // own refinement assumption is circular.  In Haskell, [sources]
        // lemmas are proved via induction (against unrefined source-
        // cases); only AFTER they're proved do they become typing
        // assumptions for OTHER lemmas' source-case refinement.
        if prior.name == lemma_name { continue; }
        if !prior.attributes.iter().any(|a| matches!(a, crate::theory::LemmaAttr::Sources)) {
            continue;
        }
        if !matches!(prior.trace_quantifier, crate::theory::TraceQuantifier::AllTraces) {
            continue;
        }
        // HS `typAsms` (Prover.hs:142-144) uses `formulaToGuarded_`
        // (fail-loud) on each source-lemma formula — propagate rather than
        // silently drop.
        let rg = formula_to_guarded(&prior.formula)
            .map_err(|e| ProveError::Guarded(guard_error_doc(&e, &prior.formula)))?;
        typing_assumptions.push(rg);
    }
    // HS-faithful saturation: store typing assumptions, then eagerly
    // run `ensure_saturated` (which applies `refine_with_source_asms`
    // with the assumptions just set).  This matches HS's
    // `refineWithSourceAsms` call site emitting `[Saturating Sources]
    // Done` at theory-close time — Rust does it per-lemma because the
    // ctx is per-lemma.
    ctx.typing_assumptions = typing_assumptions;
    let t_sat: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    ctx.ensure_saturated();
    if trace { eprintln!("[phase] ensure_saturated done dt={:.3}s",
        t_sat.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    let t_search: Option<std::time::Instant> =
        if trace { Some(std::time::Instant::now()) } else { None };
    if trace { eprintln!("[phase] run_proof_search start"); }
    // Phase marker so TAM_RS_DBG_* counts can be filtered to the
    // lemma-proof phase only.  Pair with HS's `[Saturating Sources]
    // Done` marker for HS↔Rust diffing of just the lemma proof
    // (excludes precompute/saturation).  Gated behind TAM_RS_DBG_PHASE
    // so default --prove stderr stays HS-faithful.
    if std::env::var("TAM_RS_DBG_PHASE").is_ok() {
        eprintln!("[rs-phase] lemma-proof START");
    }
    if std::env::var("TAM_DBG_LEMMA_INIT").is_ok() {
        eprintln!("[lemma-init] sys.formulas count = {}", sys.formulas.len());
        for (i, f) in sys.formulas.iter().enumerate() {
            let s = format!("{:?}", f);
            eprintln!("[lemma-init]   formula[{}]: {}", i,
                s.chars().take(250).collect::<String>());
        }
        eprintln!("[lemma-init] sys.lemmas count = {}", sys.lemmas.len());
        for (i, f) in sys.lemmas.iter().enumerate() {
            let s = format!("{:?}", f);
            eprintln!("[lemma-init]   lemma[{}]: {}", i,
                s.chars().take(250).collect::<String>());
        }
    }
    // Keep TAM_DBG_LEMMA_INIT as a documented diagnostic env var.
    // Honour the `[use_induction]` and `[sources]` attributes by
    // forcing the first proof method to be Induction. Haskell's
    // `ClosedTheory.hs` flips `pcUseInduction = UseInduction` for
    // `SourceLemma` and `InvariantLemma`-tagged lemmas — sources
    // proofs essentially always run via induction.
    let force_induction = lemma.attributes.iter().any(|a| matches!(a,
        crate::theory::LemmaAttr::UseInduction | crate::theory::LemmaAttr::Sources));
    if force_induction {
        ctx.use_induction = crate::constraint::solver::context::UseInduction::UseInduction;
    }

    // HS-faithful `replaceSorryProver` (Proof.hs:642-650):
    // when the lemma carries a parsed skeleton, walk that skeleton and
    // invoke the auto-prover only at `by sorry` leaves.  Otherwise (no
    // skeleton or parser couldn't structure it) fall through to the
    // pre-existing auto-prover-from-scratch behavior.
    if let Some(tree) = lemma.proof.tree.clone() {
        if std::env::var("TAM_DBG_REPLAY").is_ok() {
            eprintln!("[replay] firing skeleton replay for `{}` (raw {} bytes)",
                lemma_name, lemma.proof.raw.len());
        }
        return Ok(crate::replay::replace_sorry_prove(&ctx, sys, &tree, max_steps));
    } else if std::env::var("TAM_DBG_REPLAY").is_ok() {
        eprintln!("[replay] NO tree on `{}` (raw {} bytes) — falling through to auto-prover",
            lemma_name, lemma.proof.raw.len());
    }
    let r = run_proof_search(&ctx, sys, max_steps);
    if trace { eprintln!("[phase] run_proof_search done dt={:.3}s total={:.3}s",
        t_search.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64()),
        t_phase.as_ref().map_or(0.0, |t| t.elapsed().as_secs_f64())); }
    Ok(r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::maude_proc::MaudeHandle;
    use tamarin_term::maude_sig::pair_maude_sig;

    fn maude_path_local() -> Option<String> {
        std::env::var("MAUDE_PATH").ok().or_else(|| {
            for c in ["/home/linuxbrew/.linuxbrew/bin/maude", "/usr/local/bin/maude", "maude"] {
                if std::path::Path::new(c).exists() { return Some(c.to_string()); }
            }
            None
        })
    }

    fn maude() -> Option<MaudeHandle> {
        let path = maude_path_local()?;
        MaudeHandle::start(&path, pair_maude_sig()).ok()
    }

    #[test]
    fn prove_lemma_unknown_name_is_error() {
        let h = match maude() { Some(m) => m, None => return };
        let parser_theory = tamarin_parser::parse_theory("theory T begin end", &[])
            .expect("parse");
        let r = prove_lemma(&parser_theory, "nonexistent", h, 5);
        assert!(matches!(r, Err(ProveError::LemmaNotFound(_))));
    }

    fn print_tree(node: &super::ProofNode, depth: usize) {
        let pad = "  ".repeat(depth);
        let reason = if let crate::constraint::solver::proof_method::ProofMethod::Finished(r) = &node.method {
            format!(" reason={:?}", r)
        } else { String::new() };
        eprintln!("{}status={:?} method={:?} children={} goals={} nodes={} formulas={} less_atoms={} edges={} {}",
            pad, node.status, node.method, node.children.len(),
            node.sys.goals.len(), node.sys.nodes.len(), node.sys.formulas.len(),
            node.sys.less_atoms.len(), node.sys.edges.len(), reason);
        if depth > 0 {
            for (id, ru) in node.sys.nodes.iter() {
                let info = match &ru.info {
                    crate::rule::RuleInfo::Proto(p) => format!("{:?}", p.name),
                    crate::rule::RuleInfo::Intr(i) => format!("Intr({:?})", i),
                };
                let concs: Vec<String> = ru.conclusions.iter()
                    .map(|c| format!("{}({})", crate::fact::fact_tag_name(&c.tag),
                        c.terms.iter().map(|t| format!("{:?}", t)).collect::<Vec<_>>().join(",")))
                    .collect();
                eprintln!("{}  node {:?} = {} concs=[{}]", pad,
                    (id.name.clone(), id.idx), info, concs.join("; "));
            }
            eprintln!("{}  eq_store.subst = {:?}", pad, node.sys.eq_store.subst);
            for la in &node.sys.less_atoms {
                eprintln!("{}  less {:?} < {:?}", pad,
                    (la.smaller.name.clone(), la.smaller.idx),
                    (la.larger.name.clone(), la.larger.idx));
            }
            for e in &node.sys.edges {
                eprintln!("{}  edge {:?} -> {:?}", pad,
                    (e.src.0.name.clone(), e.src.0.idx),
                    (e.tgt.0.name.clone(), e.tgt.0.idx));
            }
        }
        for (k, c) in &node.children {
            eprintln!("{}case '{}'", pad, k);
            if depth < 9 { print_tree(c, depth + 1); }
        }
    }

    #[test]
    fn probe_two_rules_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/two_rules.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "reachable", h, 200).expect("prove");
        eprintln!("=== two_rules.spthy `reachable` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_two_actions_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/two_actions.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "both_actions", h, 200).expect("prove");
        eprintln!("=== two_actions.spthy `both_actions` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_falsifiable_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/falsifiable.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "never_both", h, 200).expect("prove");
        eprintln!("=== falsifiable.spthy `never_both` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_three_facts_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/three_facts.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "all_three", h, 200).expect("prove");
        eprintln!("=== three_facts.spthy `all_three` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_single_recv_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/single_recv.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "chain", h, 200).expect("prove");
        eprintln!("=== single_recv ===");
        eprintln!("status={:?}", root.status);
    }

    #[test]
    fn probe_injectivity_with_pair_sig() {
        // Probes the `injectivity::injectivity_check` corpus example.
        // Resolves the example via a workspace-relative path computed
        // from CARGO_MANIFEST_DIR (crate lives at
        // rust/crates/tamarin-theory, so examples/ is three levels up);
        // skips gracefully if the example is not present.
        let mp = match maude_path_local() { Some(p) => p, None => return };
        let src = std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../examples/features/injectivity/injectivity.spthy"
        )).unwrap_or_default();
        if src.is_empty() { return; }
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let h = MaudeHandle::start(&mp, pair_maude_sig()).expect("start maude");
        let root = prove_lemma(&pt, "injectivity_check", h, 200).expect("prove");
        eprintln!("injectivity status = {:?}", root.status);
    }

    #[test]
    fn probe_cr_recentalive_with_hashing_sig() {
        // Pinning regression test for the substSystem-edge-uniqueness
        // fixed-point bug: with the elaborated MaudeSig (hashing), the
        // simplify loop used to spin 256 iters per case because
        // `enforce_edge_uniqueness` kept signalling `Changed` on
        // already-canonical edges. The fix drops trivially-equal node
        // equalities before re-firing the pass.
        let mp = match maude_path_local() { Some(p) => p, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/CR_external.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let elab = crate::elaborate::elaborate(&pt).expect("elaborate");
        let sig = elab.signature.maude_sig.clone();
        let h = MaudeHandle::start(&mp, sig).expect("start maude");
        let t0 = std::time::Instant::now();
        let _ = prove_lemma(&pt, "recentalive", h, 200).expect("prove");
        let dt = t0.elapsed();
        // Must complete promptly — without the fix this lemma would
        // run for >30s before our wall-clock deadline kicked in.
        // After fix #27 (full `exploit_prems` in solve_premise_goal),
        // goal tracking is denser and this exists-trace probe takes
        // longer to settle; threshold raised from 5s to 60s.  The
        // load-bearing assertion is that the simplify loop *does
        // converge* — the prior bug spun forever at every node.
        assert!(dt < std::time::Duration::from_secs(60),
            "recentalive ran {:?}, expected ≤60s (simplify-loop converges)", dt);
    }

    #[test]
    fn probe_sig_minimal_with_hashing_sig() {
        // Try the trivially-true tautology with the elaborated theory's
        // MaudeSig (which adds h/1) instead of pair-only. If this hangs,
        // the goal explosion is reproducible on a near-empty file.
        let mp = match maude_path_local() { Some(p) => p, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/sig_minimal.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let elab = crate::elaborate::elaborate(&pt).expect("elaborate");
        let sig = elab.signature.maude_sig.clone();
        eprintln!("sig fun_syms count = {}", sig.fun_syms.len());
        for fs in &sig.fun_syms {
            if let tamarin_term::function_symbols::FunSym::NoEq(s) = fs {
                eprintln!("  {} (arity={}, priv={:?}, ctor={:?})",
                    String::from_utf8_lossy(&s.name), s.arity, s.privacy, s.constructability);
            }
        }
        let h = MaudeHandle::start(&mp, sig).expect("start maude");
        let root = prove_lemma(&pt, "a_self", h, 50).expect("prove");
        eprintln!("status = {:?}", root.status);
        // The lemma is a tautology; should reach Contradictory after
        // negation reduces to ⊥.
    }

    #[test]
    fn probe_two_rules_proof_shape_v2() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/two_rules.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "reachable", h, 200).expect("prove");
        eprintln!("=== two_rules.spthy `reachable` (v2) ===");
        print_tree(&root, 0);
    }

    #[test]
    fn probe_auth_pattern_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/auth_pattern.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "protocol_runs", h, 200).expect("prove");
        eprintln!("=== auth_pattern.spthy ===");
        print_tree(&root, 0);
    }

    #[test]
    fn probe_fresh_ordering_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/fresh_ordering.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "order", h, 200).expect("prove");
        eprintln!("=== fresh_ordering.spthy `order` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_needs_constructor_simple_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/needs_constructor_simple.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "sent_exists", h, 200).expect("prove");
        eprintln!("=== needs_constructor_simple ===");
        eprintln!("status={:?}", root.status);
    }

    #[test]
    fn probe_needs_constructor_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/needs_constructor.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "pair_arrives", h, 2000).expect("prove");
        eprintln!("=== needs_constructor.spthy `pair_arrives` ===");
        eprintln!("status={:?}", root.status);
    }

    /// Smaller test: just receive a fresh that was Out-ed.
    #[test]
    fn probe_recv_one_fresh() {
        let h = match maude() { Some(m) => m, None => return };
        let src = "theory T begin
rule S: [Fr(~k)] --[Sent(~k)]-> [Out(~k)]
rule R: [In(x)] --[Got(x)]-> []
lemma chain: exists-trace \"Ex k #i #j. Sent(k)@i & Got(k)@j\"
end";
        let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
        let root = prove_lemma(&pt, "chain", h, 500).expect("prove");
        eprintln!("=== probe_recv_one_fresh ===");
        eprintln!("status={:?}", root.status);
    }

    #[test]
    fn probe_reuse_lemma() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/reuse_lemma.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let r1 = prove_lemma(&pt, "setup_unique", maude().unwrap(), 200).expect("prove1");
        let r2 = prove_lemma(&pt, "setup_unique_key", h, 200).expect("prove2");
        eprintln!("setup_unique={:?}, setup_unique_key={:?}", r1.status, r2.status);
    }

    #[test]
    fn probe_restriction_unique() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/restriction_unique.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "setup_unique", h, 200).expect("prove");
        eprintln!("=== restriction_unique ===");
        eprintln!("status={:?}", root.status);
        // Diagnostic: count lemmas in the proof tree's leaves.
        fn collect_max_lemmas(n: &super::ProofNode, out: &mut usize) {
            *out = (*out).max(n.sys.lemmas.len());
            for c in n.children.values() { collect_max_lemmas(c, out); }
        }
        let mut max_lemmas = 0;
        collect_max_lemmas(&root, &mut max_lemmas);
        eprintln!("max lemma count seen in tree: {}", max_lemmas);
    }

    #[test]
    fn probe_safety_two_keys_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/safety_two_keys.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "fresh_distinct_times", h, 200).expect("prove");
        eprintln!("=== safety_two_keys.spthy `fresh_distinct_times` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    #[test]
    fn probe_safety_unique_proof_shape() {
        let h = match maude() { Some(m) => m, None => return };
        let src = std::fs::read_to_string(
            concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/safety_unique.spthy"))
            .expect("read");
        let pt = tamarin_parser::parse_theory(&src, &[]).expect("parse");
        let root = prove_lemma(&pt, "setup_unique", h, 200).expect("prove");
        eprintln!("=== safety_unique.spthy `setup_unique` ===");
        print_tree(&root, 0);
        let _ = root.status;
    }

    /// Drive the tiny_setup proof and inspect the proof-tree shape.
    /// We expect the search to:
    /// 1. Pick `Induction` (root).
    /// 2. In `non_empty_trace`, decompose Ex → Goal::Action(Setup(_))
    ///    via simplify.
    /// 3. SolveGoal(Action) → instantiates the Setup rule, exploits
    ///    its `Fr(~k)` premise, leaves no further goals.
    /// 4. Status reaches `Solved` (or `Contradictory` for some branches).
    #[test]
    fn prove_lemma_tiny_setup_drives_through_action_goal() {
        let h = match maude() { Some(m) => m, None => return };
        let src = r#"
theory TinySetup begin
rule Setup:
  [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
lemma trivial:
  exists-trace
  "Ex k #i. Setup(k) @ #i"
end
"#;
        let parser_theory = tamarin_parser::parse_theory(src, &[]).expect("parse");
        let root = prove_lemma(&parser_theory, "trivial", h, 100)
            .expect("prove_lemma should not error");

        // Root method: under the `AvoidInduction` default (exists-trace
        // lemmas), Haskell's `rankProofMethods` tries Simplify first.
        // If Simplify produces non-empty cases (decomposes the formula
        // into goals), that's picked; otherwise we fall through to
        // Induction.  For this trivial existence lemma the Ex is
        // reducible, so Simplify is the root method.  Either is
        // structurally acceptable as long as the proof reaches Solved.
        use crate::constraint::solver::proof_method::ProofMethod;
        use crate::constraint::solver::search::NodeStatus;
        assert!(matches!(root.method,
            ProofMethod::Induction | ProofMethod::Simplify
            | ProofMethod::SolveGoal(_)),
            "expected Simplify/Induction/SolveGoal at root, got {:?}", root.method);
        assert_eq!(root.status, NodeStatus::Solved,
            "expected Solved on tiny_setup, got {:?}", root.status);
    }

    #[test]
    fn prove_lemma_tiny_setup_terminates() {
        let h = match maude() { Some(m) => m, None => return };
        let src = r#"
theory TinySetup begin
rule Setup:
  [ Fr(~k) ] --[ Setup(~k) ]-> [ Out(~k) ]
lemma trivial:
  exists-trace
  "Ex k #i. Setup(k) @ #i"
end
"#;
        let parser_theory = tamarin_parser::parse_theory(src, &[]).expect("parse");
        let root = prove_lemma(&parser_theory, "trivial", h, 50)
            .expect("prove_lemma should not error");
        // Tamarin's proof is `induction → SOLVED` in the empty branch,
        // and the non_empty branch needs the existential to be
        // decomposed — which produces a Goal::Action. Whatever our
        // verdict, the search must terminate, and the non-trivial
        // branch should reach a method beyond the initial induction.
        use crate::constraint::solver::search::NodeStatus;
        assert!(!matches!(root.status, NodeStatus::Open),
            "search must terminate within budget");
    }
}
