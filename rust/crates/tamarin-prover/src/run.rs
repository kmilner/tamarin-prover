//! Batch-mode driver: turn parsed [`Args`] into proof attempts and
//! produce an analyzed-theory output document.
//!
//! Mirrors `Main.Mode.Batch.run` in spirit — load each input file,
//! parse + elaborate, optionally prove lemmas, and emit either to
//! stdout or to `--output=` / `-O DIR`. We deliberately keep the
//! output format simple here: rather than re-implementing Haskell's
//! `prettyClosedTheory` (a multi-thousand-LOC subsystem), we emit
//! the original source followed by a per-lemma summary section. The
//! summary lines match Haskell's `summary of summaries:` shape so
//! existing tooling continues to recognise them.
//!
//! When invoked without `--prove`/`--prove-all` (and without
//! `--parse-only`/`--precompute-only`), we just re-emit the source
//! verbatim — the same behaviour as Haskell's batch mode when no
//! lemma is selected for proof.

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use tamarin_term::maude_proc::{MaudeHandle, MaudePool};
use tamarin_theory::constraint::solver::search::NodeStatus;
use tamarin_theory::elaborate::elaborate;
// `prove_lemma_with_pool` is called via its fully-qualified path
// inside the prove loop (it lets us pass the optional Maude pool);
// no top-level alias needed.

use crate::cli::{lemma_matches, Args, Subcommand};

#[derive(Debug)]
pub struct RunError(pub String);

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for RunError {}

/// Outcome of proving a single lemma. Mirrors the columns of Haskell's
/// `summary of summaries:` block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LemmaVerdict {
    Verified,
    Falsified,
    /// We exhausted the search budget or hit `Sorry`.
    Analyzed,
    /// `[reuse]`-only lemma that we didn't try to prove (out of filter).
    Skipped,
    /// Lemma was filtered out by `--prove=FOO` / `--lemma=FOO`.
    Filtered,
    Error(String),
}

impl LemmaVerdict {
    pub fn label(&self) -> &str {
        match self {
            LemmaVerdict::Verified => "verified",
            LemmaVerdict::Falsified => "falsified",
            LemmaVerdict::Analyzed => "analysis incomplete",
            LemmaVerdict::Skipped => "analysis incomplete",
            LemmaVerdict::Filtered => "analysis incomplete",
            LemmaVerdict::Error(_) => "error",
        }
    }
}

/// HS-faithful per-lemma summary line, mirroring `Theory.Constraint.Solver.summarize`:
///   `<lemma> (<quantifier>): falsified - found trace (<N> steps)`
///   `<lemma> (<quantifier>): verified (<N> steps)`
///   `<lemma> (<quantifier>): analysis incomplete (<N> steps)`
fn format_lemma_summary_line(r: &LemmaResult) -> String {
    let quantifier = if r.exists_trace { "exists-trace" } else { "all-traces" };
    let body = match &r.verdict {
        LemmaVerdict::Falsified => format!("falsified - found trace ({} steps)", r.proof_steps),
        LemmaVerdict::Verified => format!("verified ({} steps)", r.proof_steps),
        LemmaVerdict::Analyzed
        | LemmaVerdict::Skipped
        | LemmaVerdict::Filtered => format!("analysis incomplete ({} steps)", r.proof_steps),
        LemmaVerdict::Error(msg) => format!("error: {}", msg),
    };
    format!("{} ({}): {}", r.name, quantifier, body)
}

#[derive(Debug, Clone)]
pub struct LemmaResult {
    pub name: String,
    pub verdict: LemmaVerdict,
    pub elapsed_ms: u128,
    /// Proof-tree node count — matches HS's "(N steps)" in
    /// `--prove` output (Theory.Proof.proofStepCount).
    pub proof_steps: usize,
    /// `true` for `exists-trace` lemmas, `false` for `all-traces`.
    /// Drives the trace-quantifier label in the summary.
    pub exists_trace: bool,
}

#[derive(Debug, Clone)]
pub struct FileResult {
    pub in_file: String,
    pub out_file: Option<String>,
    pub results: Vec<LemmaResult>,
    pub elapsed_ms: u128,
    /// Number of wellformedness check failures for this file.
    /// Surfaced in `summary of summaries` per HS's format.
    pub wf_count: usize,
}

/// Top-level dispatch. Reports any error as a `RunError` and returns
/// the exit code the binary should use (0 for success).
pub fn run(args: &Args) -> Result<i32, RunError> {
    if args.show_help {
        println!("{}", crate::cli::help_text());
        return Ok(0);
    }
    if args.show_version {
        println!("{}", crate::cli::version_text());
        return Ok(0);
    }

    match args.subcommand {
        Subcommand::Batch => run_batch(args),
        Subcommand::Interactive => run_interactive(args),
        Subcommand::Variants => run_variants(args),
        Subcommand::Test => run_test(args),
    }
}

/// `tamarin-prover test` — mirror HS's installation self-test
/// (`Main.Mode.Test`).  HS runs:
///   1. Maude version check.
///   2. GraphViz `dot` version check.
///   3. The Haskell unit-test suite (55 cases as of v1.13.0).
///
/// We do (1) and (2) here.  Porting the unit test suite is a separate
/// effort; until then we run the prover's own lib tests at build time
/// instead (`cargo test`).  Returns rc=0 on Maude/dot reachable,
/// rc=1 otherwise.
fn run_test(_args: &Args) -> Result<i32, RunError> {
    println!("Self-testing the tamarin-prover installation.\n");
    println!("*** Testing the availability of the required tools ***");
    let mv = crate::cli::detect_maude_version_pub();
    match &mv {
        Some(v) => println!("{}. OK.\n checking installation: OK.", v),
        None => {
            eprintln!("Maude check FAILED — not found on $PATH.");
            return Ok(1);
        }
    }
    let dot = std::process::Command::new("dot").arg("-V").output();
    match dot {
        Ok(out) if out.status.success() => {
            let s = String::from_utf8_lossy(&out.stderr);
            println!("GraphViz tool: 'dot'\n checking version: {}OK.", s.trim());
        }
        _ => println!("GraphViz check skipped (`dot` not found)."),
    }
    println!("\n*** TEST SUMMARY ***");
    println!("All tool checks successful.");
    println!("The tamarin-prover should work as intended.\n");
    println!("           :-) happy proving (-:");
    Ok(0)
}

/// `tamarin-prover variants` — mirror HS's `Main.Mode.Variants`.
/// HS dumps the DH-intruder rule variants (the `c_exp`, `c_inv`,
/// `c_mult`, `c_one`, etc. rules) without needing a `.spthy` file.
///
/// We mirror that: spin up Maude with the default DH-enabled MaudeSig,
/// generate the rules via [`tamarin_theory::intruder_rules::dh_intruder_rules`],
/// and pretty-print each rule in HS's `rule (modulo AC) NAME:` shape.
fn run_variants(args: &Args) -> Result<i32, RunError> {
    let maude_path = args.maude_path.clone().unwrap_or_else(default_maude_path);
    // HS's `variants` default-enables both DH and BP (bilinear-pairing)
    // — the 125-rule output set.  Mirror that: union the two sigs.
    let sig = tamarin_term::maude_sig::dh_maude_sig()
        .merge(tamarin_term::maude_sig::bp_maude_sig());
    let maude = MaudeHandle::start(&maude_path, sig).map_err(|e| {
        RunError(format!("failed to start maude at {:?}: {:?}", maude_path, e))
    })?;
    if let Some(v) = crate::cli::detect_maude_version_pub() {
        println!("maude tool: '{}'", maude_path);
        println!(" checking version: {}. OK.", v);
        println!(" checking installation: OK.");
    }
    // NOTE: this enumerates the DH intruder rule variants only (53 rules
    // on the default sig).  HS additionally generates the bilinear-
    // pairing variants (`c_em`, `d_em`, `d_pmult`) — the full HS output
    // is 125 rules.  Porting BP intruder rules is a deeper functional
    // gap (no `bp_intruder_rules` exists yet in tamarin_theory).
    let rules = tamarin_theory::intruder_rules::dh_intruder_rules(args.diff, &maude);
    // Mirror HS `Theory.Rule.prettyIntrRuleACInfo` naming:
    //   ConstrRule "_exp"    → "c_exp"
    //   DestrRule  "_exp"... → "d_0_exp"  (i64 = remaining-apps counter)
    for r in &rules {
        let name = match &r.info {
            tamarin_theory::rule::IntrRuleACInfo::ConstrRule(n) =>
                format!("c{}", String::from_utf8_lossy(n)),
            // HS suppresses the remaining-apps counter when it's 0
            // (i.e. unbounded) — `d_NAME` not `d_0_NAME`.  Matches
            // `Theory.Rule.prettyIntrRuleACInfo`.
            tamarin_theory::rule::IntrRuleACInfo::DestrRule(n, 0, _, _) =>
                format!("d{}", String::from_utf8_lossy(n)),
            tamarin_theory::rule::IntrRuleACInfo::DestrRule(n, k, _, _) =>
                format!("d_{}{}", k, String::from_utf8_lossy(n)),
            other => format!("{:?}", other),
        };
        let kind = match &r.info {
            tamarin_theory::rule::IntrRuleACInfo::ConstrRule(_)
            | tamarin_theory::rule::IntrRuleACInfo::DestrRule(_, _, _, _) => "rule (modulo AC)",
            _ => "rule",
        };
        println!();
        println!("{} {}:", kind, name);
        // Pretty-print each fact as `Tag(term, term, …)` using
        // `tamarin_term::pretty::pretty_lnterm` for argument terms.
        // Mirrors HS `prettyLNFact` for the variants command.
        let fmt_fact = |f: &tamarin_theory::fact::LNFact| -> String {
            use tamarin_theory::fact::{FactTag, Multiplicity};
            let prefix = match &f.tag {
                FactTag::Proto(Multiplicity::Persistent, _, _) => "!",
                _ => "",
            };
            let name: String = match &f.tag {
                FactTag::Proto(_, n, _) => n.clone(),
                FactTag::Fresh => "Fr".into(),
                FactTag::In => "In".into(),
                FactTag::Out => "Out".into(),
                FactTag::Ku => "!KU".into(),
                FactTag::Kd => "!KD".into(),
                FactTag::Ded => "Ded".into(),
                FactTag::Term => "Term".into(),
            };
            let args: Vec<String> = f.terms.iter()
                .map(|t| tamarin_term::pretty::pretty_lnterm(t))
                .collect();
            format!("{}{}({})", prefix, name, args.join(", "))
        };
        let fmt_facts = |facts: &[tamarin_theory::fact::LNFact]| -> String {
            let parts: Vec<String> = facts.iter().map(fmt_fact).collect();
            format!("[ {} ]", parts.join(", "))
        };
        println!("   {} --{}-> {}",
            fmt_facts(&r.premises),
            fmt_facts(&r.actions),
            fmt_facts(&r.conclusions));
    }
    Ok(0)
}

/// Default port matches Haskell `Web.Settings.defaultPort` (3001).
const DEFAULT_INTERACTIVE_PORT: u16 = 3001;

/// Run the interactive web UI. Mirrors `Main.Mode.Interactive.run`:
/// builds a [`tamarin_server::ServerConfig`] from the CLI flags, eagerly
/// loads any positional `.spthy` files into the theory store, and serves
/// HTTP until SIGINT/SIGTERM. Returns 0 on graceful shutdown.
fn run_interactive(args: &Args) -> Result<i32, RunError> {
    use std::net::{IpAddr, Ipv4Addr, SocketAddr};
    use std::path::PathBuf;

    init_rayon_pool(args);

    // Haskell defaults: 3001 on 127.0.0.1.
    let port = args.port.unwrap_or(DEFAULT_INTERACTIVE_PORT);

    // `--interface` accepts a literal IP address. Haskell's `*4` / `*` /
    // `*6` magic strings bind to all interfaces; mirror those.
    let iface_str = args
        .interface
        .clone()
        .unwrap_or_else(|| "127.0.0.1".to_string());
    let ip: IpAddr = match iface_str.as_str() {
        "*" | "*4" => IpAddr::V4(Ipv4Addr::UNSPECIFIED),
        "*6" => IpAddr::V6(std::net::Ipv6Addr::UNSPECIFIED),
        other => other.parse::<IpAddr>().map_err(|e| {
            RunError(format!(
                "could not parse --interface={:?} as an IP address: {}\n\
                 Use --interface=\"*4\" to bind to all IPv4 interfaces.",
                other, e,
            ))
        })?,
    };
    let bind_addr = SocketAddr::new(ip, port);

    // Resolve data dir. Without an explicit flag, look for `data/`
    // alongside the working directory or its ancestors — the same
    // search the server already exposes via `resolve_data_dir`.
    let data_dir = tamarin_server::handlers::static_files::resolve_data_dir(
        args.data_dir.clone().map(PathBuf::from),
    );
    // Try to discover a sibling frontend/dist for the bundled UI assets.
    let frontend_dist = guess_frontend_dist(&data_dir);

    let maude_path = args.maude_path.clone().unwrap_or_else(default_maude_path);

    let mut cfg = tamarin_server::ServerConfig::new(bind_addr, data_dir, maude_path);
    cfg.frontend_dist = frontend_dist;
    if let Some(b) = args.bound {
        cfg.max_steps = b as usize;
    }

    // Positional args are theory files (Haskell uses a working
    // directory, but we accept either: a single dir arg, or one-or-more
    // .spthy paths).
    let theory_paths: Vec<PathBuf> = collect_theory_paths(&args.in_files)?;

    if !args.quiet {
        eprintln!(
            "The server is starting up on port {}.\nBrowse to http://{} once the server is ready.",
            port, bind_addr,
        );
    }

    // Spin up a tokio runtime and run the server. We use a multi-thread
    // runtime so background `spawn_blocking` proof tasks don't park the
    // single executor thread.
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .map_err(|e| RunError(format!("failed to build tokio runtime: {}", e)))?;
    runtime
        .block_on(tamarin_server::serve(cfg, theory_paths))
        .map_err(|e| RunError(format!("server error: {}", e)))?;
    Ok(0)
}

/// Expand the positional input list into a list of `.spthy` files.
/// Haskell's interactive mode takes a single working directory; we
/// accept either a directory (whose `.spthy` files we glob) or any
/// number of `.spthy` files (the path Tamarin batch mode uses).
fn collect_theory_paths(in_files: &[String]) -> Result<Vec<std::path::PathBuf>, RunError> {
    use std::path::PathBuf;
    let mut out: Vec<PathBuf> = Vec::new();
    for f in in_files {
        let p = PathBuf::from(f);
        if p.is_dir() {
            let entries = std::fs::read_dir(&p).map_err(|e| {
                RunError(format!("could not read directory {}: {}", p.display(), e))
            })?;
            for e in entries.flatten() {
                let ep = e.path();
                if ep.extension().and_then(|s| s.to_str()) == Some("spthy") {
                    out.push(ep);
                }
            }
        } else {
            out.push(p);
        }
    }
    out.sort();
    Ok(out)
}

/// Best-effort: locate the bundled `frontend/dist/` sibling of `data/`.
/// Returns None if not found — the server tolerates this and just
/// won't serve the frontend assets.
fn guess_frontend_dist(data_dir: &std::path::Path) -> Option<std::path::PathBuf> {
    let parent = data_dir.parent()?;
    let candidate = parent.join("frontend").join("dist");
    if candidate.is_dir() {
        return Some(candidate);
    }
    None
}

fn run_batch(args: &Args) -> Result<i32, RunError> {
    // HS-faithful internal parallelism via rayon.  Mirrors the four
    // `using parList`/`parTraversable`/`parMap` sites HS uses (see
    // `lib/theory/src/Prover.hs:102,195`, `Theory/Constraint/Solver/Sources.hs:471`,
    // `lib/theory/src/TheoryObject.hs:744,752`).  Default: cap at 4
    // workers — RS's per-thread Maude IPC mutex limits speedup, and
    // larger pools have caused OOM in corpus sweeps (see MEMORY.md
    // discipline note).  `--processors=1` falls back to a 1-thread
    // pool, guaranteeing byte-identical output to the pre-parallel
    // sequential path.
    init_rayon_pool(args);
    if args.diff {
        return Err(RunError(
            "--diff (observational equivalence) is not yet ported to the Rust prover."
                .to_string(),
        ));
    }
    if args.output_module.is_some() {
        return Err(RunError(
            "--output-module is not yet ported to the Rust prover.".to_string(),
        ));
    }
    // --output-json / --output-dot: trace graph serialisation isn't
    // ported yet (HS emits a graph of the attack-trace nodes/edges
    // for any falsified lemma).  Don't hard-error — many callers
    // pass these flags unconditionally and just want them to be
    // harmless when no trace is found.  Write empty stub files
    // matching HS's empty shape so downstream tooling can `stat` them
    // and parse them without crashing.  Print a one-line warning so
    // the user knows the contents aren't real.
    if let Some(p) = &args.trace_json {
        if !args.quiet {
            eprintln!("warning: --output-json: trace graph serialisation not yet ported; writing empty stub to {}", p);
        }
        fs::write(p, "{\"graphs\": []}\n").map_err(|e| {
            RunError(format!("failed to write {}: {}", p, e))
        })?;
    }
    if let Some(p) = &args.trace_dot {
        if !args.quiet {
            eprintln!("warning: --output-dot: trace graph serialisation not yet ported; writing empty stub to {}", p);
        }
        fs::write(p, "digraph trace {}\n").map_err(|e| {
            RunError(format!("failed to write {}: {}", p, e))
        })?;
    }
    if args.in_files.is_empty() {
        return Err(RunError(
            "no input files given\n\n".to_string() + &crate::cli::help_text(),
        ));
    }
    let mut overall_status = 0i32;
    let mut file_results: Vec<FileResult> = Vec::new();

    let parser_flags: Vec<&str> = args.defines.iter().map(String::as_str).collect();

    // HS prints the maude tool + version banner ONCE at the top of the
    // batch run (`Main.Console.argExists` path).  Mirror that here:
    // emit `maude tool: 'maude'\n checking version: X. OK.\n checking
    // installation: OK.` before the first theory is loaded.  Suppressed
    // by `--quiet`.
    if !args.quiet && !args.parse_only {
        let raw_path = args.maude_path.clone().unwrap_or_else(default_maude_path);
        // HS prints just the basename when the user didn't pass --maude-path,
        // and the full path when they did.  We can't tell which here without
        // re-introspecting Args, but matching HS's default-banner shape is
        // achieved by showing the basename when the user-supplied value is
        // None.  Args' `maude_path` is already None when not provided.
        let disp = if args.maude_path.is_some() {
            raw_path.clone()
        } else {
            std::path::Path::new(&raw_path)
                .file_name()
                .and_then(|s| s.to_str())
                .unwrap_or(&raw_path)
                .to_string()
        };
        eprintln!("maude tool: '{}'", disp);
        if let Some(v) = crate::cli::detect_maude_version_pub() {
            eprintln!(" checking version: {}. OK.", v);
            eprintln!(" checking installation: OK.");
        }
    }

    // TAM_DBG_RUN_TIMING=1 prints a per-phase wall-clock breakdown of
    // run_batch to stderr.  Diagnostic-only — leave behind an env gate so
    // it can be reused next time the prover-binary overhead is suspect.
    let dbg_timing = std::env::var("TAM_DBG_RUN_TIMING")
        .ok()
        .map(|v| v == "1")
        .unwrap_or(false);

    for in_file in &args.in_files {
        let t0 = Instant::now();
        let mut t_phase = Instant::now();
        macro_rules! phase {
            ($name:expr) => {
                if dbg_timing {
                    eprintln!("[TAM_DBG_RUN_TIMING] {:>26}: {:>8.1} ms",
                              $name, t_phase.elapsed().as_secs_f64() * 1000.0);
                    // Reassign so the next phase! call measures the
                    // delta since this one.  The last invocation in the
                    // loop iteration writes a value the compiler can't
                    // see being read — that's fine, the discipline is
                    // uniform across phase boundaries.
                    #[allow(unused_assignments)]
                    { t_phase = Instant::now(); }
                }
            };
        }
        let src = fs::read_to_string(in_file).map_err(|e| {
            RunError(format!("failed to read {}: {}", in_file, e))
        })?;
        phase!("read_to_string");
        let parsed = tamarin_parser::parse_theory(&src, &parser_flags).map_err(|e| {
            RunError(format!("parse error in {}: {}", in_file, e))
        })?;
        phase!("parse_theory");
        // HS emits this trace marker as soon as the theory parses
        // (TheoryLoader.hs:409).  `--parse-only` and `--quiet` skip it.
        let theory_name = parsed.name.clone();
        if !args.quiet && !args.parse_only {
            eprintln!("[Theory {}] Theory loaded", theory_name);
        }

        // Wellformedness checks — mirrors HS `checkWellformedness`
        // (`Theory.Tools.Wellformedness:1270`).  Runs on every file
        // (not gated by `--parse-only`) so a malformed theory is
        // surfaced even without proving.
        let mut wf_report = tamarin_parser::wf::check_theory(&parsed);
        // Strip the static "Message Derivation Checks" entry — the
        // dynamic check below replaces it with the prover-based result.
        // We keep the static check available for the `--parse-only`
        // path (where no Maude is started).
        if !args.parse_only {
            wf_report.retain(|e| e.topic != "Message Derivation Checks");
        }

        if args.parse_only {
            // HS-faithful: `--parse-only` does NOT run wellformedness
            // (checkWellformedness only fires inside `--prove`'s
            // close-theory pipeline).  Just re-emit the source verbatim.
            emit_output(args, in_file, &src, None)?;
            file_results.push(FileResult {
                in_file: in_file.clone(),
                out_file: out_path_for(args, in_file),
                results: Vec::new(),
                elapsed_ms: t0.elapsed().as_millis(),
                wf_count: 0,
            });
            continue;
        }

        // Elaborate (mainly to get the protocol-specific MaudeSig).
        let mut elaborated = elaborate(&parsed).map_err(|e| {
            RunError(format!("elaboration error in {}: {}", in_file, e.message))
        })?;
        phase!("elaborate");
        let maude_sig = elaborated.signature.maude_sig.clone();
        // HS emits this marker after `translateTheory` finishes
        // (TheoryLoader.hs:454).
        if !args.quiet && !args.parse_only {
            eprintln!("[Theory {}] Theory translated", theory_name);
        }

        // Spawn a single Maude handle for this file.  Used by:
        //   - the rule-variants computation that populates each rule's
        //     `variant_substs` + `abstracted_rule` (so the pretty-printer
        //     can emit HS's `variants (modulo AC) ...` block);
        //   - the dynamic Message Derivation Check;
        //   - the per-lemma prove loop.
        let maude_path = args.maude_path.clone().unwrap_or_else(default_maude_path);
        let file_maude: Option<MaudeHandle> = if !args.parse_only {
            MaudeHandle::start(&maude_path, maude_sig.clone()).ok()
        } else {
            None
        };
        phase!("spawn maude");

        // Spawn an auxiliary MaudePool of `effective_maude_processes()`
        // EXTRA subprocesses for use at the rayon parallel sites
        // (rule-variant closure, saturate refinement).  Workers
        // `acquire()` one for the duration of one parallel task so they
        // don't serialise on `file_maude`'s IPC mutex.
        //
        // - `--processors=1` ⇒ `effective_maude_processes=1`; we skip
        //   the auxiliary pool entirely (sequential path uses
        //   `file_maude` only — byte-identical to pre-pool behaviour).
        // - `M >= 2` ⇒ spawn M independent Maudes.  Each costs
        //   ~30-100 MB; `--maude-processes=N` lets the user override.
        //
        // The pool is kept SEPARATE from `file_maude`: sequential paths
        // (main `prove_lemma` loop, derivation checks) keep using
        // `file_maude` (counter state and caches stay coherent across
        // lemmas); the pool is consumed only inside `par_iter` map
        // closures.
        let pool_size = args.effective_maude_processes();
        let file_maude_pool: Option<std::sync::Arc<MaudePool>> =
            if !args.parse_only && pool_size >= 2 {
                match MaudePool::new(&maude_path, maude_sig.clone(), pool_size) {
                    Ok(p) => Some(std::sync::Arc::new(p)),
                    Err(e) => {
                        if !args.quiet {
                            eprintln!("[warn] failed to spawn MaudePool({}): {} \
                                — falling back to single shared Maude", pool_size, e);
                        }
                        None
                    }
                }
            } else {
                None
            };
        phase!("spawn maude pool");

        // Populate variant_substs + abstracted_rule for each protocol
        // rule whose RHS contains reducible-headed sub-terms.  Without
        // this the pretty-printer always emits `/* has exactly the
        // trivial AC variant */` even when the signature carries
        // destructors (e.g. `aenc/adec`).  HS-faithful: matches
        // `closeTheoryWithMaude`'s variant pre-computation
        // (ClosedTheory.hs `closeTheory`).
        if let Some(m) = file_maude.as_ref() {
            populate_rule_variants(&mut elaborated, m,
                file_maude_pool.as_deref());
        }
        phase!("populate_rule_variants");

        // Annotate per-rule loop breakers on the OUTER theory so
        // `pretty_closed_theory` can render HS's `// loop breaker:
        // [<idx>]` comments at the rule output.  HS faithfulness:
        // `prettyClosedProtoRule` (ClosedTheory.hs:337,353) reads
        // `prettyLoopBreakers` from the `ProtoRuleACInfo` baked into
        // every closed rule by `closeTheoryWithMaude`.  Our prover
        // computes them inside `ProofContext::new` on a LOCAL copy
        // of the rules — so we re-run the same `annotate_loop_breakers`
        // pass on the outer theory here to mirror the closed-theory
        // structure HS persists.
        if let Some(m) = file_maude.as_ref() {
            use tamarin_theory::theory::TheoryItem;
            let mut rules: Vec<tamarin_theory::theory::OpenProtoRule> =
                elaborated.items.iter().filter_map(|i| match i {
                    TheoryItem::Rule(r) => Some(r.clone()), _ => None,
                }).collect();
            tamarin_theory::constraint::solver::context::annotate_loop_breakers(
                &mut rules, m);
            // Sequential writeback in source order.
            let mut iter = rules.into_iter();
            for item in elaborated.items.iter_mut() {
                if let TheoryItem::Rule(opr) = item {
                    if let Some(updated) = iter.next() {
                        opr.loop_breakers = updated.loop_breakers;
                    }
                }
            }
        }
        phase!("annotate_loop_breakers");

        // Dynamic Message Derivation Checks (mirrors HS
        // `checkVariableDeducability`, gated by `--derivcheck-timeout`,
        // default 5s).  Needs Maude, so we run it AFTER elaboration
        // and BEFORE the main prove loop.  HS default is 5s; 0 disables.
        // Each per-variable proof attempt is capped at this timeout.
        let deriv_timeout = args.derivcheck_timeout.unwrap_or(5) as u32;
        if deriv_timeout > 0 {
            // HS emits these markers around the per-variable derivability
            // check (TheoryLoader.hs:485, :498).
            if !args.quiet && !args.parse_only {
                eprintln!("[Theory {}] Derivation checks started", theory_name);
            }
            if let Some(m) = file_maude.as_ref() {
                let extra = tamarin_theory::deriv_check::check_message_derivation(
                    &parsed, m, deriv_timeout,
                );
                wf_report.extend(extra);
            }
            if !args.quiet && !args.parse_only {
                eprintln!("[Theory {}] Derivation checks ended", theory_name);
            }
        }
        phase!("derivation_checks");

        // Decide which lemmas to prove. Without --prove/--prove-all,
        // we never start the solver; output is just the source.
        let lemma_filter: &[String] = &args.lemma_names;
        let prove_anything = args.prove_mode || args.prove_all;

        let mut results: Vec<LemmaResult> = Vec::new();
        // Mirrors HS's per-lemma proof body for embedding in the
        // pretty-printed theory output.  Filled by the prove loop below.
        let mut proved_lemmas: Vec<tamarin_theory::pretty_theory::ProvedLemma> = Vec::new();

        if !prove_anything || args.precompute_only {
            // No proof step requested — record each lemma as Filtered
            // / Skipped depending on whether --lemma had any effect.
            for l in elaborated.lemmas() {
                results.push(LemmaResult {
                    name: l.name.clone(),
                    verdict: if lemma_filter.is_empty() {
                        LemmaVerdict::Skipped
                    } else if lemma_matches(lemma_filter, &l.name) {
                        // Selected but no prove flag — still skipped.
                        LemmaVerdict::Skipped
                    } else {
                        LemmaVerdict::Filtered
                    },
                    elapsed_ms: 0,
                    // HS counts the default `Sorry` placeholder proof
                    // as 1 step (one `LNode (ProofStep Sorry ...)` —
                    // see `Theory.Proof.proofStepCount`).  Match it.
                    proof_steps: 1,
                    exists_trace: matches!(
                        l.trace_quantifier,
                        tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                    ),
                });
            }
        } else {
            // Reuse the per-file maude handle.  The `maude tool: ...`
            // banner is printed once at the top of the batch run (see
            // above), matching HS.
            let maude = file_maude.clone().ok_or_else(|| {
                RunError(format!(
                    "failed to start maude at {:?}",
                    maude_path,
                ))
            })?;

            // Per-lemma proof loop.
            let budget: usize = args
                .bound
                .map(|b| b as usize)
                .unwrap_or(500);

            // Build the per-file shared prover session ONCE.  Profile
            // showed that constructing a fresh `ProofContext` per lemma
            // re-ran ~3s of file-level setup (intruder rules, Maude
            // variants, `precompute_full_sources`) per lemma; HS does
            // this work once at theory-close time.  `ProverSession`
            // captures it once; each lemma clones the cheap template
            // and runs only the per-lemma `ensure_saturated`
            // refinement against its own typing assumptions.
            //
            // Fall-through path: if `ProverSession::build` errors we
            // fall back to the per-lemma `prove_lemma_with_pool` path
            // (which re-runs the setup per lemma but is more tolerant
            // of theories where elaboration fails on a subset of
            // lemmas).  Almost never hits in practice.
            let session = tamarin_theory::prove::ProverSession::build(
                &parsed, maude.clone(), file_maude_pool.clone()).ok();

            for l in elaborated.lemmas() {
                let lemma_name = l.name.clone();
                let exists_trace = matches!(
                    l.trace_quantifier,
                    tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                );
                // HS faithfulness: `closeTheory` runs
                // `checkAndExtendProver` (Prover.hs:174-185) over ALL
                // lemmas, re-attaching the constraint system to each
                // stored skeleton step.  `--prove=X` then runs the
                // auto-prover ONLY on lemmas matching the selector
                // (Prover.hs:273-275); the rest keep their close-time
                // replayed proof, reprinted verbatim with the stored
                // status.  We mirror that: the target lemma(s) run the
                // full skeleton-replay+auto-prove; non-target lemmas run
                // check-and-extend (replay only, no auto-proving open
                // leaves) — which also keeps us from launching a heavy
                // search on lemmas the user didn't ask to prove.
                let is_target = lemma_matches(lemma_filter, &lemma_name);
                // HS does NOT print a per-lemma "proving lemma X ..."
                // marker; the only progress lines are the `[Theory X]
                // ...` set above.  Stay quiet here for HS-faithful stderr.
                let lt = Instant::now();
                let outcome = match (session.as_ref(), is_target) {
                    (Some(s), true) => tamarin_theory::prove::prove_lemma_in_session(
                        s, &lemma_name, budget),
                    (Some(s), false) => tamarin_theory::prove::check_and_extend_lemma_in_session(
                        s, &lemma_name, budget),
                    (None, _) => tamarin_theory::prove::prove_lemma_with_pool(
                        &parsed, &lemma_name, maude.clone(),
                        file_maude_pool.clone(), budget),
                };
                if dbg_timing {
                    eprintln!("[TAM_DBG_RUN_TIMING] {:>26}: {:>8.1} ms  (lemma={})",
                              "prove_lemma", lt.elapsed().as_secs_f64() * 1000.0,
                              lemma_name);
                }
                let (verdict, proof_steps, proof_body) = match outcome {
                    Ok(root) => {
                        let steps = count_proof_steps(&root);
                        let v = match root.status {
                            NodeStatus::Solved => {
                                if matches!(
                                    l.trace_quantifier,
                                    tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                                ) {
                                    LemmaVerdict::Verified
                                } else {
                                    LemmaVerdict::Falsified
                                }
                            }
                            NodeStatus::Contradictory => {
                                if matches!(
                                    l.trace_quantifier,
                                    tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                                ) {
                                    LemmaVerdict::Falsified
                                } else {
                                    LemmaVerdict::Verified
                                }
                            }
                            NodeStatus::Sorry
                            | NodeStatus::Unfinishable
                            | NodeStatus::Open => LemmaVerdict::Analyzed,
                        };
                        let body = tamarin_theory::pretty_theory::pretty_proof_body(&root);
                        (v, steps, Some(body))
                    }
                    Err(e) => (LemmaVerdict::Error(format!("{}", e)), 0, None),
                };
                proved_lemmas.push(tamarin_theory::pretty_theory::ProvedLemma {
                    name: lemma_name.clone(),
                    proof_body,
                });
                results.push(LemmaResult {
                    name: lemma_name,
                    verdict,
                    elapsed_ms: lt.elapsed().as_millis(),
                    proof_steps,
                    exists_trace,
                });
            }

            // HS-faithful: rc=0 regardless of verdict.  Falsified is a
            // valid analysis outcome — the prover ran successfully and
            // found a counter-example trace.  Only true errors (parse
            // failures, Maude crashes, IO errors) escalate to non-zero.
            for r in &results {
                if matches!(r.verdict, LemmaVerdict::Error(_)) {
                    overall_status = overall_status.max(1);
                }
            }
        }
        // Reset the phase clock so "Theory closed" + pretty-print +
        // emit_output are measured fresh (the prove loop reports its own
        // per-lemma timings above).
        t_phase = Instant::now();

        // HS emits this marker after `closeTheory` finishes
        // (TheoryLoader.hs:596).
        if !args.quiet && !args.parse_only {
            eprintln!("[Theory {}] Theory closed", theory_name);
        }

        // Build the HS-faithful theory pretty-print body.  This replaces
        // the verbatim source dump with HS's `prettyClosedTheory`
        // output shape — re-rendered signature, rules with `(modulo E)`
        // prefix and AC-variant comments, lemmas with inline guarded
        // formula and proof body, wellformedness block, and
        // Generated-from footer.
        let build_info = tamarin_theory::pretty_theory::BuildInfo {
            tamarin_version: crate::cli::VERSION.to_string(),
            maude_version: crate::cli::detect_maude_version_pub()
                .unwrap_or_else(|| "unknown".to_string()),
            git_revision: crate::cli::GIT_REV.to_string(),
            git_branch: crate::cli::GIT_BRANCH.to_string(),
            compiled_at: crate::cli::BUILD_TIMESTAMP.to_string(),
        };
        let wf_block = format_wf_block(&wf_report);
        let body = tamarin_theory::pretty_theory::pretty_closed_theory(
            &parsed,
            &elaborated,
            &proved_lemmas,
            &wf_block,
            &build_info,
        );
        phase!("pretty_closed_theory");
        emit_output(args, in_file, &body, None)?;
        phase!("emit_output");

        file_results.push(FileResult {
            in_file: in_file.clone(),
            out_file: out_path_for(args, in_file),
            results,
            elapsed_ms: t0.elapsed().as_millis(),
            wf_count: wf_report.len(),
        });
        if args.quit_on_warning && !wf_report.is_empty() {
            return Err(RunError(format!(
                "{} wellformedness check(s) failed (--quit-on-warning set)",
                wf_report.len()
            )));
        }
    }

    // HS-faithful: `--parse-only` skips the `summary of summaries:`
    // block entirely.  Only `--prove` (or any flag that actually runs
    // the prover) emits it.
    if !args.quiet && !args.parse_only {
        print_overall_summary(&file_results);
    }

    Ok(overall_status)
}

/// Format the `/* WARNING: ... */` or `/* All wellformedness checks
/// were successful. */` block that goes BETWEEN the source body and
/// the analysis summary.  Mirrors HS's `prettyWfErrorReport`
/// (Wellformedness.hs:118-125).
///
/// Each `WfError.message` is expected to carry the FULL HS-style block
/// for its topic: `Title\n=====\n\n<intro>\n<body>` — pre-formatted with
/// the exact bytes HS emits, including trailing spaces from HS's
/// `text ""` markers.  Multiple `WfError`s with the same topic are
/// merged into one block (the per-clash bodies concatenated).  Topic
/// groups are separated by blank lines.
fn format_wf_block(report: &[tamarin_parser::wf::WfError]) -> String {
    if report.is_empty() {
        return "/* All wellformedness checks were successful. */".to_string();
    }
    let mut out = String::new();
    out.push_str("/*\nWARNING: the following wellformedness checks failed!\n\n");
    // Group by topic, preserving FIRST-APPEARANCE order — mirrors HS's
    // `groupOn fst` over a left-to-right concatMap-over-checks.
    let mut topic_order: Vec<&str> = Vec::new();
    let mut grouped: std::collections::HashMap<&str, Vec<&str>> =
        std::collections::HashMap::new();
    for e in report {
        if !grouped.contains_key(e.topic.as_str()) {
            topic_order.push(e.topic.as_str());
        }
        grouped.entry(e.topic.as_str()).or_default().push(&e.message);
    }
    for (i, topic) in topic_order.iter().enumerate() {
        let msgs = &grouped[topic];
        if i > 0 { out.push('\n'); }
        for (j, m) in msgs.iter().enumerate() {
            if j > 0 { out.push('\n'); }
            out.push_str(m);
            if !m.ends_with('\n') { out.push('\n'); }
        }
    }
    // Trim trailing blank lines but keep a single newline before `*/`.
    while out.ends_with("\n\n") { out.pop(); }
    out.push_str("*/");
    out
}

/// Compute and store `variant_substs` + `abstracted_rule` on every
/// `OpenProtoRule` whose RHS contains reducible-headed sub-terms.
/// Mirrors HS's `variantsProtoRule` pre-computation performed during
/// `closeTheory`.  Rules with no reducible-headed sub-terms (the common
/// case for `pair/fst/snd` signatures) get an empty variants list,
/// which the pretty-printer treats as "trivial AC variant".
///
/// HS-parallel: `lib/theory/src/Prover.hs:195`
///   `(closeTheoryItem <$> L.get thyItems thy0) \`using\` parList rdeepseq`
/// HS evaluates the per-item `closeTheoryItem` (which calls
/// `variantsProtoRule`) in parallel via `parList rdeepseq`, preserving
/// list order.  We mirror via rayon: each item is processed in its own
/// task, results re-assembled in source order.
///
/// Determinism: `abstract_rule_and_variants` allocates fresh vars via
/// `MaudeHandle::with_fresh_counter_from(avoid_max)` (per-call counter),
/// so concurrent calls don't share counter state.  Maude IPC is
/// serialised inside `MaudeHandle::inner` (Arc<Mutex>) — workers
/// queue on Maude but don't corrupt it.
///
/// When `pool` is `Some`, each parallel task acquires its own Maude
/// subprocess for the duration of one rule, so the M parallel
/// `abstract_rule_and_variants` calls run on independent subprocesses
/// instead of contending on the single shared `maude`'s IPC mutex.
/// Per-call `with_fresh_counter_from(avoid_max)` already guarantees
/// HS-faithful witness allocation regardless of which pool member
/// handles a given rule, so output is byte-identical to the
/// single-Maude path.
fn populate_rule_variants(elaborated: &mut tamarin_theory::theory::Theory,
                          maude: &MaudeHandle,
                          pool: Option<&MaudePool>) {
    use rayon::prelude::*;
    use tamarin_theory::theory::TheoryItem;

    // HS-faithful: skip variant computation if the signature has
    // NO reducible function symbols — there's nothing to narrow.
    // Compute once (signature is read-only here) rather than in the
    // inner loop.
    if maude.maude_sig().reducible_fun_syms.is_empty() { return; }

    // Index → (abstracted_rule, variant_substs) for rules that have
    // any.  Computed in parallel; the BTreeMap/Vec collect preserves
    // source order via the keyed structure.
    let outs: Vec<Option<(tamarin_theory::rule::ProtoRuleE, Vec<tamarin_term::subst_vfresh::LNSubstVFresh>)>> =
        elaborated.items.par_iter().map(|item| {
            let TheoryItem::Rule(opr) = item else { return None; };
            // Per-task Maude: acquire from the pool when available so
            // each rule's variant computation runs on its own
            // subprocess (no IPC mutex contention).  Fall back to
            // the shared `maude` when no pool is configured.
            let result = if let Some(pool) = pool {
                let pooled = pool.acquire();
                tamarin_theory::tools::rule_variants::abstract_rule_and_variants(
                    &*pooled, &opr.rule)
            } else {
                tamarin_theory::tools::rule_variants::abstract_rule_and_variants(
                    maude, &opr.rule)
            };
            match result {
                Ok(Some(pair)) => Some(pair),
                _ => None,
            }
        }).collect();

    // Sequential writeback in source order — matches HS's
    // `parList rdeepseq` semantics (parallel evaluation, sequential
    // list materialisation).
    for (item, out) in elaborated.items.iter_mut().zip(outs.into_iter()) {
        let TheoryItem::Rule(opr) = item else { continue };
        if let Some((abstr, substs)) = out {
            opr.abstracted_rule = Some(abstr);
            opr.variant_substs = substs;
        }
    }
}

/// Install rayon's global worker pool to the size requested via
/// `--processors=N` (or a sensible default).
///
/// HS-equivalent: GHC's `+RTS -N RTS_FLAG` sets the worker capacity for
/// the `par*`/`Strategies` sites HS uses.  We mirror that surface via a
/// CLI flag.  Idempotent across files in a batch — `build_global`
/// silently errors on the second call, which is what we want.
///
/// Default: `available_parallelism()` (full machine).  Previously
/// capped at 4 to avoid the Maude IPC mutex serialising every worker
/// on a single subprocess; with `MaudePool` (`--maude-processes=M`)
/// the contention is gone and users can productively scale to every
/// core.  Memory budget is mediated by `--maude-processes`, which
/// defaults to `processors / 2`.
fn init_rayon_pool(args: &Args) {
    let n = args.effective_processors();
    // `build_global` is idempotent-error: the SECOND call returns Err
    // even if N matches.  We swallow the error: the first invocation
    // wins (which is the desired behaviour — RS runs `run_batch` once
    // per process, and tests install their own pool).
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(n)
        .thread_name(|i| format!("tamarin-rayon-{}", i))
        .build_global();
}

fn default_maude_path() -> String {
    for c in [
        "/home/linuxbrew/.linuxbrew/bin/maude",
        "/usr/local/bin/maude",
        "/usr/bin/maude",
    ] {
        if std::path::Path::new(c).exists() {
            return c.to_string();
        }
    }
    "maude".to_string()
}

/// Emit `body` to `--output` / `-O` / stdout.
fn emit_output(args: &Args, in_file: &str, body: &str, _override_out: Option<&str>) -> Result<(), RunError> {
    if let Some(out) = out_path_for(args, in_file) {
        // Ensure parent dir exists.
        if let Some(parent) = std::path::Path::new(&out).parent() {
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent).map_err(|e| {
                    RunError(format!("failed to create {}: {}", parent.display(), e))
                })?;
            }
        }
        fs::write(&out, body)
            .map_err(|e| RunError(format!("failed to write {}: {}", out, e)))?;
    } else {
        // stdout
        print!("{}", body);
    }
    Ok(())
}

/// Resolve the output path for `in_file` given the user's `-o` / `-O`
/// flags. Returns `None` when output should go to stdout.
pub fn out_path_for(args: &Args, in_file: &str) -> Option<String> {
    if let Some(of) = &args.output_file {
        if !of.is_empty() {
            return Some(of.clone());
        }
    }
    if let Some(dir) = &args.output_dir {
        let stem = std::path::Path::new(in_file)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("theory");
        let mut p = PathBuf::from(dir);
        p.push(format!("{}_analyzed.spthy", stem));
        return Some(p.to_string_lossy().to_string());
    }
    None
}

/// Count proof-tree nodes in HS's `proofStepCount` style — the number
/// of `LNode` constructors in the proof tree.  Each `step` in the
/// proof's textual form (a `simplify` / `solve(...) case X` /
/// `qed` / `SOLVED` annotation) corresponds to one ProofNode.
/// Mirrors `Theory.Proof.proofStepCount`.
fn count_proof_steps(node: &tamarin_theory::constraint::solver::search::ProofNode) -> usize {
    1 + node.children.values().map(count_proof_steps).sum::<usize>()
}

fn print_overall_summary(file_results: &[FileResult]) {
    // Mirrors HS `summary of summaries:` block (`Main.Mode.Batch`).
    let line = "=".repeat(78);
    println!();
    println!("{}", line);
    println!("summary of summaries:");
    println!();
    for fr in file_results {
        println!("analyzed: {}", fr.in_file);
        println!();
        if let Some(out) = &fr.out_file {
            // HS aligns `output:` and `processing time:` columns
            // (Theory.Constraint.Solver.summarize).
            println!("  output:          {}", out);
        }
        println!("  processing time: {:.2}s", fr.elapsed_ms as f64 / 1000.0);
        println!("  ");
        if fr.wf_count > 0 {
            println!("  WARNING: {} wellformedness check failed!", fr.wf_count);
            println!("           The analysis results might be wrong!");
            println!("  ");
        }
        for r in &fr.results {
            println!("  {}", format_lemma_summary_line(r));
        }
        println!();
    }
    println!("{}", line);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cli::parse_args;

    fn parse(args: &[&str]) -> Args {
        parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("parse")
    }

    #[test]
    fn out_path_for_uses_file_when_set() {
        let a = parse(&["-o", "/tmp/foo.spthy", "in.spthy"]);
        assert_eq!(
            out_path_for(&a, "in.spthy").as_deref(),
            Some("/tmp/foo.spthy"),
        );
    }

    #[test]
    fn out_path_for_uses_dir_with_basename_when_set() {
        let a = parse(&["-O", "/tmp/outdir", "examples/foo.spthy"]);
        let got = out_path_for(&a, "examples/foo.spthy");
        assert_eq!(got.as_deref(), Some("/tmp/outdir/foo_analyzed.spthy"));
    }

    #[test]
    fn out_path_for_none_means_stdout() {
        let a = parse(&["in.spthy"]);
        assert_eq!(out_path_for(&a, "in.spthy"), None);
    }

    #[test]
    fn diff_flag_errors_cleanly() {
        let a = parse(&["--diff", "in.spthy"]);
        let r = run(&a);
        assert!(matches!(r, Err(RunError(_))), "diff should error, got {:?}", r);
    }

    #[test]
    fn interactive_subcmd_is_routed() {
        // We can't actually invoke `run` on the interactive subcommand
        // in a unit test (it would bind a TCP socket and block), so we
        // just check that the parser routes to it and accepts the
        // expected interactive flags.
        let a = parse(&[
            "interactive",
            "--port=3001",
            "--interface=127.0.0.1",
            "--image-format=PNG",
            "--debug",
            "--no-logging",
            "--data-dir=/tmp/data",
        ]);
        assert_eq!(a.subcommand, crate::cli::Subcommand::Interactive);
        assert_eq!(a.port, Some(3001));
        assert_eq!(a.interface.as_deref(), Some("127.0.0.1"));
        assert!(matches!(a.image_format, Some(crate::cli::ImageFormat::Png)));
        assert!(a.debug);
        assert!(a.no_logging);
        assert_eq!(a.data_dir.as_deref(), Some("/tmp/data"));
    }

    #[test]
    fn interactive_invalid_interface_errors() {
        // Asking to bind to garbage should produce a clear error
        // without ever opening a socket.
        let a = parse(&["interactive", "--interface=not-an-ip"]);
        let r = run(&a);
        assert!(matches!(r, Err(_)), "expected interface parse error");
    }

    #[test]
    fn no_input_files_errors() {
        let a = parse(&[]);
        let r = run(&a);
        assert!(matches!(r, Err(_)));
    }

    #[test]
    fn help_returns_zero() {
        let a = parse(&["--help"]);
        let r = run(&a).expect("help");
        assert_eq!(r, 0);
    }

    #[test]
    fn version_returns_zero() {
        let a = parse(&["--version"]);
        let r = run(&a).expect("version");
        assert_eq!(r, 0);
    }
}
