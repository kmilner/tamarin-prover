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

use tamarin_term::maude_proc::MaudeHandle;
use tamarin_theory::constraint::solver::search::NodeStatus;
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::prove::prove_lemma;

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
            LemmaVerdict::Analyzed => "analyzed (no proof found)",
            LemmaVerdict::Skipped => "not analyzed",
            LemmaVerdict::Filtered => "not analyzed",
            LemmaVerdict::Error(_) => "error",
        }
    }
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
        Subcommand::Variants => Err(RunError(
            "the `variants` subcommand is not yet ported.".to_string(),
        )),
        Subcommand::Test => Err(RunError(
            "the `test` self-test subcommand is not yet ported.".to_string(),
        )),
    }
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
    if args.trace_json.is_some() || args.trace_dot.is_some() {
        return Err(RunError(
            "--output-json / --output-dot are not yet ported to the Rust prover."
                .to_string(),
        ));
    }
    if args.in_files.is_empty() {
        return Err(RunError(
            "no input files given\n\n".to_string() + &crate::cli::help_text(),
        ));
    }
    let mut overall_status = 0i32;
    let mut file_results: Vec<FileResult> = Vec::new();

    let parser_flags: Vec<&str> = args.defines.iter().map(String::as_str).collect();

    for in_file in &args.in_files {
        let t0 = Instant::now();
        let src = fs::read_to_string(in_file).map_err(|e| {
            RunError(format!("failed to read {}: {}", in_file, e))
        })?;
        let parsed = tamarin_parser::parse_theory(&src, &parser_flags).map_err(|e| {
            RunError(format!("parse error in {}: {}", in_file, e))
        })?;

        if args.parse_only {
            // Just re-emit the source verbatim.
            emit_output(args, in_file, &src, None)?;
            file_results.push(FileResult {
                in_file: in_file.clone(),
                out_file: out_path_for(args, in_file),
                results: Vec::new(),
                elapsed_ms: t0.elapsed().as_millis(),
            });
            continue;
        }

        // Elaborate (mainly to get the protocol-specific MaudeSig).
        let elaborated = elaborate(&parsed).map_err(|e| {
            RunError(format!("elaboration error in {}: {}", in_file, e.message))
        })?;
        let maude_sig = elaborated.signature.maude_sig.clone();

        // Decide which lemmas to prove. Without --prove/--prove-all,
        // we never start the solver; output is just the source.
        let lemma_filter: &[String] = &args.lemma_names;
        let prove_anything = args.prove_mode || args.prove_all;

        let mut results: Vec<LemmaResult> = Vec::new();

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
                    proof_steps: 0,
                    exists_trace: matches!(
                        l.trace_quantifier,
                        tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                    ),
                });
            }
        } else {
            // Spin up a Maude bridge per file.
            let maude_path = args.maude_path.clone().unwrap_or_else(default_maude_path);
            if !args.quiet {
                eprintln!("maude tool: '{}'", maude_path);
            }
            let maude = MaudeHandle::start(&maude_path, maude_sig).map_err(|e| {
                RunError(format!(
                    "failed to start maude at {:?}: {:?}",
                    maude_path, e
                ))
            })?;

            // Per-lemma proof loop.
            let budget: usize = args
                .bound
                .map(|b| b as usize)
                .unwrap_or(500);

            for l in elaborated.lemmas() {
                let lemma_name = l.name.clone();
                let exists_trace = matches!(
                    l.trace_quantifier,
                    tamarin_theory::theory::TraceQuantifier::ExistsTrace,
                );
                if !lemma_matches(lemma_filter, &lemma_name) {
                    results.push(LemmaResult {
                        name: lemma_name,
                        verdict: LemmaVerdict::Filtered,
                        elapsed_ms: 0,
                        proof_steps: 0,
                        exists_trace,
                    });
                    continue;
                }
                if !args.quiet {
                    eprintln!("proving lemma `{}` ...", lemma_name);
                }
                let lt = Instant::now();
                let outcome = prove_lemma(&parsed, &lemma_name, maude.clone(), budget);
                let (verdict, proof_steps) = match outcome {
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
                        (v, steps)
                    }
                    Err(e) => (LemmaVerdict::Error(format!("{}", e)), 0),
                };
                results.push(LemmaResult {
                    name: lemma_name,
                    verdict,
                    elapsed_ms: lt.elapsed().as_millis(),
                    proof_steps,
                    exists_trace,
                });
            }

            // Update overall_status: error or falsified-when-all-traces
            // is a non-zero exit on most CI workflows. We track the
            // most-severe outcome.
            for r in &results {
                match &r.verdict {
                    LemmaVerdict::Error(_) => overall_status = overall_status.max(2),
                    LemmaVerdict::Falsified => overall_status = overall_status.max(1),
                    _ => {}
                }
            }
        }

        let summary = format_summary(in_file, &results);
        let body = format!("{}\n{}\n", src.trim_end(), summary);
        emit_output(args, in_file, &body, None)?;

        file_results.push(FileResult {
            in_file: in_file.clone(),
            out_file: out_path_for(args, in_file),
            results,
            elapsed_ms: t0.elapsed().as_millis(),
        });
    }

    if !args.quiet {
        print_overall_summary(&file_results);
    }

    Ok(overall_status)
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

fn format_summary(in_file: &str, results: &[LemmaResult]) -> String {
    let mut s = String::new();
    s.push_str("/*\n");
    s.push_str(&format!("analyzed: {}\n", in_file));
    s.push_str("\n");
    s.push_str("  output:          (Rust port)\n");
    if results.is_empty() {
        s.push_str("  processed: no lemmas selected\n");
    } else {
        for r in results {
            let suffix = match &r.verdict {
                LemmaVerdict::Error(msg) => format!(" — {}", msg),
                _ => String::new(),
            };
            // HS-faithful format: "(<quantifier>): <verdict> - found
            // trace (<N> steps)" or "(<quantifier>, <N> steps): <verdict>"
            // depending on context.  We use HS's
            // `--prove` summary form: "(<quantifier>, <N> steps):
            // <verdict>" where N is the proof-tree node count.
            s.push_str(&format!(
                "  {} ({}, {} steps): {}{}\n",
                r.name,
                tag_for(&r.verdict, r.exists_trace),
                r.proof_steps,
                r.verdict.label(),
                suffix
            ));
        }
    }
    s.push_str("*/\n");
    s
}

fn tag_for(v: &LemmaVerdict, exists_trace: bool) -> &'static str {
    match v {
        LemmaVerdict::Verified
        | LemmaVerdict::Falsified
        | LemmaVerdict::Analyzed => {
            if exists_trace { "exists-trace" } else { "all-traces" }
        }
        LemmaVerdict::Skipped => "skipped",
        LemmaVerdict::Filtered => "filtered",
        LemmaVerdict::Error(_) => "error",
    }
}

fn print_overall_summary(file_results: &[FileResult]) {
    let line = "=".repeat(78);
    println!();
    println!("{}", line);
    println!("summary of summaries:");
    println!();
    for fr in file_results {
        println!("analyzed: {}", fr.in_file);
        if let Some(out) = &fr.out_file {
            println!("  output: {}", out);
        }
        for r in &fr.results {
            println!("  {}: {} ({}ms)", r.name, r.verdict.label(), r.elapsed_ms);
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
