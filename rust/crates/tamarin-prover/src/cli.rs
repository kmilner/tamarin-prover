//! Command-line argument parsing for `tamarin-prover` (Rust port).
//!
//! Mirrors the surface of the Haskell `tamarin-prover` CLI as defined
//! in `src/Main/Console.hs`, `src/Main/Mode/Batch.hs` and
//! `src/Main/TheoryLoader.hs`. We use a small hand-rolled parser
//! rather than pulling in `clap` so the binary stays dependency-light.
//!
//! What we currently support (batch / prove pipeline):
//!
//!   --prove[=LEMMA]            select a lemma (or prefix*) to prove. Repeatable.
//!   --prove-all                shorthand for proving every lemma.
//!   --lemma[=LEMMA]            (synonym for --prove without proving — kept for parity)
//!   --stop-on-trace=DFS|...    trace-search policy (parsed, not yet routed in port)
//!   --bound=N, -b N            proof-depth bound
//!   --saturation=N, -s N       saturation iterations (parsed, not yet routed)
//!   --heuristic=...            heuristic ranking sequence (parsed, not yet routed)
//!   --partial-evaluation=...   partial-evaluation mode (parsed, not yet routed)
//!   -D|--defines=STRING        preprocessor `#define` flags. Repeatable.
//!   --diff                     observational-equivalence mode (errors: not yet ported)
//!   --quit-on-warning          treat wellformedness warnings as fatal
//!   --auto-sources             auto-generate sources lemmas (parsed, not yet routed)
//!   --oraclename=FILE          oracle heuristic file (parsed, not yet routed)
//!   --oracle-only              oracle-only mode (parsed, not yet routed)
//!   --quiet                    suppress chatter on stderr
//!   --verbose, -v              verbose proof-search output
//!   --parse-only               parse + pretty-print, no analysis
//!   --precompute-only          run precomputation only
//!   --open-chains=N, -c N      open-chain bound (parsed, not yet routed)
//!   --derivcheck-timeout=N -d  message-derivation check timeout (parsed, not yet routed)
//!   --no-reuse                 do not export reuse lemmas (parsed, not yet routed)
//!   --no-restrictions          do not export restrictions (parsed, not yet routed)
//!   --replication-bound=N      DeepSec replication bound (parsed, not yet routed)
//!   --no-compress              do not compress sequents (parsed, not yet routed)
//!   --output=FILE, -o FILE     write the analyzed theory to FILE
//!   --Output=DIR, -O DIR       write analyzed theory to DIR/<basename>_analyzed.spthy
//!   --output-module=MODULE -m  output module selector (errors: not yet ported)
//!   --output-json=FILE, --oj   serialize traces to JSON (writes empty stub + warns; not yet ported)
//!   --output-dot=FILE, --od    serialize traces to dot (writes empty stub + warns; not yet ported)
//!   --with-maude=PATH          path to `maude` (default: looked up via PATH)
//!   --with-dot=PATH            path to GraphViz `dot` (parsed, not yet routed)
//!   --with-json=PATH           path to JSON renderer (parsed, not yet routed)
//!   -h|-?|--help               print help and exit
//!   -V|--version               print version and exit
//!
//! Subcommands recognised but unimplemented in the Rust port (clear
//! error message issued):
//!
//!   variants      compute intruder-rule variants
//!   test          self-test
//!
//! `interactive` subcommand flags (mirrors `Main/Mode/Interactive.hs`):
//!
//!   --port=N, -p N             port to listen on (default 3001)
//!   --interface=ADDR, -i ADDR  interface to listen on (default 127.0.0.1)
//!   --image-format=PNG|SVG     image format used for graphs (default SVG)
//!   --debug                    show server debugging output
//!   --no-logging               suppress web server logs
//!   --data-dir=DIR             override path to the bundled `data/` directory
//!
//! The Haskell CLI uses `cmdargs`'s `flagOpt` for both bare `--foo` and
//! `--foo=VALUE` forms; we mirror that — a `--prove` with no value
//! means "prove all lemmas".

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StopOnTrace {
    Dfs,
    Bfs,
    SeqDfs,
    Sorry,
    None,
}

impl StopOnTrace {
    fn parse(s: &str) -> Result<Self, String> {
        match s.to_ascii_lowercase().as_str() {
            "dfs" => Ok(StopOnTrace::Dfs),
            "bfs" => Ok(StopOnTrace::Bfs),
            "seqdfs" => Ok(StopOnTrace::SeqDfs),
            "sorry" => Ok(StopOnTrace::Sorry),
            "none" => Ok(StopOnTrace::None),
            other => Err(format!("unknown stop-on-trace method: {}", other)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartialEval {
    Summary,
    Verbose,
}

impl PartialEval {
    fn parse(s: &str) -> Result<Self, String> {
        match s.to_ascii_lowercase().as_str() {
            "summary" => Ok(PartialEval::Summary),
            "verbose" => Ok(PartialEval::Verbose),
            // Mirror HS TheoryLoader.hs:320: `ArgumentError "partial-evaluation: unknown option"`.
            _ => Err("partial-evaluation: unknown option".to_string()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Subcommand {
    /// The default batch mode (prove + emit theory).
    Batch,
    /// `interactive` — web UI.
    Interactive,
    /// `variants` — intruder-rule variants (not supported in port).
    Variants,
    /// `test` — self-test (not supported in port).
    Test,
}

/// Image format used for graph rendering in interactive mode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImageFormat {
    Png,
    Svg,
}

impl ImageFormat {
    fn parse(s: &str) -> Result<Self, String> {
        match s.to_ascii_lowercase().as_str() {
            "png" => Ok(ImageFormat::Png),
            "svg" => Ok(ImageFormat::Svg),
            other => Err(format!("image-format must be PNG|SVG (got {:?})", other)),
        }
    }
}

/// Parsed command-line options.
#[derive(Debug, Clone)]
pub struct Args {
    pub subcommand: Subcommand,

    /// Positional `.spthy` files.
    pub in_files: Vec<String>,

    // Lemma selection.
    /// True iff any `--prove` (with or without value) was passed.
    pub prove_mode: bool,
    /// Names / prefixes from `--prove` or `--lemma`. An empty entry
    /// (e.g. bare `--prove`) means "all lemmas".
    pub lemma_names: Vec<String>,
    /// True iff `--prove-all` was passed (alias for `--prove` with no
    /// argument).
    pub prove_all: bool,

    // Theory-load options.
    pub stop_on_trace: Option<StopOnTrace>,
    pub bound: Option<u32>,
    pub heuristic: Option<String>,
    pub partial_evaluation: Option<PartialEval>,
    pub defines: Vec<String>,
    pub diff: bool,
    pub quit_on_warning: bool,
    pub auto_sources: bool,
    pub oracle_name: Option<String>,
    pub oracle_only: bool,
    pub quiet: bool,
    pub verbose: bool,
    pub open_chains: Option<u64>,
    pub saturation: Option<u64>,
    pub derivcheck_timeout: Option<u64>,
    pub no_reuse: bool,
    pub no_restrictions: bool,
    pub replication_bound: Option<u32>,
    pub no_compress: bool,
    pub parse_only: bool,
    pub precompute_only: bool,

    /// `--processors=N` — size of the rayon worker pool used for
    /// HS-faithful internal parallelism (rule-variant closure,
    /// per-source saturate change-detection, per-item pretty-print).
    /// `None` = use default (`available_parallelism()` — full machine).
    /// `Some(1)` = single-threaded, byte-identical to sequential output.
    /// Mirrors HS's `+RTS -N RTS_FLAG` in spirit — see
    /// `lib/theory/src/Prover.hs:102,195`, `Theory/Constraint/Solver/Sources.hs:362`,
    /// `lib/theory/src/TheoryObject.hs:744,752`.
    pub processors: Option<usize>,

    /// `--maude-processes=M` — size of the pool of Maude subprocesses
    /// the rayon workers borrow from at parallel sites.  Each
    /// subprocess costs ~30-100 MB resident; too many → OOM on small
    /// VMs.  Default is `max(1, processors / 2)`, balancing throughput
    /// against memory.  `M=1` forces all workers to share one Maude
    /// (pre-pool behaviour, byte-identical to sequential).  When
    /// `--processors=1` we force `M=1` automatically (no point in a
    /// pool with no parallelism).  HS uses a single Maude per
    /// ClosedTheory — this pool is a Rust-specific implementation
    /// improvement to remove the IPC mutex contention bottleneck.
    pub maude_processes: Option<usize>,

    // Output options.
    pub output_file: Option<String>,
    pub output_dir: Option<String>,
    pub output_module: Option<String>,
    pub trace_json: Option<String>,
    pub trace_dot: Option<String>,

    // Tool paths.
    pub maude_path: Option<String>,
    pub dot_path: Option<String>,
    pub json_path: Option<String>,

    // Interactive-mode flags (mirror src/Main/Mode/Interactive.hs).
    pub port: Option<u16>,
    pub interface: Option<String>,
    pub image_format: Option<ImageFormat>,
    pub debug: bool,
    pub no_logging: bool,
    pub data_dir: Option<String>,

    // Meta.
    pub show_help: bool,
    pub show_version: bool,
}

impl Default for Args {
    fn default() -> Self {
        Args {
            subcommand: Subcommand::Batch,
            in_files: Vec::new(),
            prove_mode: false,
            lemma_names: Vec::new(),
            prove_all: false,
            stop_on_trace: None,
            bound: None,
            heuristic: None,
            partial_evaluation: None,
            defines: Vec::new(),
            diff: false,
            quit_on_warning: false,
            auto_sources: false,
            oracle_name: None,
            oracle_only: false,
            quiet: false,
            verbose: false,
            open_chains: None,
            saturation: None,
            derivcheck_timeout: None,
            no_reuse: false,
            no_restrictions: false,
            replication_bound: None,
            no_compress: false,
            parse_only: false,
            precompute_only: false,
            processors: None,
            maude_processes: None,
            output_file: None,
            output_dir: None,
            output_module: None,
            trace_json: None,
            trace_dot: None,
            maude_path: None,
            dot_path: None,
            json_path: None,
            port: None,
            interface: None,
            image_format: None,
            debug: false,
            no_logging: false,
            data_dir: None,
            show_help: false,
            show_version: false,
        }
    }
}

#[derive(Debug)]
pub enum CliError {
    /// User-facing message (already formatted).
    Msg(String),
}

impl std::fmt::Display for CliError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CliError::Msg(m) => f.write_str(m),
        }
    }
}

impl std::error::Error for CliError {}

/// Parse a raw argv-style slice (program name NOT included).
pub fn parse_args(raw: &[String]) -> Result<Args, CliError> {
    let mut args = Args::default();

    // Subcommand detection: if the first non-option token is a known
    // subcommand name, route to it. Otherwise stay in batch mode.
    let mut i = 0;
    if let Some(first) = raw.first() {
        match first.as_str() {
            "interactive" => {
                args.subcommand = Subcommand::Interactive;
                i = 1;
            }
            "variants" => {
                args.subcommand = Subcommand::Variants;
                i = 1;
            }
            "test" | "test-prover" => {
                args.subcommand = Subcommand::Test;
                i = 1;
            }
            _ => {}
        }
    }

    // A few short flags take a separate-token value (`-b N`, `-s N`,
    // `-o FILE`, etc.). We dispatch on full-name so all such cases
    // are explicit.

    let mut positional: Vec<String> = Vec::new();
    while i < raw.len() {
        let a = &raw[i];
        if a == "--" {
            // Everything after is positional.
            for x in &raw[(i + 1)..] {
                positional.push(x.clone());
            }
            break;
        }

        // Long flag.
        if let Some(rest) = a.strip_prefix("--") {
            let (key, val_inline) = split_eq(rest);
            match key {
                "help" => args.show_help = true,
                "version" => args.show_version = true,
                "prove" => {
                    args.prove_mode = true;
                    if let Some(v) = val_inline {
                        args.lemma_names.push(v.to_string());
                    } else {
                        // bare --prove → match-everything sentinel
                        args.lemma_names.push(String::new());
                    }
                }
                "prove-all" => {
                    args.prove_mode = true;
                    args.prove_all = true;
                    args.lemma_names.push(String::new());
                }
                "lemma" => {
                    if let Some(v) = val_inline {
                        args.lemma_names.push(v.to_string());
                    } else {
                        args.lemma_names.push(String::new());
                    }
                }
                "stop-on-trace" => {
                    let v = take_val(&mut i, raw, val_inline, "stop-on-trace")?;
                    args.stop_on_trace = Some(StopOnTrace::parse(&v).map_err(CliError::Msg)?);
                }
                "bound" => {
                    let v = take_val(&mut i, raw, val_inline, "bound")?;
                    args.bound = Some(parse_int(&v, "bound")?);
                }
                "heuristic" => {
                    let v = take_val(&mut i, raw, val_inline, "heuristic")?;
                    args.heuristic = Some(v);
                }
                "partial-evaluation" => {
                    let v = take_val(&mut i, raw, val_inline, "partial-evaluation")?;
                    args.partial_evaluation =
                        Some(PartialEval::parse(&v).map_err(CliError::Msg)?);
                }
                "defines" => {
                    let v = take_val(&mut i, raw, val_inline, "defines")?;
                    args.defines.push(v);
                }
                "diff" => args.diff = true,
                "quit-on-warning" => args.quit_on_warning = true,
                "auto-sources" => args.auto_sources = true,
                "oraclename" => {
                    let v = take_val(&mut i, raw, val_inline, "oraclename")?;
                    args.oracle_name = Some(v);
                }
                "oracle-only" => args.oracle_only = true,
                "quiet" => args.quiet = true,
                "verbose" => args.verbose = true,
                "open-chains" => {
                    let v = take_val(&mut i, raw, val_inline, "open-chains")?;
                    args.open_chains = Some(parse_int(&v, "open-chains")?);
                }
                "saturation" => {
                    let v = take_val(&mut i, raw, val_inline, "saturation")?;
                    args.saturation = Some(parse_int(&v, "saturation")?);
                }
                "derivcheck-timeout" => {
                    let v = take_val(&mut i, raw, val_inline, "derivcheck-timeout")?;
                    args.derivcheck_timeout = Some(parse_int(&v, "derivcheck-timeout")?);
                }
                "no-reuse" => args.no_reuse = true,
                "no-restrictions" => args.no_restrictions = true,
                "replication-bound" => {
                    let v = take_val(&mut i, raw, val_inline, "replication-bound")?;
                    args.replication_bound = Some(parse_int(&v, "replication-bound")?);
                }
                "no-compress" => args.no_compress = true,
                "parse-only" => args.parse_only = true,
                "precompute-only" => args.precompute_only = true,
                "processors" => {
                    let v = take_val(&mut i, raw, val_inline, "processors")?;
                    let n: usize = parse_int(&v, "processors")?;
                    if n == 0 {
                        return Err(CliError::Msg(
                            "--processors must be >= 1".to_string(),
                        ));
                    }
                    args.processors = Some(n);
                }
                "maude-processes" => {
                    let v = take_val(&mut i, raw, val_inline, "maude-processes")?;
                    let n: usize = parse_int(&v, "maude-processes")?;
                    if n == 0 {
                        return Err(CliError::Msg(
                            "--maude-processes must be >= 1".to_string(),
                        ));
                    }
                    args.maude_processes = Some(n);
                }
                // Output flags.
                "output" => {
                    let v = take_val(&mut i, raw, val_inline, "output")?;
                    args.output_file = Some(v);
                }
                // Note: the long form in Haskell is `--Output` (capital O)
                // for the directory variant. Accept both for friendliness.
                "Output" | "output-dir" => {
                    let v = take_val(&mut i, raw, val_inline, "Output")?;
                    args.output_dir = Some(v);
                }
                "output-module" => {
                    let v = take_val(&mut i, raw, val_inline, "output-module")?;
                    args.output_module = Some(v);
                }
                "output-json" | "oj" => {
                    let v = take_val(&mut i, raw, val_inline, "output-json")?;
                    args.trace_json = Some(v);
                }
                "output-dot" | "od" => {
                    let v = take_val(&mut i, raw, val_inline, "output-dot")?;
                    args.trace_dot = Some(v);
                }
                "with-maude" => {
                    let v = take_val(&mut i, raw, val_inline, "with-maude")?;
                    args.maude_path = Some(v);
                }
                "with-dot" => {
                    let v = take_val(&mut i, raw, val_inline, "with-dot")?;
                    args.dot_path = Some(v);
                }
                "with-json" => {
                    let v = take_val(&mut i, raw, val_inline, "with-json")?;
                    args.json_path = Some(v);
                }
                // Interactive-mode flags.
                "port" => {
                    let v = take_val(&mut i, raw, val_inline, "port")?;
                    args.port = Some(parse_int(&v, "port")?);
                }
                "interface" => {
                    let v = take_val(&mut i, raw, val_inline, "interface")?;
                    args.interface = Some(v);
                }
                "image-format" => {
                    let v = take_val(&mut i, raw, val_inline, "image-format")?;
                    args.image_format = Some(ImageFormat::parse(&v).map_err(CliError::Msg)?);
                }
                "debug" => args.debug = true,
                "no-logging" => args.no_logging = true,
                "data-dir" => {
                    let v = take_val(&mut i, raw, val_inline, "data-dir")?;
                    args.data_dir = Some(v);
                }
                other => {
                    return Err(CliError::Msg(format!("unknown flag: --{}", other)));
                }
            }
            i += 1;
            continue;
        }

        // Short flag(s). cmdargs in Haskell uses single-letter -X aliases.
        if let Some(rest) = a.strip_prefix('-') {
            if rest.is_empty() {
                // bare `-` — treat as positional (stdin convention)
                positional.push(a.clone());
                i += 1;
                continue;
            }
            // GNU-style clustering of boolean short flags, mirroring
            // System.Console.CmdArgs.Explicit (`-vh` sets both verbose
            // and help; HS `verbose`/`help`/`version` are all
            // no-argument `flagNone`/`flagHelpSimple`/`flagVersion`).
            // We walk the cluster char-by-char: a boolean short consumes
            // exactly one char and we continue with the rest; the first
            // value-taking short consumes the remainder of the token as
            // its inline value (e.g. `-b12`, `-vb12`) — or the next
            // token if nothing remains — and ends the cluster.
            for (idx, key) in rest.char_indices() {
                // Bytes after this char in the token form a potential
                // inline value for a value-taking flag.  Strip a single
                // leading `=` to keep `-b=12` working.
                let after = &rest[idx + key.len_utf8()..];
                let inline_raw = after.strip_prefix('=').unwrap_or(after);
                let inline: Option<&str> =
                    if inline_raw.is_empty() { None } else { Some(inline_raw) };
                match key {
                    'h' | '?' => {
                        args.show_help = true;
                        continue;
                    }
                    'V' => {
                        args.show_version = true;
                        continue;
                    }
                    'v' => {
                        args.verbose = true;
                        continue;
                    }
                    'b' => {
                        let v = take_short_val(&mut i, raw, inline, "bound")?;
                        args.bound = Some(parse_int(&v, "bound")?);
                    }
                    's' => {
                        let v = take_short_val(&mut i, raw, inline, "saturation")?;
                        args.saturation = Some(parse_int(&v, "saturation")?);
                    }
                    'c' => {
                        let v = take_short_val(&mut i, raw, inline, "open-chains")?;
                        args.open_chains = Some(parse_int(&v, "open-chains")?);
                    }
                    'd' => {
                        let v = take_short_val(&mut i, raw, inline, "derivcheck-timeout")?;
                        args.derivcheck_timeout = Some(parse_int(&v, "derivcheck-timeout")?);
                    }
                    'D' => {
                        let v = take_short_val(&mut i, raw, inline, "defines")?;
                        args.defines.push(v);
                    }
                    'o' => {
                        let v = take_short_val(&mut i, raw, inline, "output")?;
                        args.output_file = Some(v);
                    }
                    'O' => {
                        let v = take_short_val(&mut i, raw, inline, "Output")?;
                        args.output_dir = Some(v);
                    }
                    'm' => {
                        let v = take_short_val(&mut i, raw, inline, "output-module")?;
                        args.output_module = Some(v);
                    }
                    'p' => {
                        let v = take_short_val(&mut i, raw, inline, "port")?;
                        args.port = Some(parse_int(&v, "port")?);
                    }
                    'i' => {
                        let v = take_short_val(&mut i, raw, inline, "interface")?;
                        args.interface = Some(v);
                    }
                    other => {
                        return Err(CliError::Msg(format!("unknown short flag: -{}", other)));
                    }
                }
                // A value-taking flag consumed the remainder of the
                // token (and possibly the next token); stop scanning
                // this cluster.
                break;
            }
            i += 1;
            continue;
        }

        // Positional.
        positional.push(a.clone());
        i += 1;
    }
    args.in_files = positional;

    // Mirror Haskell: `--prove` with no value implies "match all".
    // `lemma_names` with at least one empty entry already means that,
    // so this is a no-op — but if --prove-all is set we ensure the
    // marker is present even if the user didn't pass --prove too.
    if args.prove_all && args.lemma_names.is_empty() {
        args.lemma_names.push(String::new());
    }

    Ok(args)
}

impl Args {
    /// Resolve `--processors` (or its default).  Default = full
    /// machine parallelism (`available_parallelism()`).  Previously
    /// capped at 4 to avoid Maude IPC mutex contention from making
    /// larger values unproductive; with `MaudePool` the contention
    /// is gone and we let users use every core.
    pub fn effective_processors(&self) -> usize {
        match self.processors {
            Some(n) => n.max(1),
            None => std::thread::available_parallelism()
                .map(|p| p.get())
                .unwrap_or(1),
        }
    }

    /// Resolve `--maude-processes` (or its default).
    ///
    /// Default = `max(1, effective_processors() / 2)` — balances Maude
    /// memory cost (~30-100 MB per subprocess on real protocols)
    /// against throughput; empirically a ratio of 1:2 (workers:maudes)
    /// gives most of the benefit of 1:1 without doubling memory.
    /// Tight-RAM users can override with `--maude-processes=2` etc.
    ///
    /// When `--processors=1`, force pool size 1 (no parallelism to
    /// exploit; saves spawn cost).
    pub fn effective_maude_processes(&self) -> usize {
        let procs = self.effective_processors();
        if procs == 1 {
            return 1;
        }
        match self.maude_processes {
            Some(n) => n.max(1),
            None => (procs / 2).max(1),
        }
    }
}

fn split_eq(s: &str) -> (&str, Option<&str>) {
    match s.find('=') {
        Some(i) => (&s[..i], Some(&s[(i + 1)..])),
        None => (s, None),
    }
}

fn take_val(
    i: &mut usize,
    raw: &[String],
    inline: Option<&str>,
    name: &str,
) -> Result<String, CliError> {
    if let Some(v) = inline {
        return Ok(v.to_string());
    }
    let next = raw.get(*i + 1).cloned().ok_or_else(|| {
        CliError::Msg(format!("flag --{} requires a value", name))
    })?;
    if next.starts_with('-') {
        return Err(CliError::Msg(format!(
            "flag --{} requires a value (got {:?})",
            name, next
        )));
    }
    *i += 1;
    Ok(next)
}

fn take_short_val(
    i: &mut usize,
    raw: &[String],
    inline: Option<&str>,
    name: &str,
) -> Result<String, CliError> {
    if let Some(v) = inline {
        return Ok(v.to_string());
    }
    let next = raw.get(*i + 1).cloned().ok_or_else(|| {
        CliError::Msg(format!("flag -{} requires a value", short_for(name)))
    })?;
    if next.starts_with('-') {
        return Err(CliError::Msg(format!(
            "flag -{} requires a value (got {:?})",
            short_for(name),
            next
        )));
    }
    *i += 1;
    Ok(next)
}

fn short_for(long: &str) -> char {
    match long {
        "bound" => 'b',
        "saturation" => 's',
        "open-chains" => 'c',
        "derivcheck-timeout" => 'd',
        "defines" => 'D',
        "output" => 'o',
        "Output" => 'O',
        "output-module" => 'm',
        "port" => 'p',
        "interface" => 'i',
        _ => '?',
    }
}

fn parse_int<T: std::str::FromStr>(s: &str, name: &str) -> Result<T, CliError> {
    s.parse::<T>().map_err(|_| {
        CliError::Msg(format!("{}: expected integer, got {:?}", name, s))
    })
}

/// Does the lemma name match the user's `--prove`/`--lemma` filter?
///
/// Mirrors HS `lemmaSelector` (TheoryLoader.hs:378-389): the empty
/// filter `[]`, the single-empty filter `[""]`, and the double-empty
/// filter `["",""]` all mean "all lemmas".  Otherwise we run
/// `any lemmaMatches filter` where a pattern ending in `*` matches by
/// prefix (with the `*` dropped) and any other pattern (including a
/// bare `""`) matches only by exact name.  Note this is NOT "drop all
/// empties": three or more bare entries (e.g. `["","",""]`) fall
/// through to the `any` arm and match nothing, exactly like HS.
pub fn lemma_matches(filter: &[String], lemma_name: &str) -> bool {
    match filter.len() {
        0 => return true,
        1 if filter[0].is_empty() => return true,
        2 if filter[0].is_empty() && filter[1].is_empty() => return true,
        _ => {}
    }
    filter.iter().any(|pat| {
        if let Some(prefix) = pat.strip_suffix('*') {
            lemma_name.starts_with(prefix)
        } else {
            pat == lemma_name
        }
    })
}

// =============================================================================
// Help / version text
// =============================================================================

/// The version string the binary prints in response to `--version`.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Git revision + branch + build timestamp, populated by `build.rs`.
pub const GIT_REV: &str = env!("TAMARIN_GIT_REV");
pub const GIT_BRANCH: &str = env!("TAMARIN_GIT_BRANCH");
pub const BUILD_TIMESTAMP: &str = env!("TAMARIN_BUILD_TIMESTAMP");

/// `--version` output.  Mirrors HS `--version` handling (Console.hs:328):
/// `putStrLn versionStr` (the banner + license) is emitted first, THEN
/// `ensureMaude` prints the `maude tool:` / ` checking version:` /
/// ` checking installation:` self-check lines, and finally
/// `getVersionIO` emits the `Generated from:` block (Console.hs:86-91).
///
/// In `ensureMaude` (Console.hs:151-165) ` checking version: ` carries
/// the *maude* version followed by `. OK.` (`Right (strip out ++ ". OK.")`),
/// not the tamarin banner.  HS additionally writes the self-check lines to
/// stderr while the banner/`Generated from:` go to stdout; we keep a single
/// combined string here for simplicity, but preserve HS's line ORDER.
pub fn version_text() -> String {
    let maude_version = detect_maude_version_pub();
    let maude_ok = maude_version.is_some();
    let mv = maude_version.unwrap_or_else(|| "unknown".to_string());
    let ok = if maude_ok { "OK." } else { "FAILED." };
    format!(
        // versionStr: banner + license (Console.hs:220-231).
        "tamarin-prover {VERSION}, (C) David Basin, Cas Cremers, Jannik Dreier, Simon Meier, Ralf Sasse, Benedikt Schmidt, 2010-2023\n\
         \n\
         This program comes with ABSOLUTELY NO WARRANTY. It is free software, and you\n\
         are welcome to redistribute it according to its LICENSE, see\n\
         'https://github.com/tamarin-prover/tamarin-prover/blob/master/LICENSE'.\n\
         maude tool: 'maude'\n\
         \x20checking version: {mv}. {ok}\n\
         \x20checking installation: {ok}\n\
         Generated from:\n\
         Tamarin version {VERSION}\n\
         Maude version {mv}\n\
         Git revision: {GIT_REV}, branch: {GIT_BRANCH}\n\
         Compiled at: {BUILD_TIMESTAMP}\n",
    )
}

/// Probe `maude --version` on `PATH` and return the trimmed version
/// string when Maude is reachable, `None` otherwise.
///
/// Mirrors HS `maudePath = fromMaybe "maude" . findArg "withMaude"`
/// (Console.hs:84-85): when no `--with-maude` is supplied, HS probes the
/// bare `maude` binary on `PATH` — it never consults hardcoded
/// developer-box paths.  Use [`detect_maude_version_at`] to honor an
/// explicit `--with-maude` path.
pub fn detect_maude_version_pub() -> Option<String> {
    detect_maude_version_at("maude")
}

/// Probe `<path> --version` and return the trimmed version string when
/// the binary is reachable, `None` otherwise.  Callers that have an
/// explicit `--with-maude` path (e.g. `run::run_test`/`run::run_variants`)
/// should pass it here so the reported version matches the binary the
/// prover will actually invoke (HS `ensureMaude` uses `maudePath as`).
pub fn detect_maude_version_at(path: &str) -> Option<String> {
    if let Ok(out) = std::process::Command::new(path).arg("--version").output() {
        if out.status.success() {
            let s = String::from_utf8_lossy(&out.stdout);
            // Maude prints just the version number, e.g. "3.5.1".
            let v = s.trim().to_string();
            if !v.is_empty() {
                return Some(v);
            }
        }
    }
    None
}

pub fn help_text() -> String {
    let mut s = String::new();
    s.push_str("tamarin-prover [COMMAND] ... [OPTIONS] FILES\n");
    s.push_str("  Security protocol analysis and verification (Rust port).\n");
    s.push('\n');
    s.push_str("Commands:\n");
    s.push_str("  interactive  Start a web-server to construct proofs interactively.\n");
    s.push_str("  variants     Compute intruder-rule variants (NOT YET PORTED).\n");
    s.push_str("  test         Self-test (NOT YET PORTED).\n");
    s.push('\n');
    s.push_str("Interactive-mode flags (used with the `interactive` subcommand):\n");
    s.push_str("  -p --port=PORT                        Port to listen on (default 3001).\n");
    s.push_str("  -i --interface=INTERFACE              Interface to listen on (default 127.0.0.1).\n");
    s.push_str("     --image-format=PNG|SVG             Image format for graphs (default SVG).\n");
    s.push_str("     --debug                            Show server debugging output.\n");
    s.push_str("     --no-logging                       Suppress web server logs.\n");
    s.push_str("     --data-dir=DIR                     Override path to the bundled `data/` dir.\n");
    s.push('\n');
    s.push_str("Lemma selection / proof options:\n");
    s.push_str("     --prove[=LEMMAPREFIX*|LEMMANAME]   Prove the named lemma(s). Repeatable.\n");
    s.push_str("     --prove-all                        Prove every lemma.\n");
    s.push_str("     --lemma[=LEMMAPREFIX*|LEMMANAME]   Restrict to lemma(s) by name/prefix.\n");
    s.push_str("     --stop-on-trace=DFS|BFS|SEQDFS|SORRY|NONE   Trace search policy.\n");
    s.push_str("  -b --bound=INT                        Bound proof depth.\n");
    s.push_str("     --heuristic=...                    Heuristic ranking sequence.\n");
    s.push_str("  -s --saturation=N                     Saturation iterations.\n");
    s.push_str("  -c --open-chains=N                    Open-chain bound.\n");
    s.push_str("  -d --derivcheck-timeout=N             Derivation check timeout.\n");
    s.push_str("     --auto-sources                     Auto-generate sources lemmas.\n");
    s.push_str("     --oraclename=FILE                  Oracle file path.\n");
    s.push_str("     --oracle-only                      Stop if oracle ranks no goals.\n");
    s.push_str("     --partial-evaluation=SUMMARY|VERBOSE   Partial-evaluation mode.\n");
    s.push('\n');
    s.push_str("Parser options:\n");
    s.push_str("  -D --defines=STRING                   Define pseudo-preprocessor flag.\n");
    s.push_str("     --diff                             Diff (observational equivalence) mode.\n");
    s.push_str("     --quit-on-warning                  Treat wellformedness warnings as fatal.\n");
    s.push_str("     --parse-only                       Just parse + pretty-print.\n");
    s.push_str("     --precompute-only                  Just run precomputation.\n");
    s.push_str("     --processors=N                     Rayon worker count for internal parallelism.\n");
    s.push_str("                                        Default: available_parallelism() (full machine).\n");
    s.push_str("                                        N=1 → byte-identical to sequential output.\n");
    s.push_str("     --maude-processes=M                Maude subprocesses in the per-task pool.\n");
    s.push_str("                                        Default: max(1, processors / 2).  Each costs\n");
    s.push_str("                                        ~30-100 MB RAM; lower if memory is tight.\n");
    s.push_str("                                        M=1 → single Maude (pre-pool behaviour).\n");
    s.push('\n');
    s.push_str("Output:\n");
    s.push_str("  -o --output=FILE                      Write analyzed theory to FILE.\n");
    s.push_str("  -O --Output=DIR                       Write to DIR/<basename>_analyzed.spthy.\n");
    s.push_str("  -m --output-module=MOD                Output module selector.\n");
    s.push_str("     --output-json=FILE                 Serialize traces to JSON.\n");
    s.push_str("     --output-dot=FILE                  Serialize traces to dot.\n");
    s.push('\n');
    s.push_str("Tools:\n");
    s.push_str("     --with-maude=PATH                  Path to `maude` binary.\n");
    s.push_str("     --with-dot=PATH                    Path to `dot`.\n");
    s.push_str("     --with-json=PATH                   Path to JSON tool.\n");
    s.push('\n');
    s.push_str("Misc:\n");
    s.push_str("     --quiet                            Suppress progress output.\n");
    s.push_str("  -v --verbose                          Verbose proof-search output.\n");
    s.push_str("     --no-reuse                         Do not export reuse lemmas.\n");
    s.push_str("     --no-restrictions                  Do not export restrictions.\n");
    s.push_str("     --replication-bound=N              Replication bound for DeepSec.\n");
    s.push_str("     --no-compress                      Do not compress sequents.\n");
    s.push_str("  -h --help                             Display this help.\n");
    s.push_str("  -V --version                          Print version.\n");
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(args: &[&str]) -> Args {
        parse_args(&args.iter().map(|s| s.to_string()).collect::<Vec<_>>()).expect("parse")
    }

    #[test]
    fn default_is_batch() {
        let a = parse(&[]);
        assert_eq!(a.subcommand, Subcommand::Batch);
        assert!(a.in_files.is_empty());
        assert!(!a.prove_mode);
    }

    #[test]
    fn positional_file() {
        let a = parse(&["foo.spthy", "bar.spthy"]);
        assert_eq!(a.in_files, vec!["foo.spthy", "bar.spthy"]);
    }

    #[test]
    fn prove_with_value() {
        let a = parse(&["--prove=secrecy", "x.spthy"]);
        assert!(a.prove_mode);
        assert_eq!(a.lemma_names, vec!["secrecy".to_string()]);
        assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
    }

    #[test]
    fn prove_bare_means_all() {
        let a = parse(&["--prove", "x.spthy"]);
        assert!(a.prove_mode);
        assert_eq!(a.lemma_names, vec!["".to_string()]);
        assert_eq!(a.in_files, vec!["x.spthy".to_string()]);
    }

    #[test]
    fn prove_all_alias() {
        let a = parse(&["--prove-all", "x.spthy"]);
        assert!(a.prove_mode);
        assert!(a.prove_all);
        assert_eq!(a.lemma_names, vec!["".to_string()]);
    }

    #[test]
    fn prove_repeated() {
        let a = parse(&["--prove=foo", "--prove=bar*", "x.spthy"]);
        assert_eq!(a.lemma_names, vec!["foo", "bar*"]);
    }

    #[test]
    fn maude_path_short_and_long() {
        let a = parse(&["--with-maude=/opt/maude/maude"]);
        assert_eq!(a.maude_path.as_deref(), Some("/opt/maude/maude"));
        let a = parse(&["--with-maude", "/opt/maude/maude"]);
        assert_eq!(a.maude_path.as_deref(), Some("/opt/maude/maude"));
    }

    #[test]
    fn output_file_and_dir() {
        let a = parse(&["-o", "out.spthy", "input.spthy"]);
        assert_eq!(a.output_file.as_deref(), Some("out.spthy"));
        let a = parse(&["-O", "outdir", "input.spthy"]);
        assert_eq!(a.output_dir.as_deref(), Some("outdir"));
        let a = parse(&["--output=foo.spthy"]);
        assert_eq!(a.output_file.as_deref(), Some("foo.spthy"));
        let a = parse(&["--Output=bar"]);
        assert_eq!(a.output_dir.as_deref(), Some("bar"));
    }

    #[test]
    fn quiet_and_verbose_flags() {
        let a = parse(&["--quiet", "--verbose"]);
        assert!(a.quiet);
        assert!(a.verbose);
    }

    #[test]
    fn bound_short_and_long() {
        let a = parse(&["-b", "12"]);
        assert_eq!(a.bound, Some(12));
        let a = parse(&["--bound=99"]);
        assert_eq!(a.bound, Some(99));
    }

    #[test]
    fn saturation_short_and_long() {
        let a = parse(&["-s", "7"]);
        assert_eq!(a.saturation, Some(7));
        let a = parse(&["--saturation=4"]);
        assert_eq!(a.saturation, Some(4));
    }

    #[test]
    fn open_chains_short_and_long() {
        let a = parse(&["-c", "20"]);
        assert_eq!(a.open_chains, Some(20));
        let a = parse(&["--open-chains=11"]);
        assert_eq!(a.open_chains, Some(11));
    }

    #[test]
    fn heuristic_passthrough() {
        let a = parse(&["--heuristic=S"]);
        assert_eq!(a.heuristic.as_deref(), Some("S"));
    }

    #[test]
    fn stop_on_trace_known() {
        let a = parse(&["--stop-on-trace=DFS"]);
        assert_eq!(a.stop_on_trace, Some(StopOnTrace::Dfs));
        let a = parse(&["--stop-on-trace=BFS"]);
        assert_eq!(a.stop_on_trace, Some(StopOnTrace::Bfs));
        let a = parse(&["--stop-on-trace=SeqDFS"]);
        assert_eq!(a.stop_on_trace, Some(StopOnTrace::SeqDfs));
        let a = parse(&["--stop-on-trace=NONE"]);
        assert_eq!(a.stop_on_trace, Some(StopOnTrace::None));
    }

    #[test]
    fn stop_on_trace_unknown_is_err() {
        let r = parse_args(
            &["--stop-on-trace=banana".to_string()],
        );
        assert!(r.is_err());
    }

    #[test]
    fn diff_flag_parsed() {
        let a = parse(&["--diff", "x.spthy"]);
        assert!(a.diff);
    }

    #[test]
    fn quit_on_warning_parsed() {
        let a = parse(&["--quit-on-warning"]);
        assert!(a.quit_on_warning);
    }

    #[test]
    fn defines_repeatable() {
        let a = parse(&["-DFLAG_A", "--defines=FLAG_B"]);
        assert_eq!(a.defines, vec!["FLAG_A", "FLAG_B"]);
    }

    #[test]
    fn parse_only_and_precompute_only() {
        let a = parse(&["--parse-only"]);
        assert!(a.parse_only);
        let a = parse(&["--precompute-only"]);
        assert!(a.precompute_only);
    }

    #[test]
    fn interactive_subcommand_recognised() {
        let a = parse(&["interactive", "x.spthy"]);
        assert_eq!(a.subcommand, Subcommand::Interactive);
    }

    #[test]
    fn variants_subcommand_recognised() {
        let a = parse(&["variants"]);
        assert_eq!(a.subcommand, Subcommand::Variants);
    }

    #[test]
    fn test_subcommand_recognised() {
        let a = parse(&["test"]);
        assert_eq!(a.subcommand, Subcommand::Test);
    }

    #[test]
    fn help_short_and_long() {
        let a = parse(&["--help"]);
        assert!(a.show_help);
        let a = parse(&["-h"]);
        assert!(a.show_help);
        let a = parse(&["-?"]);
        assert!(a.show_help);
    }

    #[test]
    fn version_short_and_long() {
        let a = parse(&["--version"]);
        assert!(a.show_version);
        let a = parse(&["-V"]);
        assert!(a.show_version);
    }

    #[test]
    fn output_module_parsed() {
        let a = parse(&["-m", "spthy"]);
        assert_eq!(a.output_module.as_deref(), Some("spthy"));
        let a = parse(&["--output-module=msr"]);
        assert_eq!(a.output_module.as_deref(), Some("msr"));
    }

    #[test]
    fn output_dot_and_json() {
        let a = parse(&["--output-dot=trace.dot", "--output-json=trace.json"]);
        assert_eq!(a.trace_dot.as_deref(), Some("trace.dot"));
        assert_eq!(a.trace_json.as_deref(), Some("trace.json"));
    }

    #[test]
    fn auto_sources_flag_parsed() {
        let a = parse(&["--auto-sources"]);
        assert!(a.auto_sources);
    }

    #[test]
    fn oracle_flags_parsed() {
        let a = parse(&["--oraclename=./my.oracle", "--oracle-only"]);
        assert_eq!(a.oracle_name.as_deref(), Some("./my.oracle"));
        assert!(a.oracle_only);
    }

    #[test]
    fn ddash_routes_to_positional() {
        let a = parse(&["--", "--prove", "weird-name"]);
        assert_eq!(a.in_files, vec!["--prove", "weird-name"]);
        assert!(!a.prove_mode);
    }

    #[test]
    fn unknown_long_flag_is_err() {
        let r = parse_args(&["--nonsense".to_string()]);
        assert!(r.is_err());
    }

    #[test]
    fn unknown_short_flag_is_err() {
        let r = parse_args(&["-Z".to_string()]);
        assert!(r.is_err());
    }

    #[test]
    fn lemma_matches_exact() {
        let f = vec!["foo".to_string()];
        assert!(lemma_matches(&f, "foo"));
        assert!(!lemma_matches(&f, "bar"));
    }

    #[test]
    fn lemma_matches_prefix_star() {
        let f = vec!["secrecy*".to_string()];
        assert!(lemma_matches(&f, "secrecy_alice"));
        assert!(lemma_matches(&f, "secrecy"));
        assert!(!lemma_matches(&f, "auth"));
    }

    #[test]
    fn lemma_matches_empty_filter_matches_all() {
        let f: Vec<String> = vec![];
        assert!(lemma_matches(&f, "anything"));
        let f = vec![String::new()];
        assert!(lemma_matches(&f, "anything"));
    }

    #[test]
    fn lemma_matches_any_in_filter() {
        let f = vec!["foo".to_string(), "bar*".to_string()];
        assert!(lemma_matches(&f, "foo"));
        assert!(lemma_matches(&f, "barbaric"));
        assert!(!lemma_matches(&f, "baz"));
    }

    #[test]
    fn lemma_matches_two_empties_match_all() {
        // HS lemmaSelector special-cases `["", ""]` to True.
        let f = vec![String::new(), String::new()];
        assert!(lemma_matches(&f, "anything"));
    }

    #[test]
    fn lemma_matches_three_empties_match_nothing() {
        // HS lemmaSelector only special-cases null/[""]/["",""]; three
        // bare entries fall through to `any lemmaMatches` and an empty
        // pattern only matches a lemma literally named "".
        let f = vec![String::new(), String::new(), String::new()];
        assert!(!lemma_matches(&f, "anything"));
        assert!(lemma_matches(&f, ""));
    }

    #[test]
    fn clustered_boolean_shorts() {
        // GNU-style clustering: `-vh` sets both verbose and help.
        let a = parse(&["-vh"]);
        assert!(a.verbose);
        assert!(a.show_help);
        let a = parse(&["-hV"]);
        assert!(a.show_help);
        assert!(a.show_version);
    }

    #[test]
    fn clustered_bool_then_value_short() {
        // A value-taking short ends the cluster, consuming the rest as
        // its inline value: `-vb12` = verbose + bound 12.
        let a = parse(&["-vb12"]);
        assert!(a.verbose);
        assert_eq!(a.bound, Some(12));
    }

    #[test]
    fn partial_eval_unknown_message() {
        let r = parse_args(&["--partial-evaluation=banana".to_string()]);
        match r {
            Err(CliError::Msg(m)) => {
                assert_eq!(m, "partial-evaluation: unknown option");
            }
            _ => panic!("expected error"),
        }
    }

    #[test]
    fn maude_processes_parsed() {
        let a = parse(&["--maude-processes=3", "x.spthy"]);
        assert_eq!(a.maude_processes, Some(3));
    }

    #[test]
    fn maude_processes_zero_rejected() {
        let r = parse_args(&["--maude-processes=0".to_string()]);
        assert!(r.is_err());
    }

    #[test]
    fn effective_maude_processes_single_processor_forces_one() {
        let a = parse(&["--processors=1", "--maude-processes=8", "x.spthy"]);
        // When processors=1, pool size collapses to 1 regardless of
        // --maude-processes (no parallelism to exploit).
        assert_eq!(a.effective_maude_processes(), 1);
    }

    #[test]
    fn effective_maude_processes_default_is_half_processors() {
        let a = parse(&["--processors=8", "x.spthy"]);
        // 8/2 = 4 default
        assert_eq!(a.effective_maude_processes(), 4);
    }

    #[test]
    fn effective_maude_processes_explicit_override() {
        let a = parse(&["--processors=8", "--maude-processes=2", "x.spthy"]);
        assert_eq!(a.effective_maude_processes(), 2);
    }
}
