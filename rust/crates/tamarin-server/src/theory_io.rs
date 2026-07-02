//! Parse + elaborate a `.spthy` file into a [`TheoryEntry`].

use chrono::Local;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tamarin_parser::parse_theory;
use tamarin_term::maude_proc::MaudeHandle;
use tamarin_theory::elaborate::elaborate;

use crate::state::{TheoryEntry, TheoryOrigin};

#[derive(Debug)]
pub enum LoadError {
    Io(String),
    Parse(String),
    Elaborate(String),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Io(s) => write!(f, "IO error: {}", s),
            LoadError::Parse(s) => write!(f, "parse error: {}", s),
            LoadError::Elaborate(s) => write!(f, "elaboration error: {}", s),
        }
    }
}
impl std::error::Error for LoadError {}

/// Read the file, parse it, elaborate it, and return a [`TheoryEntry`].
///
/// `entry.idx` is left as `0`; [`TheoryStore::insert`] assigns the
/// real index.
pub fn load_from_path(path: &Path, maude_path: &str) -> Result<TheoryEntry, LoadError> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| LoadError::Io(format!("{}: {}", path.display(), e)))?;
    load_from_source(&src, TheoryOrigin::Local(PathBuf::from(path)), maude_path)
}

/// Parse + elaborate from a string (for the upload path), then "close"
/// the theory by pre-computing each protocol rule's AC-variants via
/// Maude (HS `closeTheory`), so the source / rules / overview renderers
/// can emit the `variants (modulo AC)` blocks byte-for-byte.  Variant
/// computation is best-effort: if Maude can't be started the theory is
/// still usable (rules just render without their variants block).
pub fn load_from_source(
    src: &str,
    origin: TheoryOrigin,
    maude_path: &str,
) -> Result<TheoryEntry, LoadError> {
    let mut parser_theory = parse_theory(src, &[])
        .map_err(|e| LoadError::Parse(format!("{:?}", e)))?;
    let mut typed = elaborate(&parser_theory)
        .map_err(|e| LoadError::Elaborate(e.message))?;

    // SAPIC `process:` translation — mirror `run.rs`'s CLI-side pass
    // (run.rs:658-696) so the web load path renders SAPIC theories exactly
    // like `--prove`.  Runs ONLY for `is_sapic` theories (exactly one
    // top-level `process:`); `apply_sapic` returns `Ok(vec![])` when
    // `!typed.is_sapic`, so it is safe to call unconditionally and leaves
    // non-process theories byte-unchanged.  It injects the generated MSR
    // rules + `single_session` restriction + `heuristic: p` into BOTH
    // `parser_theory` (which drives the web rules / source / message
    // renderers) and `typed` (for AC-variant pre-computation), so it MUST run
    // before `populate_rule_variants` below.  `user_set_heuristic` is true iff
    // a `heuristic:` item already populated `typed.heuristic` (HS
    // `addHeuristic` returns `Nothing` in that case).
    //
    // Install the user/builtin function-symbol flag sets
    // (`USER_PRIVATE_FUNS` / `USER_DESTRUCTOR_FUNS` / …) for the duration of
    // BOTH the SAPIC translation AND the variant pre-computation below.  These
    // thread-locals drive `term_to_lnterm`'s symbol resolution (privacy /
    // constructability); `elaborate()` sets them only for its own scope, so
    // without re-installing them here the SAPIC-injected rules' builtin
    // symbols (`rep` private, `check_rep` / `get_rep` destructors from
    // `locations-report`) re-elaborate with the default public-constructor
    // flags, serialising as `tamXC..` — which Maude rejects, leaving the rule
    // with "no variants".  The guard must therefore stay alive across the
    // `populate_rule_variants` call in the maude block below (it does: this
    // binding lives to the end of the function).
    let _sapic_funs_guard =
        tamarin_theory::elaborate::set_user_funs_for_theory(&parser_theory);
    let user_set_heuristic = !typed.heuristic.is_empty();
    // The SAPIC-process wellformedness warnings feed only the wf report, which
    // is out of scope on the web load path, so we discard them here; a hard
    // translation error still propagates as `LoadError::Elaborate`.
    let _ = tamarin_sapic::apply::apply_sapic(
        &mut parser_theory, &mut typed, user_set_heuristic,
    ).map_err(|e| LoadError::Elaborate(e.message))?;

    if let Ok(maude) = MaudeHandle::start(maude_path, typed.signature.maude_sig.clone()) {
        tamarin_theory::tools::rule_variants::populate_rule_variants(&mut typed, &maude, None);
        // Annotate per-rule loop breakers on the stored theory so the web
        // rules / source / message renderers emit HS's `// loop breaker: [<n>]`
        // comments — HS `prettyClosedProtoRule` reads them from the
        // `ProtoRuleACInfo` baked into every closed rule.  Our prover computes
        // them inside `ProofContext::new` on a local copy; mirror `run.rs`'s
        // CLI-side pass here on the load path (identical writeback in source
        // order) so the byte-faithful `web_proto_rules` printer has them.
        use tamarin_theory::theory::{OpenProtoRule, TheoryItem};
        let mut rules: Vec<OpenProtoRule> = typed.items.iter().filter_map(|i| match i {
            TheoryItem::Rule(r) => Some(r.clone()),
            _ => None,
        }).collect();
        tamarin_theory::constraint::solver::context::annotate_loop_breakers(&mut rules, &maude);
        let mut iter = rules.into_iter();
        for item in typed.items.iter_mut() {
            if let TheoryItem::Rule(opr) = item {
                if let Some(updated) = iter.next() {
                    opr.loop_breakers = updated.loop_breakers;
                }
            }
        }
    }
    Ok(TheoryEntry {
        idx: 0,
        name: typed.name.clone(),
        parser_theory: Arc::new(parser_theory),
        typed_theory: Arc::new(typed),
        origin,
        loaded_at: Local::now(),
        primary: true,
        errors_html: String::new(),
        proof_state: None,
    })
}
