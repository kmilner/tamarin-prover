//! Parse + elaborate a `.spthy` file into a [`TheoryEntry`].

use chrono::Local;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tamarin_parser::parse_theory;
use tamarin_parser::wf::WfError;
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
pub fn load_from_path(
    path: &Path,
    maude_path: &str,
    derivcheck_timeout: u32,
) -> Result<TheoryEntry, LoadError> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| LoadError::Io(format!("{}: {}", path.display(), e)))?;
    load_from_source(
        &src, TheoryOrigin::Local(PathBuf::from(path)), maude_path, derivcheck_timeout)
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
    derivcheck_timeout: u32,
) -> Result<TheoryEntry, LoadError> {
    let mut parser_theory = parse_theory(src, &[])
        .map_err(|e| LoadError::Parse(format!("{:?}", e)))?;

    // HS `liftedAddProtoRule` (Theory/Text/Parser.hs:166-193) expands each
    // rule's `_restrict(φ)` into a fresh `Restr_<rule>_<i>` restriction
    // (inserted before the rule) and rewrites the rule's actions DURING
    // parsing.  RS captures `_restrict` into `Rule.embedded_restrictions`
    // at parse time; run the lifting pass here, immediately after parse and
    // BEFORE the wellformedness clone / elaboration / SAPIC translation —
    // the exact position the CLI uses (run.rs:507) — so the transformed
    // parser theory drives every web renderer (rules / source / message /
    // graphs / sequents).
    tamarin_theory::rule_restriction::lift_rule_restrictions(&mut parser_theory)
        .map_err(|e| LoadError::Parse(format!(
            "_restrict expansion failed: {}", e.message)))?;

    // Wellformedness report — computed by the SAME pipeline `--prove` runs
    // (`run.rs`'s `checkWellformedness`, mirroring HS `TheoryLoader.hs`), so the
    // interactive web UI surfaces exactly the warnings HS does.  HS runs
    // `checkWellformedness` at theory load (before any proving), so running it
    // here — including the Maude-backed derivation check in the block below — is
    // faithful.  The result feeds two renderings: the `/* WARNING: ... */`
    // comment in the source/message routes (`format_wf_block`) and the
    // `<div class="wf-warning">` header banner in help/overview (`errors_html`).
    //
    // Static checks run on the PRE-translation parsed theory (HS runs
    // `check_theory` BEFORE the SAPIC `translate` pass, run.rs:517-528).  HS
    // `thyProtoRules` applies `applyMacroInRule` to every rule before the
    // checks, so clone + macro-expand first.
    let parsed_for_wf = {
        let mut tmp = parser_theory.clone();
        tamarin_theory::macro_expand::expand_theory_macros(&mut tmp);
        tmp
    };
    let mut wf_report = tamarin_parser::wf::check_theory(&parsed_for_wf);
    // Strip the STATIC "Message Derivation Checks" entry — the dynamic,
    // Maude-backed check in the maude block below replaces it (run.rs:527-528).
    wf_report.retain(|e| e.topic != "Message Derivation Checks");

    let mut typed = elaborate(&parser_theory)
        .map_err(|e| LoadError::Elaborate(e.message))?;
    let maude_sig = typed.signature.maude_sig.clone();

    // Subterm-convergence check on the signature's subterm-rule set
    // (run.rs:577-580): replace `check_theory`'s AST-level placeholder with the
    // signature-driven, width-wrapped version now that the MaudeSig exists.
    wf_report.retain(|e| e.topic != "Subterm Convergence Warning");
    wf_report.extend(
        tamarin_theory::pretty_theory::subterm_convergence_report_wf(&maude_sig),
    );

    // Formula terms (run.rs:601-616): needs the elaborated MaudeSig
    // (reducible/irreducible funsym classification), so it runs here rather than
    // inside `check_theory`.  Insert BEFORE the guardedness / lemma-annotation
    // topics to match HS `formulaReports` order (8b before 8c/9).
    {
        let term_errors = tamarin_theory::check_terms::check_terms_wf(
            &parsed_for_wf, &maude_sig);
        if !term_errors.is_empty() {
            let insert_before = wf_report.iter().position(|e| {
                matches!(e.topic.as_str(),
                    " Formula guardedness"
                    | "Lemma annotations" | "Multiplication restriction of rules"
                    | "Nat Sorts" | "Subterm Convergence Warning"
                    | "Message Derivation Checks" | "Derivation Checks")
            }).unwrap_or(wf_report.len());
            let tail = wf_report.split_off(insert_before);
            wf_report.extend(term_errors);
            wf_report.extend(tail);
        }
    }

    // Formula guardedness (run.rs:638-656): each lemma/restriction formula that
    // cannot be converted to a guarded formula.  Runs on the PRE-translation
    // parser theory (HS `formulaReports`), before the SAPIC pass below.
    {
        let guard_errors = tamarin_theory::elaborate::check_guarded_wf(&parser_theory);
        if !guard_errors.is_empty() {
            let insert_before = wf_report.iter().position(|e| {
                matches!(e.topic.as_str(),
                    "Lemma annotations" | "Multiplication restriction of rules"
                    | "Nat Sorts" | "Subterm Convergence Warning"
                    | "Message Derivation Checks" | "Derivation Checks")
            }).unwrap_or(wf_report.len());
            let tail = wf_report.split_off(insert_before);
            wf_report.extend(guard_errors);
            wf_report.extend(tail);
        }
    }

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
    // HS `Sapic.checkWellformedness` (Warnings.hs) is part of `preReport`, which
    // is PREPENDED to the rest of the report (run.rs:685-695).  A hard
    // translation error still propagates as `LoadError::Elaborate`.
    let sapic_wf = tamarin_sapic::apply::apply_sapic(
        &mut parser_theory, &mut typed, user_set_heuristic,
    ).map_err(|e| LoadError::Elaborate(e.message))?;
    if !sapic_wf.is_empty() {
        let mut new_report = sapic_wf;
        new_report.extend(std::mem::take(&mut wf_report));
        wf_report = new_report;
    }

    // HS re-runs the full `checkWellformedness` on the TRANSLATED theory
    // (run.rs:698-731): re-run `factLhsOccurNoRhs` on the post-translation
    // parsed theory so SAPIC-only premise facts (e.g. a `Message(c,m)` consumed
    // by an `in(c,m)` with no producing `out`) are surfaced.  No-op for
    // non-SAPIC theories (pre- and post-translation rule sets are equal).
    if typed.is_sapic {
        let post_thy = {
            let mut tmp = parser_theory.clone();
            tamarin_theory::macro_expand::expand_theory_macros(&mut tmp);
            tmp
        };
        let topic = "Facts occur in the left-hand-side but not in any right-hand-side ";
        wf_report.retain(|e| e.topic != topic);
        let lhs_rhs = tamarin_parser::wf::fact_lhs_occur_no_rhs(&post_thy);
        if !lhs_rhs.is_empty() {
            let insert_before = wf_report.iter().position(|e| {
                matches!(e.topic.as_str(),
                    "Formula terms" | " Formula guardedness"
                    | "Lemma annotations" | "Multiplication restriction of rules"
                    | "Nat Sorts" | "Subterm Convergence Warning"
                    | "Message Derivation Checks" | "Derivation Checks")
            }).unwrap_or(wf_report.len());
            let tail = wf_report.split_off(insert_before);
            wf_report.extend(lhs_rhs);
            wf_report.extend(tail);
        }
    }

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

        // Dynamic Message Derivation Checks (run.rs:974-995): HS
        // `checkVariableDeducability`, gated by `--derivcheck-timeout` (HS
        // interactive default 5s).  The budget comes from ServerConfig
        // (CLI flag on the interactive path, 5s default otherwise) —
        // matching HS interactive, which honors the flag
        // (Main/Mode/Interactive.hs:62).  Needs the Maude handle; runs on
        // the POST-translation parser theory (`parser_theory`, matching
        // run.rs's `&parsed` at that point).
        let extra = tamarin_theory::deriv_check::check_message_derivation(
            &parser_theory, &maude, derivcheck_timeout,
        );
        wf_report.extend(extra);
    }

    // HS `makeWfErrorsHtml` (src/Web/Handler.hs:463-469) — the header-banner
    // rendering of the same report; empty string when the report is empty.
    let errors_html = make_wf_errors_html(&wf_report);

    Ok(TheoryEntry {
        idx: 0,
        name: typed.name.clone(),
        parser_theory: Arc::new(parser_theory),
        typed_theory: Arc::new(typed),
        origin,
        loaded_at: Local::now(),
        primary: true,
        wf_report,
        errors_html,
        proof_state: None,
    })
}

/// Build the HS `makeWfErrorsHtml` banner (`src/Web/Handler.hs:463-469`): wrap
/// the wellformedness report in a `<div class="wf-warning">`, prefixed by the
/// literal `WARNING: ...<br /><br />` line and followed by the report body
/// rendered exactly as HS's `renderHtmlDoc (htmlDoc $ prettyWfErrorReport
/// report)` — each source line HTML-escaped, its leading spaces turned into
/// `&nbsp;`, and a `<br/>` appended (HS `postprocessHtmlDoc`,
/// Text/PrettyPrint/Html.hs:157-162).  Empty report ⇒ empty string
/// (HS `makeWfErrorsHtml [] = ""`).
///
/// `format_wf_block` is reused as the single source of truth for the report
/// body: strip its `/* ... */` framing to recover the same
/// `prettyWfErrorReport` text HS feeds to `renderHtmlDoc`, then re-render it
/// HS-web-style.  Line-wrap width may differ from HS's web render, but the
/// parity gate compares structure/text (whitespace-collapsed), so only the
/// word tokens must match — which they do (the body is byte-identical to the
/// `--prove` `/* */` block, itself HS-byte-faithful).
fn make_wf_errors_html(report: &[WfError]) -> String {
    if report.is_empty() {
        return String::new();
    }
    let block = tamarin_theory::pretty_theory::format_wf_block(report);
    // `format_wf_block` frames the body as
    //   "/*\nWARNING: the following wellformedness checks failed!\n\n<body>*/"
    // where <body> is the byte-exact `prettyWfErrorReport` text.  Strip the
    // fixed prefix/suffix to recover just <body>.
    const PREFIX: &str = "/*\nWARNING: the following wellformedness checks failed!\n\n";
    let body = block
        .strip_prefix(PREFIX)
        .and_then(|b| b.strip_suffix("*/"))
        .unwrap_or(&block);
    // Mirror HS `postprocessHtmlDoc = unlines . map (addBreak . indent) . lines`
    // over the HTML-escaped body: each line's leading spaces become `&nbsp;`,
    // the rest is entity-escaped, and `<br/>` is appended; lines joined by `\n`
    // with a trailing `\n` (unlines).
    let mut rendered = String::new();
    for line in body.lines() {
        let n_lead = line.len() - line.trim_start_matches(' ').len();
        for _ in 0..n_lead {
            rendered.push_str("&nbsp;");
        }
        rendered.push_str(&crate::handlers::root::html_escape(&line[n_lead..]));
        rendered.push_str("<br/>\n");
    }
    // HS `makeWfErrorsHtml`: <div> + literal WARNING line + rendered body + </div>.
    format!(
        "<div class=\"wf-warning\">\n\
         WARNING: the following wellformedness checks failed!<br /><br />\n\
         {rendered}\n</div>",
    )
}
