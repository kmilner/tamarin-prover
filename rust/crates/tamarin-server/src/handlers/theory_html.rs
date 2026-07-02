//! HTML rendering for theory pages.
//!
//! This mirrors a *minimal* slice of Haskell's `Web.Theory` + `Web.Hamlet`
//! pretty printing — enough to surface the lemmas, restrictions and
//! rules in the UI, and to wire `Autoprove` links the frontend
//! recognises.

use crate::handlers::path_parse::{url_path_escape, SourceKind, TheoryPath};
use crate::handlers::root::html_escape;
use crate::state::TheoryEntry;

use tamarin_theory::pretty_formula::pretty_formula;
use tamarin_theory::theory::{LemmaAttr, TraceQuantifier};
use tamarin_theory::constraint::solver::proof_method::{ProofMethod, Result as MethodResult};
use tamarin_theory::constraint::solver::search::{proof_status, ProofNode, ProofStatus};

/// Full overview/framing page (the one served at `/thy/trace/<idx>/overview/...`).
pub fn overview_page(entry: &TheoryEntry, path: &TheoryPath) -> String {
    let header_html = header(entry);
    let proof_state = proof_state(entry);
    let main_view = path_html(entry, path);
    format!(
        r##"<!DOCTYPE html>
<html><head><title>Theory: {name}</title>
<link rel="stylesheet" href="/static/css/intdot-style.css">
<link rel="stylesheet" href="/static/css/tamarin-prover-ui.css">
<link rel="stylesheet" href="/static/css/jquery-contextmenu.css">
<link rel="stylesheet" href="/static/css/smoothness/jquery-ui.css">
<script src="/static/js/jquery.js"></script>
<script src="/static/js/jquery-ui.js"></script>
<script src="/static/js/jquery-layout.js"></script>
<script src="/static/js/jquery-cookie.js"></script>
<script src="/static/js/jquery-superfish.js"></script>
<script src="/static/js/jquery-contextmenu.js"></script>
<script src="/static/js/tamarin-prover-ui.js"></script>
<script type="module" src="/static/js/intdot-graph.es.js"></script>
<script type="module" src="/static/js/intdot-staticgraph.es.js"></script>
<script type="module" src="/static/js/intdot-dynamicgraph.es.js"></script>
</head>
<body>
<p class="loading">Analyzing, please wait... <a id="cancel" href="#">Cancel</a></p>
<div class="ui-layout-north">{header_html}</div>
<div class="ui-layout-west">
  <h1 class="pane-head">Proof scripts</h1>
  <div id="proof-wrapper" class="scroll-wrapper">
    <div id="proof" class="monospace">{proof_state}</div>
  </div>
</div>
<div class="ui-layout-east">
  <h1 class="pane-head">&nbsp;Debug information</h1>
  <div id="debug-wrapper" class="scroll-wrapper">
    <div id="ui-debug-display"></div>
  </div>
</div>
<div class="ui-layout-center">
  <h1 id="main-title" class="pane-head">Visualization display</h1>
  <div id="main-wrapper" class="scroll-wrapper" tabindex="0">
    <div id="ui-main-display">{main_view}</div>
  </div>
</div>
<div id="dialog"></div>
<div id="confirm-dialog"></div>
<ul id="contextMenu">
  <li class="autoprove"><a href="#autoprove">Autoprove</a></li>
</ul>
</body>
</html>
"##,
        name = html_escape(&entry.name),
        header_html = header_html,
        proof_state = proof_state,
        main_view = main_view,
    )
}

fn header(entry: &TheoryEntry) -> String {
    // HS `headerTpl` (Web/Hamlet.hs:166-197): the Reload-file and
    // Append-modified-lemmas forms are gated on `isLocalOrigin origin`.
    let is_local = matches!(entry.origin, crate::state::TheoryOrigin::Local(_));
    let filename = html_escape(&format!("{}.spthy", entry.name));
    let reload_form = if is_local {
        format!(
            "<li><form class=\"ajax-form ajax-form-full reload-confirm\" method=\"POST\" \
             action=\"/thy/trace/{idx}/reload\">\
             <button class=\"nav-button\" type=\"submit\">Reload file</button></form></li>",
            idx = entry.idx)
    } else { String::new() };
    let append_form = if is_local {
        format!(
            "<li><form class=\"ajax-form\" method=\"POST\" \
             action=\"/thy/trace/{idx}/get_and_append/{filename}\">\
             <button class=\"link-button\" type=\"submit\">Append modified lemmas to file</button>\
             </form></li>",
            idx = entry.idx, filename = filename)
    } else { String::new() };
    format!(r##"
<div class="layout-pane-north">
  <div id="header-info">Running <a href="/"><span class="tamarin">Tamarin</span></a> {version} (Rust port)</div>
</div>
<div id="header-links">
<ul id="navigation">
  <li><a href="/">Index</a></li>
  {reload_form}
  <li><a href="#">Actions</a><ul>
    <li><a target="_blank" href="/thy/trace/{idx}/source">Show source</a></li>
    <li><a href="/thy/trace/{idx}/download/{filename}">Download source</a></li>
    {append_form}
  </ul></li>
  <li><a href="#">Options</a><ul class="list-with-toggles">
    <li><a id="abbrv-toggle" href="#">Abbreviate terms</a></li>
    <li><a id="agent-toggle" href="#">Clustering by role</a></li>
    <li><a id="auto-toggle"  href="#">Show annotation auto-sources</a></li>
    <li><a id="lvl0-toggle"  href="#">Graph simplification off</a></li>
    <li><a id="lvl1-toggle"  href="#">Graph simplification L1</a></li>
    <li><a id="lvl2-toggle"  href="#">Graph simplification L2</a></li>
    <li><a id="lvl3-toggle"  href="#">Graph simplification L3</a></li>
  </ul></li>
</ul>
</div>
"##,
        version = env!("CARGO_PKG_VERSION"),
        idx = entry.idx,
        filename = filename,
        reload_form = reload_form,
        append_form = append_form,
    )
}

/// Left-pane proof-state tree.  Faithful port of Haskell's `theoryIndex`
/// (`src/Web/Theory.hs:369-416`) → `lemmaIndex` (`src/Web/Theory.hs:296-329`)
/// → `proofIndex` (`src/Web/Theory.hs:223-257`) → `prettyProofWith`
/// (`Theory/Proof.hs:1078-1096`).  The frame is
///
/// ```text
/// theory <help-link>Name</help-link> begin
/// <Message theory>  <Multiset rewriting rules … (N)>  <Tactic(s)>
/// <Raw sources (N cases, …)>  <Refined sources (N cases, …)>
/// add lemma
/// <lemma_1 index>  …  <lemma_k index>
/// end
/// ```
///
/// Blank-line separators (`text ""`) are emitted as `<br>` and collapsed by
/// the parity normalizer; only element structure / link targets / visible
/// text are compared.
fn proof_state(entry: &TheoryEntry) -> String {
    let typed = &entry.typed_theory;
    let idx = entry.idx;
    let mut out = String::new();
    // `kwTheoryHeader $ linkToPath … ["help"] (text name)` = `theory <help> begin`.
    out.push_str(&format!(
        "theory <a class=\"internal-link help\" href=\"/thy/trace/{idx}/main/help\">{name}</a> begin<br><br>\n",
        idx = idx, name = html_escape(&entry.name)));
    // `overview n info p = linkToPath … [] (bold n <-> info)`.  Message /
    // Tactic pass `text ""` as info (a trailing space); rules / sources pass
    // their `(N …)` annotation.
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/message\"><strong>Message theory</strong> </a><br><br>\n",
        idx = idx));
    // `ruleLinkMsg = "Multiset rewriting rules" ++ (if null restrictions then ""
    // else " and restrictions")`; `rulesInfo = parens (length crProtocol)`.
    let has_restr = typed.restrictions().next().is_some();
    let rule_msg = if has_restr {
        "Multiset rewriting rules and restrictions"
    } else {
        "Multiset rewriting rules"
    };
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/rules\"><strong>{msg}</strong> ({n})</a><br><br>\n",
        idx = idx, msg = html_escape(rule_msg), n = proto_rule_count(entry)));
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/tactic\"><strong>Tactic(s)</strong> </a><br><br>\n",
        idx = idx));
    // `reqCasesLink name k = overview name (casesInfo k) (TheorySource k 0 0)`.
    // Note HS's "Refined sources " carries a trailing space inside `bold`.
    let (raw_n, raw_ch) = source_case_counts(entry, false);
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/cases/raw/0/0\"><strong>Raw sources</strong> {info}</a><br><br>\n",
        idx = idx, info = html_escape(&cases_info(raw_n, raw_ch))));
    let (ref_n, ref_ch) = source_case_counts(entry, true);
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/cases/refined/0/0\"><strong>Refined sources </strong> {info}</a><br><br>\n",
        idx = idx, info = html_escape(&cases_info(ref_n, ref_ch))));
    // `add lemma` for the very first slot (`TheoryAdd "<first>"`).
    out.push_str(&format!(
        "<a class=\"internal-link add\" href=\"/thy/trace/{idx}/main/add/%3Cfirst%3E\">add lemma</a><br><br>\n",
        idx = idx));

    // `vcat $ intersperse (text "") lemmas`.
    for l in typed.lemmas() {
        lemma_index(&mut out, entry, l);
        out.push_str("<br>\n");
    }

    // `kwEnd`.
    out.push_str("end\n");
    out
}

/// HS `length (getClassifiedRules thy)._crProtocol` — the count shown in the
/// `Multiset rewriting rules … (N)` link.  Equal to the number of rules the
/// `main/rules` page renders (`extraACRules ++ protoRules`), i.e.
/// `web_proto_rules.len()` plus the ISend/IRecv-style intruder members of
/// `crProtocol` (`ctx.intruder_rules` minus construction/destruction rules).
fn proto_rule_count(entry: &TheoryEntry) -> usize {
    let proto = tamarin_theory::pretty_theory::web_proto_rules(
        &entry.parser_theory, &entry.typed_theory).len();
    let extra = entry.proof_state.as_ref().map_or(0, |ps| {
        let ctx = ps.ctx.lock();
        ctx.intruder_rules.iter()
            .filter(|ir| !is_constr_intr(&ir.info) && !is_destr_intr(&ir.info))
            .count()
    });
    proto + extra
}

/// HS `casesInfo` rendering: `(N cases, deconstructions complete)` or
/// `(N cases, K partial deconstructions left)`.
fn cases_info(n_cases: usize, n_chains: usize) -> String {
    let chain_info = if n_chains == 0 {
        "deconstructions complete".to_string()
    } else {
        format!("{} partial deconstructions left", n_chains)
    };
    format!("({} cases, {})", n_cases, chain_info)
}

/// HS `lemmaIndex` (`src/Web/Theory.hs:296-329`): the lemma header
/// (`lemma Name [attrs]: <tq> "<formula>"`), the `edit lemma`/`delete lemma`
/// links, the `proofIndex` tree, then a trailing `add lemma`.  The header +
/// edit/delete are wrapped by HS in `markStatus (root color)` — a `hl_*` span
/// the normalizer unwraps, so we emit them plain.
fn lemma_index(out: &mut String, entry: &TheoryEntry,
               l: &tamarin_theory::theory::Lemma<tamarin_theory::theory::ProofSkeleton>) {
    let idx = entry.idx;
    let tq = match l.trace_quantifier {
        TraceQuantifier::AllTraces => "all-traces",
        TraceQuantifier::ExistsTrace => "exists-trace",
    };
    let attrs = render_attrs(&l.attributes);
    let formula = pretty_formula(&l.formula);
    let n_url = url_path_escape(&l.name);
    // `kwLemma <-> prettyLemmaName l <> colon` $-$ `nest 2 (sep [tq, "form"])`
    // $-$ `edit lemma <-> " or " <-> delete lemma`.
    out.push_str(&format!(
        "lemma {name}{attrs}: {tq} \"{f}\" \
         <a class=\"internal-link edit\" href=\"/thy/trace/{idx}/main/edit/{n_url}\">edit lemma</a> \
         or \
         <a class=\"internal-link delete\" href=\"/thy/trace/{idx}/main/delete/{n_url}\">delete lemma</a><br>\n",
        idx = idx,
        name = html_escape(&l.name),
        attrs = html_escape(&attrs),
        tq = tq,
        f = html_escape(&formula),
        n_url = n_url,
    ));
    // `proofIndex l._lName tidx renderUrl mkRoute annPrf` — the annotated
    // proof tree, rendered by `prettyProofWith ppStep ppCase . insertPaths`.
    let live_root = entry.proof_state.as_ref().and_then(|ps| ps.get_root(&l.name));
    match live_root {
        Some(root) => {
            let cx = PpCtx { idx, lemma: &l.name, tq: l.trace_quantifier };
            let path: Vec<String> = Vec::new();
            pp_prf(out, &cx, &path, &root);
        }
        None => {
            // No live proof state yet (lazily built): the lemma's root is a
            // fresh `Sorry Nothing`.  HS `proofIndex` of such a proof is
            // `ppCases (Sorry) [] = kwBy <> " " <> stepLink ["sorry-step"]`
            // (an `Unmarked`, unannotated-free `Sorry` step gets no
            // `remove-step`).  Emitting it keeps the lemma discoverable and
            // matches HS's freshly-loaded overview.
            out.push_str(&format!(
                "by <a class=\"internal-link proof-step sorry-step\" \
                 href=\"/thy/trace/{idx}/main/proof/{n_url}\">sorry</a>",
                idx = idx, n_url = n_url));
        }
    }
    out.push_str("<br>\n");
    // `linkToPath renderUrl (TheoryAdd l._lName) ["add"] "add lemma"`.
    out.push_str(&format!(
        "<a class=\"internal-link add\" href=\"/thy/trace/{idx}/main/add/{n_url}\">add lemma</a><br>\n",
        idx = idx, n_url = n_url));
}

/// Addressing context threaded through the `proofIndex` recursion.
struct PpCtx<'a> {
    idx: usize,
    lemma: &'a str,
    tq: TraceQuantifier,
}

/// HS `ProofStepColor` after `annotateLemmaProof` — the per-step highlight.
#[derive(Clone, Copy, PartialEq)]
enum StepColor { Unmarked, Green, Red, Yellow }

/// HS `annotateLemmaProof.interpret` (`src/Web/Theory.hs:2183-2192`): map the
/// aggregate subtree [`ProofStatus`] + trace quantifier to a highlight colour.
fn interpret_color(tq: TraceQuantifier, status: ProofStatus) -> StepColor {
    use ProofStatus::*;
    match status {
        Incomplete | Undetermined => StepColor::Unmarked,
        Unfinishable | Invalidated => StepColor::Yellow,
        TraceFound => match tq {
            TraceQuantifier::AllTraces => StepColor::Red,
            TraceQuantifier::ExistsTrace => StepColor::Green,
        },
        Complete => match tq {
            TraceQuantifier::AllTraces => StepColor::Green,
            TraceQuantifier::ExistsTrace => StepColor::Red,
        },
    }
}

/// HS `prettyProofWith.ppPrf` / `ppCases` (`Theory/Proof.hs:1080-1096`):
/// dispatch on the node's children shape.
fn pp_prf(out: &mut String, cx: &PpCtx, path: &[String], node: &ProofNode) {
    let children = &node.children;
    if children.is_empty() {
        // `ppCases ps@(Finished Solved) [] = prettyStep ps` (SOLVED leaf,
        // no `by`); every other leaf is `prettyCase ps (kwBy<>" ") <> step`.
        if !matches!(node.method, ProofMethod::Finished(MethodResult::Solved)) {
            out.push_str("by ");
        }
        pp_step(out, cx, path, node);
    } else if children.len() == 1 && children.contains_key("") {
        // `ppCases ps [("", prf)] = prettyStep ps $-$ ppPrf prf` — single
        // unnamed continuation, no `case` label.
        pp_step(out, cx, path, node);
        out.push_str("<br>\n");
        let mut child_path = path.to_vec();
        child_path.push(String::new());
        pp_prf(out, cx, &child_path, &children[""]);
    } else {
        // `ppCases ps cases = prettyStep ps $-$
        //    (vcat $ intersperse (prettyCase ps kwNext) $ map ppCase cases)
        //    $-$ prettyCase ps kwQED`.
        pp_step(out, cx, path, node);
        out.push_str("<br>\n");
        for (i, (name, child)) in children.iter().enumerate() {
            if i > 0 { out.push_str("next<br>\n"); }
            pp_case(out, cx, path, name, child);
        }
        out.push_str("qed");
    }
}

/// HS `prettyProofWith.ppCase` (`Theory/Proof.hs:1094-1096`):
/// `nest 2 $ (prettyCase (root prf) (kwCase <-> name)) $-$ ppPrf prf`.  The
/// `case <name>` keyword is wrapped by HS in `markStatus`, a `hl_*` span the
/// normalizer unwraps, so we emit it plain.
fn pp_case(out: &mut String, cx: &PpCtx, path: &[String], name: &str, child: &ProofNode) {
    out.push_str(&format!("case {}<br>\n", html_escape(name)));
    let mut child_path = path.to_vec();
    child_path.push(name.to_string());
    pp_prf(out, cx, &child_path, child);
    out.push_str("<br>\n");
}

/// HS `proofIndex.ppStep` (`src/Web/Theory.hs:232-257`): a coloured
/// `proof-step` link carrying the pretty method, plus (unless the method is
/// `Sorry`) an empty `remove-step` link at the same path.  An unannotated
/// step (HS `psInfo == Nothing`) renders as a plain `hl_superfluous` span with
/// no link.
fn pp_step(out: &mut String, cx: &PpCtx, path: &[String], node: &ProofNode) {
    let label = html_escape(&crate::handlers::proof_tree::method_label(&node.method));
    if !node.annotated {
        // `superfluousStep = withTag "span" [("class","hl_superfluous")] ppMethod`.
        out.push_str(&format!("<span class=\"hl_superfluous\">{}</span>", label));
        return;
    }
    let url = format!(
        "/thy/trace/{idx}/main/proof/{lemma}{path}",
        idx = cx.idx, lemma = url_path_escape(cx.lemma), path = encode_index_path(path));
    let color = interpret_color(cx.tq, proof_status(node));
    let cls = match color {
        StepColor::Unmarked => "sorry-step",
        StepColor::Green => "hl_good",
        StepColor::Red => "hl_bad",
        StepColor::Yellow => "hl_medium",
    };
    out.push_str(&format!(
        "<a class=\"internal-link proof-step {cls}\" href=\"{url}\">{label}</a>",
        cls = cls, url = url, label = label));
    // `invalidatedStep`: an `Invalidated` step also gets a `verify it` link.
    if color == StepColor::Yellow && matches!(node.method, ProofMethod::Invalidated) {
        out.push_str(&format!(
            " <a class=\"internal-link hl_medium\" href=\"/thy/trace/{idx}/verify/proof/{lemma}\">verify it</a>",
            idx = cx.idx, lemma = url_path_escape(cx.lemma)));
    }
    // `<> case psMethod step of Sorry _ -> emptyDoc; _ -> removeStep`.
    if !matches!(node.method, ProofMethod::Sorry(_)) {
        out.push_str(&format!(
            "<a class=\"internal-link remove-step\" href=\"{url}\"></a>", url = url));
    }
}


fn encode_index_path(path: &[String]) -> String {
    if path.is_empty() { return String::new(); }
    let mut s = String::new();
    for seg in path {
        s.push('/');
        let escaped = if seg.is_empty() { "_".to_string() }
            else if seg.starts_with('_') { format!("_{}", seg) }
            else { seg.to_string() };
        s.push_str(&url_path_escape(&escaped));
    }
    s
}

fn render_attrs(attrs: &[LemmaAttr]) -> String {
    if attrs.is_empty() { return String::new(); }
    let parts: Vec<String> = attrs.iter().map(|a| match a {
        LemmaAttr::Sources => "sources".into(),
        LemmaAttr::Reuse => "reuse".into(),
        LemmaAttr::DiffReuse => "diff_reuse".into(),
        LemmaAttr::UseInduction => "use_induction".into(),
        LemmaAttr::HideLemma(s) => format!("hide_lemma={}", s),
        LemmaAttr::Heuristic(s) => format!("heuristic={}", s),
        LemmaAttr::Output(xs) => format!("output={}", xs.join(",")),
        LemmaAttr::Left => "left".into(),
        LemmaAttr::Right => "right".into(),
        LemmaAttr::Hint(s) => s.clone(),
    }).collect();
    format!(" [{}]", parts.join(", "))
}

/// Main pane: render the content for a given path.
pub fn path_html(entry: &TheoryEntry, path: &TheoryPath) -> String {
    let typed = &entry.typed_theory;
    match path {
        TheoryPath::Help => help_html(entry),
        TheoryPath::Rules => rules_html(entry),
        TheoryPath::Message => message_html(entry),
        TheoryPath::Tactic => {
            // HS `tacticSnippet` (Web/Theory.hs:934) =
            //   ppSection "Tactic(s)" (prettyTactic <$> _thyTactic)
            // ppSection h s = <h2>h</h2> $$ <p class="monospace rules">
            //                   vcat (intersperse (text "") s)
            let body: Vec<String> = typed.tactic.iter().map(|t| t.render()).collect();
            format!(
                "<h2>Tactic(s)</h2>\n<p class=\"monospace rules\">{}</p>",
                body.join("\n\n"),
            )
        }
        // HS renders `text "this is a mistake"` for the bare lemma path
        // (`htmlThyPath` `TheoryLemma _`, Web/Theory.hs:1068) — the UI never
        // navigates here (it uses the proof path); mirror it verbatim.
        TheoryPath::Lemma(_) => "this is a mistake".into(),
        TheoryPath::Proof { lemma, sub } => proof_html(entry, lemma, sub),
        TheoryPath::Method { lemma, sub, .. } => proof_html(entry, lemma, sub),
        TheoryPath::Source { kind, .. } => sources_html(entry, kind),
        // HS `htmlThyPath` arms `TheoryEdit`/`TheoryAdd`/`TheoryDelete`
        // (`src/Web/Theory.hs:1025-1133`).
        TheoryPath::Edit(name) => edit_lemma_html(entry, name),
        TheoryPath::Add(name) => add_lemma_html(name),
        TheoryPath::Delete(name) => delete_lemma_html(name),
    }
}

/// HS `htmlThyPath (TheoryEdit name)` (`src/Web/Theory.hs:1025-1065`).  The
/// textarea holds the lemma's `_lPlaintext` (HS `getLemmaPlaintext`,
/// `src/Web/Handler.hs:178-187`); a missing lemma falls back to the same
/// "Enter your new Lemma" default as Add.  `rows = 2 + (#newlines in plaintext)`
/// (HS `textHeight`).
fn edit_lemma_html(entry: &TheoryEntry, name: &str) -> String {
    let plaintext = entry.typed_theory.lookup_lemma(name)
        .map(|l| l.plaintext.clone())
        .unwrap_or_else(|| "Enter your new Lemma".to_string());
    let rows = 2 + plaintext.matches('\n').count();
    let esc_name = html_escape(name);
    format!(
        "<form method=\"post\" action=\"../../edit/edit/{action}\">\
<div contenteditable=\"true\">\
<label for=\"lemmaTextArea\"> Edit Lemma {name}</label>\n\
<textarea name=\"lemma-text\" id=\"lemmaTextArea\" rows=\"{rows}\">{plaintext}</textarea>\n\
</div>\n\
<button type=\"submit\">Submit</button>\n\
<p></p>\n\
<h3> Introduction to Lemma Edit:</h3>\n\
{noscript}\n\
<p><ul class=\"wrap-text\">\
<li>Modifying the lemma in the box above and clicking the submit button will attempt to modify the lemma in the current theory.\n<br>&zwnj;</br>\n</li>\n\
<li>Failures in parsing the lemma or verifying its well-formedness will result in an error, and the lemma will NOT be modified.\nHowever, your changes will be kept on this page until you leave this right panel.\n<br>&zwnj;</br>\n</li>\n\
<li>Editing a lemma will NOT modify the file it was loaded from, but clicking on \"Append modified lemmas to file\" in the Actions menu adds all modified lemmas as a comment at the end of the file on disk they were loaded from.\n<br>&zwnj;</br>\n</li>\n\
<li>Clicking on \"Download source\" in the Actions menu will download the modified version of the theory (including the modified lemmas), but not modify the file on disk.\n<br>&zwnj;</br>\n</li>\n\
<li>Modifying a reuse lemma will invalidate all subsequent proofs.\n<br>&zwnj;</br>\n</li>\n\
<li>Modifying a sources lemma is not supported and will result in an error.</li>\n\
</ul>\n{wrap_style}\n</p>\n</form>\n",
        action = esc_name,
        name = esc_name,
        rows = rows,
        plaintext = html_escape(&plaintext),
        noscript = NOSCRIPT_WARNING,
        wrap_style = WRAP_TEXT_STYLE,
    )
}

/// HS `htmlThyPath (TheoryAdd name)` (`src/Web/Theory.hs:1103-1133`).  The
/// textarea is always the literal "Enter your new Lemma" (HS passes
/// `lname = Nothing` for Add, so `getLemmaPlaintext` returns the default).
fn add_lemma_html(name: &str) -> String {
    let esc_name = html_escape(name);
    format!(
        "<form method=\"post\" action=\"../../edit/add/{action}\">\
<div contenteditable=\"true\">\
<label for=\"lemmaTextArea\">LemmaText</label>\n\
<textarea name=\"lemma-text\" id=\"lemmaTextArea\">Enter your new Lemma</textarea>\n\
</div>\n\
<button type=\"submit\">Submit</button>\n\
<p></p>\n\
<h3> Introduction to Adding Lemmas:</h3>\n\
{noscript}\n\
<p><ul class=\"wrap-text\">\
<li>Adds the lemma in the current position in the theory, but will throw an error if a lemma with the same name exists, the parsing fails, or the lemma isn't well-formed.\n<br>&zwnj;</br>\n</li>\n\
<li>Adding a lemma will NOT modify the loaded source file, but clicking on \"Append modified lemmas to file\" in the Actions menu appends all added lemmas as a comment at the end of the current theory file.\n<br>&zwnj;</br>\n</li>\n\
<li>Clicking on \"Download source\" in the Actions menu will download the modified version of the theory (including the added lemmas).</li>\n\
</ul>\n{wrap_style}\n</p>\n</form>\n",
        action = esc_name,
        noscript = NOSCRIPT_WARNING,
        wrap_style = WRAP_TEXT_STYLE,
    )
}

/// HS `htmlThyPath (TheoryDelete name)` (`src/Web/Theory.hs:1070-1101`).
fn delete_lemma_html(name: &str) -> String {
    let esc_name = html_escape(name);
    format!(
        "<p> Do you want to delete lemma {name}?</p>\n\
<form method=\"post\" action=\"../../edit/delete/{action}\">\
<button type=\"submit\">Yes</button>\n\
<p></p>\n\
<h3> Introduction to Lemma Delete:</h3>\n\
{noscript}\n\
<p><ul class=\"wrap-text\">\
<li>Clicking on the button above will delete the lemma from the loaded theory.\n<br>&zwnj;</br>\n</li>\n\
<li>Deleting a lemma will NOT modify the file it was loaded from, but clicking on \"Download source\" in the Actions menu will download the modified version of the theory (so without the deleted lemmas).\n<br>&zwnj;</br>\n</li>\n\
<li>Deleting a reuse lemma will invalidate all subsequent proofs.\n<br>&zwnj;</br>\n</li>\n\
<li>Deleting a source lemma is not supported and will result in an error.</li>\n\
{wrap_style}\n</ul>\n</p>\n</form>\n",
        name = esc_name,
        action = esc_name,
        noscript = NOSCRIPT_WARNING,
        wrap_style = WRAP_TEXT_STYLE,
    )
}

/// HS's shared `<noscript>` JavaScript-required warning (the `<span
/// class="tamarin">Tamarin</span>` Hamlet-emits a stray extra `</span>` the
/// parity normalizer drops; we emit a single well-formed span).
const NOSCRIPT_WARNING: &str =
    "<noscript><div class=\"warning\">Warning: JavaScript must be enabled for the\n\
<span class=\"tamarin\">Tamarin</span>\nprover GUI to function properly.</div>\n</noscript>";

/// HS's shared `.wrap-text li` inline `<style>` block.
const WRAP_TEXT_STYLE: &str =
    "<style>.wrap-text li {white-space: normal;\nword-wrap: break-word;}</style>";

/// HS `helpHtml` (`src/Web/Theory.hs:1187-1285`): the static Quick-introduction
/// + keyboard-shortcut help page, prefixed by the `Theory: NAME (Loaded at TIME
/// from ORIGIN) ERRORS` env line.  The env line's `(Loaded at ...)` parenthetical
/// is stripped by the parity normalizer (`norm_env`) on both sides, so its
/// timestamp/origin need not be byte-identical to HS.  `errorsHtml` is the
/// wellformedness banner (`<div class="wf-warning">…</div>` when the theory has
/// warnings, empty otherwise), populated from the stored `wf_report` at load.
fn help_html(entry: &TheoryEntry) -> String {
    // HS `show info.origin` — e.g. `Local "/path/Foo.spthy"`.
    let origin = match &entry.origin {
        crate::state::TheoryOrigin::Local(p) => format!("Local \"{}\"", p.display()),
        crate::state::TheoryOrigin::Upload(n) => format!("Upload \"{}\"", n),
        crate::state::TheoryOrigin::Interactive => "Interactive".to_string(),
    };
    let time = entry.loaded_at.format("%H:%M:%S").to_string();
    let env_line = format!(
        "<p>Theory: {name} (Loaded at {time} from {origin}) {errors}</p>",
        name = html_escape(&entry.name),
        time = html_escape(&time),
        origin = html_escape(&origin),
        errors = entry.errors_html,
    );
    format!(
        "{env_line}\n\
<div id=\"help\"><h3>Quick introduction</h3>\n{noscript}\n\
<p><em>Left pane: Proof scripts display.</em><ul>\
<li>When a theory is initially loaded, there will be a line at the end of each theorem stating <tt>\"by sorry // not yet proven\"</tt>.  Click on <tt>sorry</tt> to inspect the proof state.</li>\
<li>Right-click to show further options, such as autoprove.</li></ul></p>\n\
<p><em>Right pane: Visualization.</em><ul>\
<li>Visualization and information display relating to the currently selected item.</li></ul></p></div>\n\
<h3>Keyboard shortcuts</h3>\n\
<p><div id=\"shortcuts\"><table>\
<tr><td><span class=\"keys\">j/k</span></td><td>Jump to the next/previous proof path within the currently focused lemma.</td></tr>\
<tr><td><span class=\"keys\">J/K</span></td><td>Jump to the next/previous open constraint within the currently focused lemma, or to the next/previous lemma if there are no more <tt>sorry</tt> steps in the proof of the current lemma.</td></tr>\
<tr><td><span class=\"keys\">1-9</span></td><td>Apply the proof method with the given number as shown in the applicable proof method section in the main view.</td></tr>\
<tr><td><span class=\"keys\">a/A</span></td><td>Apply the autoprove method to the focused proof step. <span class=\"keys\">a</span> stops after finding a solution, and <span class=\"keys\">A</span> searches for all solutions. Needs to have a <tt>sorry</tt> selected to work.</td></tr>\
<tr><td><span class=\"keys\">b/B</span></td><td>Apply a bounded-depth version of the autoprove method to the focused proof step. <span class=\"keys\">b</span> stops after finding a solution, and <span class=\"keys\">B</span> searches for all solutions. Needs to have a <tt>sorry</tt> selected to work.</td></tr>\
<tr><td><span class=\"keys\">s/S</span></td><td>Apply the autoprove method to all lemmas. <span class=\"keys\">s</span> stops after finding a solution, and <span class=\"keys\">S</span> searches for all solutions.</td></tr>\
<tr><td><span class=\"keys\">?</span></td><td>Display this help message.</td></tr>\
</table></div></p>\n",
        env_line = env_line,
        noscript = NOSCRIPT_WARNING,
    )
}

/// Render the proof tree pane for a lemma at a given sub-path.
/// If a live [`ProofState`] is already built, use the actual tree;
/// otherwise fall back to the lemma's static info plus a build hint.
pub fn proof_html(entry: &TheoryEntry, lemma: &str, sub: &[String]) -> String {
    // HS `htmlThyPath` for `TheoryProof l p` (Web/Theory.hs:1019-1023):
    //   pp $ fromMaybe (text "No such lemma or proof path.") $ do
    //     lemma <- lookupLemma l thy
    //     subProofSnippet ... l p (getProofContext lemma thy)
    //       <$> resolveProofPath thy l p
    // → renders ONLY the sub-proof snippet at the resolved path; a missing
    //   lemma or unresolvable proof path yields the single fallback string.
    //   No lemma header, no formula echo, no whole-tree dump.
    if entry.typed_theory.lookup_lemma(lemma).is_none() {
        return "No such lemma or proof path.".into();
    }
    if let Some(ps) = &entry.proof_state {
        if let Some(root) = ps.get_root(lemma) {
            if let Some(n) = crate::handlers::proof_tree::navigate_at(&root, sub) {
                // Install this lemma's per-lemma `use_induction`/`heuristic`
                // into the shared ctx before ranking (HS `getProofContext`);
                // otherwise the Applicable Proof Methods order + ranking name
                // default to `AvoidInduction`/`Smart` and diverge from HS.
                let mut ctx_guard = ps.ctx.lock();
                ps.install_lemma_settings(&mut ctx_guard, lemma);
                return crate::handlers::proof_tree::render_sub_proof_snippet(
                    entry.idx, lemma, sub, n, &ctx_guard);
            }
        }
    }
    "No such lemma or proof path.".into()
}

// ---------------------------------------------------------------------
// Main-pane content: message / rules / source-case snippets.
//
// These mirror HS `Web.Theory` `messageSnippet` (920-931), `rulesSnippet`
// (887-917) and `htmlSource`/`reqCasesSnippet` (820-879).  All TEXT content is
// produced by the byte-faithful `--prove` printers (`pretty_theory`,
// `pretty_formula`, `pretty_system`) so it stays consistent with the CLI; this
// module only adds the surrounding HTML tags HS's `withTag`/`ppSection` emit.
// ---------------------------------------------------------------------

use tamarin_theory::rule::{IntrRuleAC, IntrRuleACInfo};

/// HS `isConstrRule` for the message-page classification (Model/Rule.hs:684-691):
/// `_crConstruct` = ConstrRule | FreshConstr | PubConstr | NatConstr | Coerce.
fn is_constr_intr(info: &IntrRuleACInfo) -> bool {
    matches!(info,
        IntrRuleACInfo::ConstrRule(_)
        | IntrRuleACInfo::FreshConstr
        | IntrRuleACInfo::PubConstr
        | IntrRuleACInfo::NatConstr
        | IntrRuleACInfo::Coerce)
}

/// HS `isDestrRule` (Model/Rule.hs:671-675): `_crDestruct` = DestrRule | IEquality.
fn is_destr_intr(info: &IntrRuleACInfo) -> bool {
    matches!(info, IntrRuleACInfo::DestrRule(..) | IntrRuleACInfo::IEquality)
}

/// HS `ppSection header s = <h2>header</h2> $$ <p class="monospace rules"> body`
/// (Web/Theory.hs:928-931).  Always emitted (used by `messageSnippet`).
fn pp_section(out: &mut String, header: &str, body: &str) {
    out.push_str("<h2>");
    out.push_str(header);
    out.push_str("</h2>\n<p class=\"monospace rules\"><pre>");
    out.push_str(&html_escape(body));
    out.push_str("</pre></p>\n");
}

/// HS `ppWithHeader` (Web/Theory.hs:912-917): like [`pp_section`] but the whole
/// section is OMITTED when `body` is empty (`caseEmptyDoc emptyDoc … body`).
fn pp_with_header(out: &mut String, header: &str, body: &str) {
    if body.is_empty() { return; }
    pp_section(out, header, body);
}

/// HS `messageSnippet` (Web/Theory.hs:920-931): Signature +
/// Construction/Deconstruction rule sections.
fn message_html(entry: &TheoryEntry) -> String {
    // `prettySignatureWithMaude thy._thySignature` — the same signature block
    // the theory body prints.
    let sig_block = tamarin_theory::pretty_theory::web_signature_block(
        &entry.typed_theory.signature.maude_sig);
    // `getClassifiedRules thy`'s `_crConstruct` / `_crDestruct`.  RS stores
    // proto rules separately, so `ctx.intruder_rules` is exactly HS's
    // `intrRulesAC`; an order-preserving filter reproduces the classification.
    let mut construct: Vec<IntrRuleAC> = Vec::new();
    let mut destruct: Vec<IntrRuleAC> = Vec::new();
    if let Some(ps) = &entry.proof_state {
        let ctx = ps.ctx.lock();
        for ir in &ctx.intruder_rules {
            if is_constr_intr(&ir.info) { construct.push(ir.clone()); }
            else if is_destr_intr(&ir.info) { destruct.push(ir.clone()); }
        }
    }
    // `map prettyRuleAC` joined by one blank line == `pretty_intruder_variants`.
    let construct_block = tamarin_theory::pretty_formula::pretty_intruder_variants(&construct);
    let destruct_block = tamarin_theory::pretty_formula::pretty_intruder_variants(&destruct);
    let mut out = String::new();
    pp_section(&mut out, "Signature", &sig_block);
    pp_section(&mut out, "Construction Rules", &construct_block);
    pp_section(&mut out, "Deconstruction Rules", &destruct_block);
    out
}

/// HS `showInjFact` (Web/Theory.hs:906-910): `showFactTag tag ++ "(" ++
/// intercalate "," ("id":positions) ++ ")"`.
fn show_inj_fact(
    tag: &tamarin_theory::fact::FactTag,
    behaviours: &[Vec<tamarin_theory::tools::injective_fact_instances::MonotonicBehaviour>],
) -> String {
    use tamarin_theory::fact::{FactTag, Multiplicity};
    let name = tamarin_theory::fact::fact_tag_name(tag);
    let head = match tag {
        FactTag::Proto(Multiplicity::Persistent, _, _) => format!("!{}", name),
        _ => name.to_string(),
    };
    let mut parts: Vec<String> = vec!["id".to_string()];
    for bb in behaviours {
        if bb.len() == 1 {
            parts.push(bb[0].to_string());
        } else {
            let inner: Vec<String> = bb.iter().map(|b| b.to_string()).collect();
            parts.push(format!("({})", inner.join(",")));
        }
    }
    format!("{}({})", head, parts.join(","))
}

/// HS `rulesSnippet` (Web/Theory.hs:887-917).
fn rules_html(entry: &TheoryEntry) -> String {
    let mut out = String::new();
    // HS `rulesSnippet`'s FIRST `ppWithHeader "Macros" (prettyMacros ...)` —
    // emitted only when the theory declares macros (`theoryMacros thy`
    // non-empty); the same `macros: name( args ) = body, ...` block the
    // `--prove` theory body renders.
    let macros_block = tamarin_theory::pretty_theory::web_macros(&entry.parser_theory);
    let proto_rules = tamarin_theory::pretty_theory::web_proto_rules(
        &entry.parser_theory, &entry.typed_theory);
    let mut inj_body = String::from("None");
    let mut extra_ac: Vec<String> = Vec::new();
    if let Some(ps) = &entry.proof_state {
        let ctx = ps.ctx.lock();
        // `getInjectiveFactInsts thy` — already computed on the context.
        if !ctx.injective_fact_insts.is_empty() {
            let items: Vec<String> = ctx.injective_fact_insts.iter()
                .map(|(tag, behaviours)| show_inj_fact(tag, behaviours))
                .collect();
            inj_body = items.join(", ");
        }
        // `extraACRules` = `_crProtocol` not already in `theoryRules`.  The
        // intruder members of `_crProtocol` are exactly the non-constr/
        // non-destr intruder rules (ISend, IRecv); RS keeps proto rules out of
        // `ctx.intruder_rules`, so the name-collision filter HS needs is a
        // no-op here.
        for ir in &ctx.intruder_rules {
            if is_constr_intr(&ir.info) || is_destr_intr(&ir.info) { continue; }
            // `prettyIntruderRuleAC r = prettyRuleAC r $--$ nest 2
            //    (multiComment_ ["has exactly the trivial AC variant"])`.
            let body = tamarin_theory::pretty_formula::pretty_intruder_variants(
                std::slice::from_ref(ir));
            extra_ac.push(format!(
                "{}\n  /* has exactly the trivial AC variant */", body));
        }
    }
    // `vcat (map prettyIntruderRuleAC extraACRules ++ map prettyClosedProtoRule protoRules)`.
    let mut msr_parts = extra_ac;
    msr_parts.extend(proto_rules);
    let msr_body = msr_parts.join("\n\n");
    let restr_body = tamarin_theory::pretty_theory::web_restrictions(
        &entry.parser_theory, &entry.typed_theory).join("\n\n");

    // HS `rulesSnippet` order: Macros (if any) → Fact Symbols → MSR → Restrictions.
    if let Some(m) = &macros_block {
        pp_with_header(&mut out, "Macros", m);
    }
    pp_with_header(&mut out, "Fact Symbols with Injective Instances", &inj_body);
    pp_with_header(&mut out, "Multiset Rewriting Rules", &msr_body);
    pp_with_header(&mut out, "Restrictions of the Set of Traces", &restr_body);
    out
}

/// HS `reqCasesSnippet` + `htmlSource` (Web/Theory.hs:820-879): the raw/refined
/// source-case listing.  The `src_idx`/`case_idx` URL fields are ignored (HS
/// `TheorySource kind _ _` renders the whole `getSource kind thy` list); they
/// only address the per-case interactive graph.
fn sources_html(entry: &TheoryEntry, kind: &SourceKind) -> String {
    let mut out = String::new();
    let (kind_str, want_refined) = match kind {
        SourceKind::Raw => ("raw", false),
        SourceKind::Refined => ("refined", true),
    };
    let source_lists = compute_source_lists(entry, want_refined);
    for (j, (goal, cases)) in source_lists.iter().enumerate() {
        render_html_source(&mut out, entry.idx, kind_str, j + 1, goal, cases);
    }
    out
}

/// Compute `getSource kind thy` — the raw or refined source list, as
/// `(goal, cases)` pairs.  Shared by `sources_html` (the page) and
/// `source_case_counts` (the theory-index `(N cases, …)` annotation) so both
/// stay consistent.  Returns empty when the proof state is not yet built.
fn compute_source_lists(
    entry: &TheoryEntry,
    want_refined: bool,
) -> Vec<(tamarin_theory::constraint::constraints::Goal,
         Vec<(String, tamarin_theory::constraint::system::System)>)> {
    use tamarin_theory::constraint::system::SourceKind as SysSourceKind;
    let Some(ps) = &entry.proof_state else { return Vec::new(); };
    let ctx = ps.ctx.lock();
    // Refined sources fold in the `[sources]`-lemma typing assumptions
    // (HS `refineWithSourceAsms`, Rule.hs:157).  With no such lemma the refine
    // is a plain relabel to `RefinedSource` (Sources.hs:617-618).
    let typ_asms: Vec<tamarin_theory::guarded::Guarded> = if want_refined {
        entry.typed_theory.lemmas()
            .filter(|l| matches!(l.trace_quantifier, TraceQuantifier::AllTraces)
                && l.attributes.iter().any(|a| matches!(a, LemmaAttr::Sources)))
            .filter_map(|l| tamarin_theory::guarded::formula_to_guarded(&l.formula).ok())
            .collect()
    } else { Vec::new() };

    // `getSource kind thy`: raw = `ctx.full_sources` (precomputed + saturated);
    // refined = raw with `refineWithSourceAsms` applied (or relabeled).
    if want_refined && !typ_asms.is_empty() {
        let cloned: Vec<_> = ctx.full_sources.iter()
            .map(|s| { let _ = s.cases(&ctx); s.clone() }).collect();
        let refined = tamarin_theory::constraint::solver::sources::refine_with_source_asms(
            cloned, &typ_asms, &ctx);
        refined.iter().map(|s| (s.goal.clone(), s.cases_or_empty())).collect()
    } else {
        ctx.full_sources.iter().map(|s| {
            let mut cases = s.cases(&ctx);
            if want_refined {
                for (_, sys) in cases.iter_mut() {
                    sys.source_kind = Some(SysSourceKind::RefinedSources);
                }
            }
            (s.goal.clone(), cases)
        }).collect()
    }
}

/// HS `casesInfo kind` (Web/Theory.hs:399-406): `(nCases, chainInfo)` where
/// `nCases = length (getSource kind thy)` and `nChains = sum $ map (sum .
/// unsolvedChainConstraints)`.  Rendered as `(N cases, deconstructions
/// complete)` or `(N cases, K partial deconstructions left)`.
fn source_case_counts(entry: &TheoryEntry, want_refined: bool) -> (usize, usize) {
    let source_lists = compute_source_lists(entry, want_refined);
    let n_cases = source_lists.len();
    let n_chains: usize = source_lists.iter()
        .flat_map(|(_, cases)| cases.iter())
        .map(|(_, sys)|
            tamarin_theory::constraint::solver::sources::unsolved_chain_constraints(sys))
        .sum();
    (n_cases, n_chains)
}

/// HS `htmlSource` (Web/Theory.hs:820-845) for a single [`Source`].
fn render_html_source(
    out: &mut String,
    idx: usize,
    kind: &str,
    j: usize,
    goal: &tamarin_theory::constraint::constraints::Goal,
    cases: &[(String, tamarin_theory::constraint::system::System)],
) {
    // `ppPrem = doubleQuotes (prettyGoal th._cdGoal)`.
    let goal_str = tamarin_theory::pretty_theory::web_pretty_goal(goal);
    let n_cases = cases.len();
    // `ppHeader = "Sources of" <-> ppPrem <-> parens (nCases <-> "cases")`.
    let header = format!("Sources of \"{}\" ({} cases)", goal_str, n_cases);
    out.push_str("<h2>");
    out.push_str(&html_escape(&header));
    out.push_str("</h2>\n");
    if cases.is_empty() {
        out.push_str("<h3>No cases.</h3>\n");
        return;
    }
    for (i, (name, sys)) in cases.iter().enumerate() {
        let ii = i + 1;
        // `isPartial = not (null (unsolvedChains se))`.
        let is_partial =
            tamarin_theory::constraint::solver::sources::unsolved_chain_constraints(sys) != 0;
        let partial = if is_partial { " (partial deconstructions)" } else { "" };
        // `<h3> Source i of nCases / named "name" [(partial deconstructions)] </h3>`.
        out.push_str(&format!(
            "<h3>Source {i} of {n} / named \"{name}\"{partial}</h3>\n",
            i = ii, n = n_cases, name = html_escape(name), partial = partial,
        ));
        // `refDotInteractiveStaticPath renderUrl tidx (TheorySource kind j i)`.
        out.push_str(&format!(
            "<static-graph graphsrc=\"/thy/trace/{idx}/intdot/cases/{kind}/{j}/{i}\"></static-graph>\n",
            idx = idx, kind = kind, j = j, i = ii,
        ));
        // `withTag "p" [] ppPrem`.
        out.push_str("<p>\"");
        out.push_str(&html_escape(&goal_str));
        out.push_str("\"</p>\n");
        // `wrapP (prettyNonGraphSystem se)`, `wrapP = <p class="monospace cases">`.
        out.push_str("<p class=\"monospace cases\"><pre>");
        out.push_str(&html_escape(
            &tamarin_theory::pretty_system::pretty_non_graph_system(sys)));
        out.push_str("</pre></p>\n");
    }
}
