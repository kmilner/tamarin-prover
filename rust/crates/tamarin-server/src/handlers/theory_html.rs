//! HTML rendering for theory pages.
//!
//! This mirrors a *minimal* slice of Haskell's `Web.Theory` + `Web.Hamlet`
//! pretty printing — enough to surface the lemmas, restrictions and
//! rules in the UI, and to wire `Autoprove` links the frontend
//! recognises.

use crate::handlers::path_parse::TheoryPath;
use crate::handlers::root::html_escape;
use crate::state::TheoryEntry;

use tamarin_theory::pretty_formula::pretty_formula;
use tamarin_theory::theory::{LemmaAttr, TraceQuantifier};

/// Full overview/framing page (the one served at `/thy/trace/<idx>/overview/...`).
pub fn overview_page(entry: &TheoryEntry, path: &TheoryPath) -> String {
    let header_html = header(entry);
    let proof_state = proof_state(entry);
    let main_view = path_html(entry, path);
    format!(
        r##"<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Theory: {name}</title>
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
    format!(r##"
<div class="layout-pane-north">
  <div id="header-info">Running <a href="/"><span class="tamarin">Tamarin</span></a> {version} (Rust port)</div>
</div>
<div id="header-links">
<ul id="navigation">
  <li><a href="/">Index</a></li>
  <li><a href="#">Actions</a><ul>
    <li><a target="_blank" href="/thy/trace/{idx}/source">Show source</a></li>
    <li><a href="/thy/trace/{idx}/download/{filename}">Download source</a></li>
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
        filename = html_escape(&format!("{}.spthy", entry.name)),
    )
}

/// Left-pane proof-state tree.  Mirrors Haskell's `theoryIndex` +
/// `lemmaIndex` + `proofIndex` (`src/Web/Theory.hs:296-417`).
fn proof_state(entry: &TheoryEntry) -> String {
    let typed = &entry.typed_theory;
    let idx = entry.idx;
    let mut out = String::new();
    // Header — clickable "help".
    out.push_str(&format!(
        "<a class=\"internal-link help\" href=\"/thy/trace/{idx}/main/help\">theory {}</a>\n<br><br>\n",
        html_escape(&entry.name),
        idx = idx));
    // Top-level overview links.
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/message\"><strong>Message theory</strong></a><br>\n",
        idx = idx));
    let rules: Vec<_> = typed.rules().collect();
    let restrs: Vec<_> = typed.restrictions().collect();
    let rules_info = if restrs.is_empty() {
        format!("Multiset rewriting rules ({})", rules.len())
    } else {
        format!("Multiset rewriting rules and restrictions ({})", rules.len())
    };
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/rules\"><strong>{}</strong></a><br>\n",
        html_escape(&rules_info),
        idx = idx));
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/tactic\"><strong>Tactic(s)</strong></a><br>\n",
        idx = idx));
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/cases/raw/0/0\"><strong>Raw sources</strong></a><br>\n",
        idx = idx));
    out.push_str(&format!(
        "<a class=\"internal-link\" href=\"/thy/trace/{idx}/main/cases/refined/0/0\"><strong>Refined sources</strong></a><br>\n",
        idx = idx));
    out.push_str("<br>\n");

    // Lemmas — each with the nested proof tree below.  Mirrors
    // Haskell's `lemmaIndex` (`src/Web/Theory.hs:296-318`): the lemma
    // NAME is plain text (no link); the clickable step is `by sorry`
    // pointing at `/main/proof/<lemma>/_`.  Haskell's `TheoryLemma`
    // path renders the literal "this is a mistake" — so we must not
    // link there.
    let lemmas: Vec<_> = typed.lemmas().collect();
    for l in lemmas {
        let tq = match l.trace_quantifier {
            TraceQuantifier::AllTraces => "all-traces",
            TraceQuantifier::ExistsTrace => "exists-trace",
        };
        let attrs = render_attrs(&l.attributes);
        let formula = pretty_formula(&l.formula);
        out.push_str(&format!(
            "<div class=\"lemma-row\">\n\
             <span class=\"hl_keyword\">lemma</span> {n}:{attrs}<br>\n\
             &nbsp;&nbsp;{tq} \"{f}\"<br>\n\
             &nbsp; <a class=\"ajax-action proof-step autoprove\" href=\"/thy/trace/{idx}/autoprove/idfs/0/false/proof/{n_url}\">[autoprove]</a>\n",
            idx = idx,
            n = html_escape(&l.name),
            n_url = url_path_escape_local(&l.name),
            tq = tq,
            attrs = html_escape(&attrs),
            f = html_escape(&formula),
        ));
        // Nested proof tree (if a live proof state exists).  If there's
        // no live tree yet, fall back to the Haskell-style
        // `by <sorry-step>` line so the user can click into the lemma's
        // initial proof view.  This matches Haskell's
        // `proofIndex` output for a freshly loaded lemma whose root is
        // `Sorry "not yet proven"`.
        let mut rendered_tree = false;
        if let Some(ps) = &entry.proof_state {
            if let Some(root) = ps.get_root(&l.name) {
                out.push_str("<div class=\"proof-index\" style=\"margin-left:1em;font-family:monospace\">\n");
                let path: Vec<String> = Vec::new();
                render_index_node(&mut out, idx, &l.name, &path, &root);
                out.push_str("</div>\n");
                rendered_tree = true;
            }
        }
        if !rendered_tree {
            // Static fallback "by sorry" link — points at the LEMMA
            // ROOT proof path (sub = []), matching Haskell's URL
            // emission `proof/<lemma>` (no trailing `_`).  See
            // `path_parse.rs` for the parser's `proof/<lemma>` →
            // `sub = []` semantics.
            out.push_str(&format!(
                "&nbsp;<span class=\"hl_keyword\">by</span> \
                 <a class=\"internal-link proof-step sorry-step\" \
                 href=\"/thy/trace/{idx}/main/proof/{n_url}\">\
                 <span class=\"hl_keyword\">sorry</span></a><br>\n",
                idx = idx,
                n_url = url_path_escape_local(&l.name),
            ));
        }
        out.push_str("</div>\n");
    }
    out
}

/// Render a single proof-tree node in the left-pane "proof index"
/// style — clickable step links + nested children.  Mirrors Haskell's
/// `proofIndex.ppStep` (`Web/Theory.hs:235`).
fn render_index_node(
    out: &mut String,
    idx: usize,
    lemma: &str,
    path: &[String],
    node: &tamarin_theory::constraint::solver::search::ProofNode,
) {
    let url_path = encode_index_path(path);
    // Status-coloured class.
    let cls = match node.status {
        tamarin_theory::constraint::solver::search::NodeStatus::Solved => "hl_good",
        tamarin_theory::constraint::solver::search::NodeStatus::Contradictory => "hl_good",
        tamarin_theory::constraint::solver::search::NodeStatus::Open => "sorry-step",
        tamarin_theory::constraint::solver::search::NodeStatus::Sorry => "sorry-step",
        tamarin_theory::constraint::solver::search::NodeStatus::Unfinishable => "hl_medium",
    };
    let label = crate::handlers::proof_tree::method_label(&node.method);
    // Class includes `internal-link` so the frontend JS picks it up
    // (events.installRelativeClickHandler targets
    // `div#proof a.internal-link.proof-step`); see
    // `data/js/tamarin-prover-ui.js:428-433`.  Without that class, the
    // sorry-step link is a plain anchor — clicking does nothing
    // because the AJAX handler isn't installed on it.
    out.push_str(&format!(
        "<a class=\"internal-link proof-step {cls}\" href=\"/thy/trace/{idx}/main/proof/{lemma}{path}\">{label}</a><br>\n",
        cls = cls,
        idx = idx,
        lemma = url_path_escape_local(lemma),
        path = url_path,
        label = html_escape(&label),
    ));
    for (case_name, child) in &node.children {
        let mut child_path = path.to_vec();
        child_path.push(case_name.clone());
        out.push_str(&format!(
            "<div style=\"margin-left:1em\">case {}<br>",
            html_escape(case_name)));
        render_index_node(out, idx, lemma, &child_path, child);
        out.push_str("</div>");
    }
}

fn url_path_escape_local(s: &str) -> String {
    s.chars().map(|c| match c {
        c if c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '.' => c.to_string(),
        c => format!("%{:02X}", c as u32),
    }).collect()
}

fn encode_index_path(path: &[String]) -> String {
    if path.is_empty() { return String::new(); }
    let mut s = String::new();
    for seg in path {
        s.push('/');
        let escaped = if seg.is_empty() { "_".to_string() }
            else if seg.starts_with('_') { format!("_{}", seg) }
            else { seg.to_string() };
        s.push_str(&url_path_escape_local(&escaped));
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
        TheoryPath::Rules => {
            let mut s = String::from("<h2>Rules</h2><pre>");
            for r in typed.rules() {
                s.push_str(&html_escape(r.name()));
                s.push('\n');
            }
            s.push_str("</pre>");
            s
        }
        TheoryPath::Message => {
            let mut s = String::from("<h2>Restrictions</h2><ul>");
            for r in typed.restrictions() {
                s.push_str("<li>");
                s.push_str(&html_escape(&r.name));
                s.push_str("</li>");
            }
            s.push_str("</ul>");
            s
        }
        TheoryPath::Tactic => "<h2>Tactic</h2><p>(stub: tactic view not yet implemented)</p>".into(),
        TheoryPath::Lemma(name) => lemma_html(entry, name),
        TheoryPath::Proof { lemma, sub } => proof_html(entry, lemma, sub),
        TheoryPath::Method { lemma, sub, .. } => proof_html(entry, lemma, sub),
        TheoryPath::Source { .. } => "<h2>Source case</h2><p>(stub: source-case view not yet implemented in the Rust port)</p>".into(),
        TheoryPath::Edit(_) | TheoryPath::Add(_) | TheoryPath::Delete(_) =>
            "<p>(stub: editing not yet implemented in the Rust port)</p>".into(),
    }
}

fn help_html(entry: &TheoryEntry) -> String {
    let counts = format!(
        "{} rules, {} restrictions, {} lemmas",
        entry.typed_theory.rules().count(),
        entry.typed_theory.restrictions().count(),
        entry.typed_theory.lemmas().count(),
    );
    format!(
        "<h2>Theory <code>{name}</code></h2>\n\
         <p>{counts}</p>\n\
         <p>Use the <strong>Proof scripts</strong> panel on the left to navigate to a lemma. \
         Click <em>[autoprove]</em> next to a lemma to run the Rust autoprover.</p>\n\
         <p><em>Note:</em> this is the Rust port of Tamarin's interactive server. \
         Graph rendering and several edit operations are not yet wired up; \
         proof construction itself runs the same solver that backs \
         <code>tamarin-prover --prove</code> in the Rust port.</p>\n",
        name = html_escape(&entry.name),
        counts = counts,
    )
}

fn lemma_html(entry: &TheoryEntry, name: &str) -> String {
    let typed = &entry.typed_theory;
    match typed.lookup_lemma(name) {
        None => format!("<p>Lemma <code>{}</code> not found.</p>", html_escape(name)),
        Some(l) => {
            let tq = match l.trace_quantifier {
                TraceQuantifier::AllTraces => "all-traces",
                TraceQuantifier::ExistsTrace => "exists-trace",
            };
            let formula = pretty_formula(&l.formula);
            format!(
                "<h2>Lemma <code>{n}</code></h2>\n\
                 <p><em>{tq}</em></p>\n\
                 <pre class=\"formula\">\"{f}\"</pre>\n\
                 <p>\n\
                 <a class=\"ajax-action\" href=\"/thy/trace/{idx}/autoprove/idfs/0/false/proof/{n}\">[autoprove (dfs)]</a>\n\
                 &nbsp;\n\
                 <a class=\"ajax-action\" href=\"/thy/trace/{idx}/autoprove/bfs/0/false/proof/{n}\">[autoprove (bfs)]</a>\n\
                 </p>\n",
                n = html_escape(name),
                tq = tq,
                f = html_escape(&formula),
                idx = entry.idx,
            )
        }
    }
}

/// Render the proof tree pane for a lemma at a given sub-path.
/// If a live [`ProofState`] is already built, use the actual tree;
/// otherwise fall back to the lemma's static info plus a build hint.
pub fn proof_html(entry: &TheoryEntry, lemma: &str, sub: &[String]) -> String {
    let typed = &entry.typed_theory;
    let lemma_meta = match typed.lookup_lemma(lemma) {
        Some(l) => l,
        None => return format!("<p>Lemma <code>{}</code> not found.</p>",
            html_escape(lemma)),
    };
    let tq = match lemma_meta.trace_quantifier {
        TraceQuantifier::AllTraces => "all-traces",
        TraceQuantifier::ExistsTrace => "exists-trace",
    };
    let mut out = String::new();
    out.push_str(&format!(
        "<h2>Lemma <code>{}</code></h2>\n<p><em>{}</em></p>\n",
        html_escape(lemma), tq));
    out.push_str(&format!(
        "<pre class=\"formula\">\"{}\"</pre>\n",
        html_escape(&pretty_formula(&lemma_meta.formula))));
    // If a live proof state exists, render the sub-proof snippet
    // at the requested path (Haskell's `subProofSnippet` style).
    if let Some(ps) = &entry.proof_state {
        if let Some(root) = ps.get_root(lemma) {
            // Navigate to the node at `sub` if possible.
            let node = crate::handlers::proof_tree::navigate_at(&root, sub);
            match node {
                Some(n) => {
                    let ctx_guard = ps.ctx.lock();
                    out.push_str(
                        &crate::handlers::proof_tree::render_sub_proof_snippet(
                            entry.idx, lemma, sub, n, &ctx_guard));
                }
                None => {
                    out.push_str(&format!(
                        "<p>(path {:?} not present in proof tree)</p>\n",
                        sub));
                }
            }
            // Also show the full proof tree (compact) at the bottom so
            // the user can click into other branches.
            out.push_str("<hr><h3>Proof tree</h3>\n");
            out.push_str(&crate::handlers::proof_tree::render_proof_tree_html(
                entry.idx, lemma, &root));
            return out;
        }
    }
    // No live tree built yet — render the lemma's "initial" state
    // with action links the user can click to step through.
    out.push_str(&format!(
        "<div class=\"proof-node\">\n\
         <span class=\"proof-method\">sorry /* initial */</span> \
         <span class=\"proof-status\" style=\"color:#136a8a\">open</span>\n\
         <span class=\"proof-actions\">\n\
         <a class=\"ajax-action proof-step\" href=\"/thy/trace/{idx}/proof-step/{lemma}/simplify\">[simplify]</a>\n\
         <a class=\"ajax-action proof-step\" href=\"/thy/trace/{idx}/proof-step/{lemma}/induction\">[induction]</a>\n\
         <a class=\"ajax-action\" href=\"/thy/trace/{idx}/autoprove/idfs/0/false/proof/{lemma}\">[autoprove (dfs)]</a>\n\
         </span>\n\
         </div>\n",
        idx = entry.idx,
        lemma = html_escape(lemma)));
    out
}
