//! Live proof-tree state — mirror of Haskell's `IncrementalProof` +
//! `applyProverAtPath`.
//!
//! Haskell's interactive UI keeps a mutable proof tree per lemma; user
//! clicks dispatch a `ProofMethod` at a path in that tree and the
//! result is spliced back in.
//!
//! In the Rust port we model this with:
//!
//! - [`LemmaProofState`]: per-lemma `ProofNode` root + the system at
//!   the root (the lemma's initial negated formula).
//! - [`apply_at_path`]: navigate by case-name path, run the requested
//!   `ProofMethod` via `exec_proof_method`, replace that subtree's
//!   children, return the new root.
//! - [`render_proof_tree_html`]: render the tree as nested HTML
//!   matching Haskell's `prettyProof` indentation.
//!
//! The implementation is intentionally minimal: it doesn't yet drive
//! the full `run_proof_search` loop on click — that's the autoprove
//! button.  Each user-driven step applies exactly one method and
//! returns the resulting cases.  The proof can therefore stay "open"
//! until the user navigates / clicks again.

use std::collections::BTreeMap;
use std::sync::Arc;

use parking_lot::Mutex;

use tamarin_term::maude_proc::MaudeHandle;
use tamarin_theory::constraint::constraints::Goal;
use tamarin_theory::constraint::solver::context::ProofContext;
use tamarin_theory::constraint::solver::proof_method::{
    exec_proof_method, is_finished, ProofMethod,
};
use tamarin_theory::constraint::solver::search::{
    candidate_methods, NodeStatus, ProofNode,
};
use tamarin_theory::constraint::system::{formula_to_system, SourceKind, System};
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::guarded::{formula_to_guarded, Guarded};
use tamarin_theory::pretty_system::pretty_non_graph_system;
use tamarin_theory::theory::{LemmaAttr, OpenProtoRule, TraceQuantifier};

use crate::handlers::root::html_escape;

/// Per-lemma live proof state, held inside [`TheoryEntry`].
pub struct LemmaProofState {
    pub root: ProofNode,
}

/// Each [`TheoryEntry`] carries one of these. `ctx` is shared (Arc'd)
/// so we don't rebuild the full source-case precomputation on every
/// click; per-lemma roots are cloned cheaply.
///
/// Maude handles are NOT cloneable across threads safely (the
/// underlying child process has a single stdin/stdout); each
/// `ProofContext` carries its own handle. We hold the context behind a
/// `Mutex` so step application is serialised against autoprove runs.
pub struct ProofState {
    pub ctx: Arc<Mutex<ProofContext>>,
    pub by_lemma: Arc<Mutex<BTreeMap<String, LemmaProofState>>>,
}

impl ProofState {
    /// Build the [`ProofContext`] + initial per-lemma roots for a
    /// freshly loaded theory.  Mirrors the construction in
    /// `tamarin_theory::prove::prove_lemma` minus the search loop.
    pub fn new(
        parser_theory: &tamarin_parser::ast::Theory,
        maude_path: &str,
    ) -> Result<Self, String> {
        let typed = elaborate(parser_theory)
            .map_err(|e| format!("elaborate: {}", e.message))?;
        let sig = typed.signature.maude_sig.clone();
        let maude = MaudeHandle::start(maude_path, sig)
            .map_err(|e| format!("maude start: {:?}", e))?;
        let rules: Vec<OpenProtoRule> = typed.rules().cloned().collect();
        let ctx = ProofContext::new(maude, rules);
        // Build the initial system for every lemma.
        let mut by_lemma: BTreeMap<String, LemmaProofState> = BTreeMap::new();
        for lemma in typed.lemmas() {
            let lname = lemma.name.clone();
            let g = match formula_to_guarded(&lemma.formula) {
                Ok(g) => g,
                Err(_) => continue,
            };
            // Convert restrictions.
            let mut restrictions: Vec<Guarded> = Vec::new();
            for r in typed.restrictions() {
                if let Ok(rg) = formula_to_guarded(&r.formula) {
                    restrictions.push(rg);
                }
            }
            let tq = match lemma.trace_quantifier {
                TraceQuantifier::AllTraces =>
                    tamarin_parser::ast::TraceQuantifier::AllTraces,
                TraceQuantifier::ExistsTrace =>
                    tamarin_parser::ast::TraceQuantifier::ExistsTrace,
            };
            let mut sys = formula_to_system(
                restrictions,
                SourceKind::RawSources,
                tq,
                false,
                &g,
            );
            // Reuse lemmas from earlier in the theory.
            let mut reuse: Vec<Guarded> = Vec::new();
            for prior in typed.lemmas() {
                if prior.name == lname { break; }
                if !prior.attributes.iter().any(|a| matches!(a, LemmaAttr::Reuse)) {
                    continue;
                }
                if !matches!(prior.trace_quantifier, TraceQuantifier::AllTraces) {
                    continue;
                }
                if let Ok(rg) = formula_to_guarded(&prior.formula) {
                    reuse.push(rg);
                }
            }
            sys.insert_lemmas(reuse);
            // Root method is `Sorry("initial")` until the user (or
            // autoprover) applies a method.
            let root = ProofNode {
                method: ProofMethod::Sorry(Some("initial".into())),
                sys,
                children: BTreeMap::new(),
                status: NodeStatus::Open,
                annotated: true,
            };
            by_lemma.insert(lname, LemmaProofState { root });
        }
        Ok(ProofState {
            ctx: Arc::new(Mutex::new(ctx)),
            by_lemma: Arc::new(Mutex::new(by_lemma)),
        })
    }

    /// Apply a `ProofMethod` at `path` in the lemma's proof tree.
    /// Returns the new node status, or an error string for malformed
    /// inputs.
    pub fn apply_at_path(
        &self,
        lemma: &str,
        path: &[String],
        method: ProofMethod,
    ) -> Result<NodeStatus, String> {
        let ctx_guard = self.ctx.lock();
        let mut by_lemma = self.by_lemma.lock();
        let lp = by_lemma.get_mut(lemma)
            .ok_or_else(|| format!("unknown lemma: {}", lemma))?;
        let node = navigate_mut(&mut lp.root, path)
            .ok_or_else(|| format!("path not found: {:?}", path))?;
        // Run the method against the node's current system.
        let cases = exec_proof_method(&ctx_guard, &method, &node.sys)
            .ok_or_else(|| format!("method {:?} not applicable", method))?;
        node.method = method;
        node.children.clear();
        if cases.is_empty() {
            // Empty case-list = contradiction closes the branch.
            node.status = NodeStatus::Contradictory;
        } else {
            let mut any_open = false;
            for (name, sys) in cases {
                // Eagerly classify each child as finished / open.
                let (status, leaf_method) = match is_finished(&ctx_guard, &sys) {
                    Some(r) => {
                        let s = match &r {
                            tamarin_theory::constraint::solver::proof_method::Result::Solved =>
                                NodeStatus::Solved,
                            tamarin_theory::constraint::solver::proof_method::Result::Contradictory(_) =>
                                NodeStatus::Contradictory,
                            tamarin_theory::constraint::solver::proof_method::Result::Unfinishable =>
                                NodeStatus::Unfinishable,
                        };
                        (s, ProofMethod::Finished(r))
                    }
                    None => {
                        any_open = true;
                        (NodeStatus::Open, ProofMethod::Sorry(None))
                    }
                };
                let child = ProofNode {
                    method: leaf_method,
                    sys,
                    children: BTreeMap::new(),
                    status,
                    annotated: true,
                };
                node.children.insert(name, child);
            }
            node.status = if any_open { NodeStatus::Open } else {
                // Rollup: prefer Solved → Sorry → Unfinishable →
                // Contradictory, matching Haskell's `ProofStatus`
                // semigroup.
                let mut s = NodeStatus::Contradictory;
                for c in node.children.values() {
                    s = combine_status(s, c.status.clone());
                }
                s
            };
        }
        Ok(node.status.clone())
    }

    /// Replace a lemma's root with a brand new search result (e.g.
    /// from autoprove).  Returns Ok on success.
    pub fn replace_root(&self, lemma: &str, root: ProofNode) -> Result<(), String> {
        let mut by_lemma = self.by_lemma.lock();
        let lp = by_lemma.get_mut(lemma)
            .ok_or_else(|| format!("unknown lemma: {}", lemma))?;
        lp.root = root;
        Ok(())
    }

    /// Fork this proof state: share the same `ProofContext` (so we
    /// don't re-precompute sources / re-boot Maude) but deep-copy the
    /// per-lemma proof trees so mutations on one idx don't leak to the
    /// other.  Mirrors Haskell `modifyTheory`'s value-typed
    /// `IncrementalProof` semantics: each version-fork sees the source
    /// tree at the moment of fork, then evolves independently.
    pub fn fork(&self) -> Self {
        let src = self.by_lemma.lock();
        let mut clone: BTreeMap<String, LemmaProofState> = BTreeMap::new();
        for (k, v) in src.iter() {
            clone.insert(k.clone(), LemmaProofState { root: v.root.clone() });
        }
        ProofState {
            ctx: self.ctx.clone(),
            by_lemma: Arc::new(Mutex::new(clone)),
        }
    }

    /// Read the root ProofNode for a lemma.
    pub fn get_root(&self, lemma: &str) -> Option<ProofNode> {
        self.by_lemma.lock().get(lemma).map(|lp| lp.root.clone())
    }

    /// Find the system at the given path (root if empty).
    pub fn get_system_at(
        &self,
        lemma: &str,
        path: &[String],
    ) -> Option<tamarin_theory::constraint::system::System> {
        let by_lemma = self.by_lemma.lock();
        let lp = by_lemma.get(lemma)?;
        let node = navigate(&lp.root, path)?;
        Some(node.sys.clone())
    }
}

fn navigate<'a>(node: &'a ProofNode, path: &[String]) -> Option<&'a ProofNode> {
    let mut cur = node;
    for seg in path {
        cur = cur.children.get(seg)?;
    }
    Some(cur)
}

/// Public alias for the internal `navigate` — used by other handlers
/// that need to inspect a node at a specific proof path.
pub fn navigate_at<'a>(node: &'a ProofNode, path: &[String]) -> Option<&'a ProofNode> {
    navigate(node, path)
}

fn navigate_mut<'a>(node: &'a mut ProofNode, path: &[String]) -> Option<&'a mut ProofNode> {
    let mut cur = node;
    for seg in path {
        cur = cur.children.get_mut(seg)?;
    }
    Some(cur)
}

fn combine_status(a: NodeStatus, b: NodeStatus) -> NodeStatus {
    use NodeStatus::*;
    match (&a, &b) {
        (Solved, _) | (_, Solved) => Solved,
        (Sorry, _) | (_, Sorry) => Sorry,
        (Unfinishable, _) | (_, Unfinishable) => Unfinishable,
        (Open, _) | (_, Open) => Open,
        (Contradictory, Contradictory) => Contradictory,
    }
}

/// Parse a slash-separated proof method path piece, mirroring
/// Haskell's interactive URL.
///
/// Examples:
///   - `simplify`              → `Simplify`
///   - `induction`             → `Induction`
///   - `sorry`                 → `Sorry(None)`
///   - `solve/<goal-id>`       → `SolveGoal(g)` where `g` is the
///     `goal-id`-th goal in the target system (1-based, matching
///     Haskell's `goalNr` rendering).
///
/// The method-string is split from the path-tail at the LAST segment
/// by the caller; this fn just parses the head segment + an optional
/// goal-id segment for `solve`.
pub fn parse_method(segments: &[String], sys: &tamarin_theory::constraint::system::System)
    -> Option<ProofMethod>
{
    let head = segments.first()?.to_lowercase();
    match head.as_str() {
        "simplify" => Some(ProofMethod::Simplify),
        "induction" => Some(ProofMethod::Induction),
        "sorry" => Some(ProofMethod::Sorry(None)),
        "solve" => {
            let id: usize = segments.get(1)?.parse().ok()?;
            // 1-based — Haskell `goalNr` starts at 1.
            let (g, _st) = sys.goals.iter()
                .filter(|(_, st)| !st.solved)
                .nth(id.saturating_sub(1))?;
            Some(ProofMethod::SolveGoal(g.clone()))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------
// HTML rendering of the proof tree
// ---------------------------------------------------------------------

/// Render the proof tree for a lemma as nested HTML — mirrors
/// Haskell's `prettyProof` / `Web/Hamlet/proof.hamlet`.
pub fn render_proof_tree_html(
    idx: usize,
    lemma: &str,
    root: &ProofNode,
) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "<h2>Proof of <code>{}</code></h2>\n",
        html_escape(lemma),
    ));
    let path: Vec<String> = Vec::new();
    render_node(&mut out, idx, lemma, &path, root);
    out
}

/// Render the per-path sub-proof snippet.  Mirrors Haskell's
/// `subProofSnippet` (`src/Web/Theory.hs:513-611`).  Emits:
///
///   1. `<h3>Applicable Proof Methods: <heuristic></h3>`
///      `<div class="preformatted methods">…numbered method links…</div>`
///      `a. <autoprove>` etc.
///   2. `<h3>Constraint system</h3>`
///      `<dynamic-graph graphSrc="…">` (when the system has nodes/edges)
///      `<div class="preformatted sequent">…prettyNonGraphSystem…</div>`
///   3. `<h3>N sub-case(s)</h3>`
///      `<h4>case <name></h4>` + `<static-graph graphSrc="…">` per child.
pub fn render_sub_proof_snippet(
    idx: usize,
    lemma: &str,
    proof_path: &[String],
    node: &ProofNode,
    ctx: &ProofContext,
) -> String {
    let mut out = String::new();
    let url_path = encode_path(proof_path);
    // Applicable Proof Methods.
    write_applicable_methods(&mut out, idx, lemma, &url_path, &node.sys, ctx);
    out.push_str("<p></p>\n");
    // Constraint system.
    out.push_str("<h3>Constraint system</h3>\n");
    if has_graph_content(&node.sys) {
        let src = format!(
            "/thy/trace/{idx}/interactive-graph-def/proof/{lemma}{path}",
            idx = idx,
            lemma = url_path_escape(lemma),
            path = url_path,
        );
        out.push_str(&format!(
            "<dynamic-graph graphSrc=\"{}\"></dynamic-graph>\n",
            src,
        ));
    }
    out.push_str("<div class=\"preformatted sequent\"><pre>");
    out.push_str(&html_escape(&pretty_non_graph_system(&node.sys)));
    out.push_str("</pre></div>\n");
    // Sub-cases.
    let n_cases = node.children.len();
    out.push_str(&format!("<h3>{} sub-case(s)</h3>\n", n_cases));
    for case_name in node.children.keys() {
        let mut child_path = proof_path.to_vec();
        child_path.push(case_name.clone());
        let child_url = encode_path(&child_path);
        out.push_str(&format!("<h4>case {}</h4>\n", html_escape(case_name)));
        let src = format!(
            "/thy/trace/{idx}/interactive-graph-def/proof/{lemma}{path}",
            idx = idx,
            lemma = url_path_escape(lemma),
            path = child_url,
        );
        out.push_str(&format!(
            "<static-graph graphSrc=\"{}\"></static-graph>\n",
            src,
        ));
    }
    out
}

fn has_graph_content(sys: &System) -> bool {
    !sys.nodes.is_empty() || !sys.edges.is_empty()
}

fn write_applicable_methods(
    out: &mut String,
    idx: usize,
    lemma: &str,
    url_path: &str,
    sys: &System,
    ctx: &ProofContext,
) {
    // Match Haskell `rankProofMethods` (`ProofMethod.hs:653-668`):
    // candidates come from `proofMethods`, then `execMethods` filters
    // via `mapMaybe execMethod` to those that successfully apply.  In
    // Rust, `candidate_methods` is the un-filtered list (used by the
    // search loop which tries each in order); for the UI we must
    // filter, so the user-visible numbering matches the actual click
    // semantics (otherwise the user can click an inapplicable method
    // and get an alert).  Filtering is exactly Haskell's
    // `execProofMethod` call — same cost the search loop pays.
    let methods: Vec<ProofMethod> = candidate_methods(sys, ctx, 0)
        .into_iter()
        .filter(|m| exec_proof_method(ctx, m, sys).is_some())
        .collect();
    if methods.is_empty() {
        out.push_str("<h3>Constraint System is Solved or Unfinishable</h3>\n");
        return;
    }
    out.push_str("<h3>Applicable Proof Methods:</h3>\n");
    out.push_str("<div class=\"preformatted methods\"><pre>");
    // Mirror Haskell `Web.Theory.subProofSnippet` (`Web/Theory.hs:593-596`):
    // each ranked method N (1-based) emits
    //   <a class="internal-link proof-method"
    //      href="/thy/trace/<idx>/main/method/<lemma>/<N>/<sub>">label</a>
    // The frontend's `mainDisplay.applyProofMethod` keyboard shortcuts
    // (1..9) target `div.methods a.internal-link`, and the click handler
    // for `internal-link` posts the URL via `server.handleJson` —
    // landing on our `/main/method/...` route which dispatches to
    // `apply_method_and_redirect` and returns a `{redirect}`.
    for (i, m) in methods.iter().enumerate() {
        let nr = i + 1;
        out.push_str(&format!(
            "{nr}. <a class=\"internal-link proof-method\" href=\"/thy/trace/{idx}/main/method/{lemma}/{nr}{path}\">{label}</a>\n",
            nr = nr,
            idx = idx,
            lemma = url_path_escape(lemma),
            path = url_path,
            label = html_escape(&method_label(m)),
        ));
    }
    out.push_str("</pre></div>\n");
    // Autoprove links — match Haskell's `a.` / `b.` / `s.` style.
    out.push_str(&format!(
        "<p>a. <a class=\"internal-link autoprove\" href=\"/thy/trace/{idx}/autoprove/idfs/0/False/proof/{lemma}{path}\">autoprove</a> &nbsp; \
         b. <a class=\"internal-link bounded-autoprove\" href=\"/thy/trace/{idx}/autoprove/idfs/5/False/proof/{lemma}{path}\">autoprove</a> with proof-depth bound 5 &nbsp; \
         s. <a class=\"internal-link autoprove-all\" href=\"/thy/trace/{idx}/autoproveAll/idfs/0/proof/{lemma}{path}\">autoprove</a> for all lemmas\n</p>\n",
        idx = idx,
        lemma = url_path_escape(lemma),
        path = url_path,
    ));
}

fn render_node(
    out: &mut String,
    idx: usize,
    lemma: &str,
    path: &[String],
    node: &ProofNode,
) {
    let url_path = encode_path(path);
    out.push_str("<div class=\"proof-node\">");
    // Method line with status badge.
    let badge = status_badge(&node.status);
    out.push_str(&format!(
        "<span class=\"proof-method\">{}</span> {}",
        html_escape(&method_label(&node.method)),
        badge,
    ));
    // Action links: depending on method/status, offer apply links.
    if matches!(node.method,
        ProofMethod::Sorry(_) | ProofMethod::Invalidated)
        && matches!(node.status, NodeStatus::Open)
    {
        // Offer Simplify / Induction / Solve links.
        out.push_str(" <span class=\"proof-actions\">");
        out.push_str(&action_link(idx, lemma, &url_path, "simplify", "[simplify]"));
        out.push_str(&action_link(idx, lemma, &url_path, "induction", "[induction]"));
        // Solve links — list the unsolved goals at this node, capped
        // at 8 so the UI doesn't blow up on systems with many open
        // goals.
        let mut shown = 0usize;
        for (i, (g, st)) in node.sys.goals.iter().enumerate() {
            if st.solved { continue; }
            if shown >= 8 { break; }
            // Haskell's `goalNr` is 1-based on UNSOLVED goals; we
            // mirror that by counting only unsolved entries here.
            let nr = node.sys.goals.iter()
                .take(i + 1)
                .filter(|(_, s)| !s.solved)
                .count();
            let goal_label = goal_summary(g);
            out.push_str(&action_link(
                idx, lemma, &url_path,
                &format!("solve/{}", nr),
                &format!("[solve {}: {}]", nr, html_escape(&goal_label)),
            ));
            shown += 1;
        }
        out.push_str("</span>");
    }
    out.push_str("</div>");
    // Children indented underneath.  Mirror Haskell's
    // `<h4>case <name></h4>` per child shape (Web/Theory.hs:605-611),
    // wrapped in a single `<div class="proof-children">` so the indent
    // reads consistently.
    if !node.children.is_empty() {
        out.push_str("<div class=\"proof-children\" style=\"margin-left:1.5em\">");
        for (case_name, child) in &node.children {
            let mut child_path = path.to_vec();
            child_path.push(case_name.clone());
            out.push_str(&format!(
                "<h4>case {}</h4>\n",
                html_escape(case_name)));
            render_node(out, idx, lemma, &child_path, child);
        }
        out.push_str("</div>");
    }
}

/// Port of Haskell's `prettyProofMethod`
/// (`lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs:1307`).
pub fn method_label(m: &ProofMethod) -> String {
    match m {
        ProofMethod::Sorry(reason) => match reason {
            Some(r) => format!("sorry /* {} */", r),
            None => "sorry".to_string(),
        },
        ProofMethod::Simplify => "simplify".to_string(),
        ProofMethod::SolveGoal(g) => format!("solve( {} )", goal_summary(g)),
        ProofMethod::Induction => "induction".to_string(),
        ProofMethod::Finished(r) => match r {
            tamarin_theory::constraint::solver::proof_method::Result::Solved =>
                "SOLVED // trace found".to_string(),
            tamarin_theory::constraint::solver::proof_method::Result::Contradictory(reason) => {
                match reason {
                    Some(why) => format!("contradiction /* {} */", pretty_contradiction(why)),
                    None => "contradiction".to_string(),
                }
            }
            tamarin_theory::constraint::solver::proof_method::Result::Unfinishable =>
                "UNFINISHABLE // reducible operator in subterm".to_string(),
        }
        ProofMethod::Invalidated =>
            "// proof may have been invalidated by editing a reuse lemma above. You should".to_string(),
        ProofMethod::RawSolve(inner) =>
            format!("solve( {} )", inner),
    }
}

/// Port of Haskell's `prettyContradiction`
/// (`lib/theory/src/Theory/Constraint/Solver/Contradictions.hs:457`).
fn pretty_contradiction(c: &tamarin_theory::constraint::solver::contradictions::Contradiction) -> String {
    use tamarin_theory::constraint::solver::contradictions::Contradiction::*;
    match c {
        Cyclic => "cyclic".to_string(),
        SubtermCyclic => "contradictory subterm store".to_string(),
        IncompatibleEqs => "incompatible equalities".to_string(),
        NonNormalTerms => "non-normal terms".to_string(),
        ForbiddenExp => "non-normal exponentiation rule instance".to_string(),
        ForbiddenBP => "non-normal bilinear pairing rule instance".to_string(),
        ForbiddenKD => "forbidden KD-fact".to_string(),
        ForbiddenChain => "forbidden chain".to_string(),
        ImpossibleChain => "impossible chain".to_string(),
        NonInjectiveFactInstance(a, b, c) =>
            format!("non-injective facts ({}, {}, {})",
                pretty_lvar(a), pretty_lvar(b), pretty_lvar(c)),
        FormulasFalse => "from formulas".to_string(),
        SuperfluousLearn(m, v) => {
            use tamarin_term::pretty::pretty_lnterm;
            format!("\"{}\" derived before and after \"{}\"",
                pretty_lnterm(m), pretty_lvar(v))
        }
        NodeAfterLast(i, j) =>
            format!("node {} after last node {}", pretty_lvar(j), pretty_lvar(i)),
    }
}

fn pretty_lvar(v: &tamarin_term::lterm::LVar) -> String {
    let mut s = String::new();
    tamarin_term::pretty::pp_lvar(v, &mut s);
    s
}

fn status_badge(s: &NodeStatus) -> String {
    let (color, label) = match s {
        NodeStatus::Solved => ("#138a36", "✓ verified"),
        NodeStatus::Contradictory => ("#138a36", "✓ closed"),
        NodeStatus::Unfinishable => ("#8a6213", "? unfinishable"),
        NodeStatus::Sorry => ("#8a1313", "✗ sorry"),
        NodeStatus::Open => ("#136a8a", "○ open"),
    };
    format!("<span class=\"proof-status\" style=\"color:{}\">{}</span>",
        color, label)
}

fn action_link(
    idx: usize, lemma: &str,
    url_path: &str, method: &str, label: &str,
) -> String {
    format!(
        "<a class=\"ajax-action proof-step\" href=\"/thy/trace/{idx}/proof-step/{lemma}{path}/{method}\">{label}</a> ",
        idx = idx,
        lemma = url_path_escape(lemma),
        path = url_path,
        method = method,
        label = label,
    )
}

fn url_path_escape(s: &str) -> String {
    s.chars().map(|c| match c {
        c if c.is_ascii_alphanumeric() || c == '_' || c == '-' || c == '.' => c.to_string(),
        c => format!("%{:02X}", c as u32),
    }).collect()
}

/// Match Haskell's `prefixWithUnderscore`: empty segments become `_`
/// so the Yesod / axum routers don't collapse adjacent slashes.
fn prefix_with_underscore(s: &str) -> String {
    if s.is_empty() { "_".into() }
    else if s.starts_with('_') { format!("_{}", s) }
    else { s.to_string() }
}

fn encode_path(path: &[String]) -> String {
    if path.is_empty() { return String::new(); }
    let mut s = String::new();
    for seg in path {
        s.push('/');
        s.push_str(&url_path_escape(&prefix_with_underscore(seg)));
    }
    s
}

/// Inverse of `prefix_with_underscore`.
pub fn unprefix_underscore(s: &str) -> String {
    if s == "_" { String::new() }
    else if s.starts_with("__") { s[1..].to_string() }
    else { s.to_string() }
}

fn goal_summary(g: &Goal) -> String {
    use tamarin_term::pretty::pretty_lnterm;
    match g {
        Goal::Action(nid, fa) => {
            let tag = tamarin_theory::fact::fact_tag_name(&fa.tag);
            let args: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
            format!("{}({}) @ #{}{}", tag, args.join(","), nid.name, nid.idx)
        }
        Goal::Chain(src, tgt) => format!("Chain #{}{} -> #{}{}",
            src.0.name, src.0.idx, tgt.0.name, tgt.0.idx),
        Goal::Premise(np, fa) => {
            let tag = tamarin_theory::fact::fact_tag_name(&fa.tag);
            let args: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
            format!("{}({}) @ prem #{}{}", tag, args.join(","),
                np.0.name, np.0.idx)
        }
        Goal::Split(s) => format!("Split({:?})", s),
        Goal::Disj(_) => "Disj(...)".to_string(),
        Goal::Subterm((a, b)) => format!("{} \u{2291} {}",
            pretty_lnterm(a), pretty_lnterm(b)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        for c in [
            "/home/linuxbrew/.linuxbrew/bin/maude",
            "/usr/local/bin/maude",
            "/opt/homebrew/bin/maude",
            "/usr/bin/maude",
            "maude",
        ] {
            if std::path::Path::new(c).exists() {
                return Some(c.to_string());
            }
        }
        None
    }

    #[test]
    fn build_state_for_trivial_theory() {
        let mp = match maude_path() { Some(p) => p, None => return };
        let src = r#"
theory T begin
rule Setup: [Fr(~k)] --[Setup(~k)]-> [Out(~k)]
lemma trivial: exists-trace
  "Ex k #i. Setup(k) @ #i"
end
"#;
        let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
        let state = ProofState::new(&pt, &mp).expect("build state");
        // Should have one lemma initialised.
        let root = state.get_root("trivial").expect("trivial root");
        assert!(matches!(root.method, ProofMethod::Sorry(_)));
        assert!(matches!(root.status, NodeStatus::Open));
    }

    #[test]
    fn apply_simplify_step() {
        let mp = match maude_path() { Some(p) => p, None => return };
        let src = r#"
theory T begin
rule Setup: [Fr(~k)] --[Setup(~k)]-> [Out(~k)]
lemma trivial: exists-trace
  "Ex k #i. Setup(k) @ #i"
end
"#;
        let pt = tamarin_parser::parse_theory(src, &[]).expect("parse");
        let state = ProofState::new(&pt, &mp).expect("build state");
        // Apply simplify at the root.
        let path: Vec<String> = Vec::new();
        let r = state.apply_at_path("trivial", &path, ProofMethod::Simplify);
        assert!(r.is_ok(), "simplify should succeed: {:?}", r);
        let root = state.get_root("trivial").expect("root");
        // Method should now be Simplify (not Sorry).
        assert!(matches!(root.method, ProofMethod::Simplify),
            "root method after simplify: {:?}", root.method);
    }

    #[test]
    fn parse_method_simplify_induction_sorry() {
        let sys = tamarin_theory::constraint::system::System::empty();
        assert!(matches!(parse_method(&["simplify".into()], &sys),
            Some(ProofMethod::Simplify)));
        assert!(matches!(parse_method(&["induction".into()], &sys),
            Some(ProofMethod::Induction)));
        assert!(matches!(parse_method(&["sorry".into()], &sys),
            Some(ProofMethod::Sorry(None))));
        assert!(parse_method(&["solve".into()], &sys).is_none());
        assert!(parse_method(&["bogus".into()], &sys).is_none());
    }

    #[test]
    fn render_smoke_test() {
        let root = ProofNode {
            method: ProofMethod::Sorry(None),
            sys: tamarin_theory::constraint::system::System::empty(),
            children: BTreeMap::new(),
            status: NodeStatus::Open,
            annotated: true,
        };
        let html = render_proof_tree_html(1, "L", &root);
        assert!(html.contains("Proof of"));
        assert!(html.contains("L"));
    }
}
