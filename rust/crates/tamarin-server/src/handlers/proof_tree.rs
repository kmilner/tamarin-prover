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
use tamarin_theory::constraint::solver::context::{ProofContext, UseInduction};
use tamarin_theory::constraint::solver::goals::GoalRanking;
use tamarin_theory::constraint::solver::proof_method::{
    exec_proof_method, finished_subterms, is_finished, ProofMethod,
};
use tamarin_theory::constraint::solver::search::{
    candidate_methods_with_expl, NodeStatus, ProofNode,
};
use tamarin_theory::constraint::system::{formula_to_system, SourceKind, System};
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::guarded::{formula_to_guarded, Guarded};
use tamarin_theory::pretty_system::pretty_non_graph_system;
use tamarin_theory::theory::{LemmaAttr, OpenProtoRule, TraceQuantifier};

use crate::handlers::path_parse::{prefix_with_underscore, url_path_escape};
use crate::handlers::root::html_escape;

/// Per-lemma live proof state, held inside [`TheoryEntry`].
pub struct LemmaProofState {
    pub root: ProofNode,
}

/// Per-lemma search settings that HS/`--prove` install into the
/// `ProofContext` before ranking THAT lemma's applicable proof methods.
///
/// The web server builds ONE shared `ProofContext` (`Arc<Mutex<…>>`) for a
/// theory (so it doesn't re-precompute sources / re-boot Maude per click),
/// but HS's per-lemma `getProofContext` sets `pcUseInduction` and
/// `pcHeuristic` from the lemma's attributes + the theory's `heuristic:`
/// directive.  Without these the shared ctx defaults to `AvoidInduction` +
/// `Smart`, which diverges from HS at the display / method-index sites that
/// recompute `candidate_methods*` / `ranking_for_depth`.
///
/// Mirrors `tamarin_theory::prove::prove_lemma`:
///   - `use_induction`: `UseInduction` iff the lemma carries `[use_induction]`
///     or `[sources]` (prove.rs:749-753); else the `AvoidInduction` default.
///   - `heuristic`: per-lemma `[heuristic=..]` > theory-level `heuristic:`
///     directive, parsed via `parse_heuristic_str_with_tactics`
///     (prove.rs:601-623, minus the CLI `--heuristic` the web path never has).
///     `None` ⇒ HS default `Smart`.
///
/// Built ONCE in [`ProofState::new`] and never mutated → held lock-free
/// (`Arc<BTreeMap<…>>`); each read site copies its two fields into the
/// Mutex-locked ctx before ranking, so there is no stale read across
/// interleaved requests.
pub struct LemmaSearchSettings {
    pub use_induction: UseInduction,
    pub heuristic: Option<Vec<GoalRanking>>,
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
    /// Immutable, lock-free per-lemma search settings (see
    /// [`LemmaSearchSettings`]).  Built once in [`ProofState::new`]; read at
    /// every display / method-index site to override the shared ctx's
    /// `use_induction` + `heuristic` for the lemma being ranked.
    pub lemma_settings: Arc<BTreeMap<String, LemmaSearchSettings>>,
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
        // Build the ProofContext WITH the theory's restrictions, mirroring
        // HS `closeRuleCache`'s `safetyRestrictions` (Rule.hs:155-156) and the
        // `--prove` path (`prove.rs` `ProverSession::new`, which builds the
        // context via `new_with_restrictions`).  Without the restrictions the
        // precomputed source cases (`ctx.full_sources`, surfaced on the web
        // `main/cases/{raw,refined}` pages) lack the `lemmas:` safety formulas
        // and any restriction-driven case pruning, diverging from HS.  The
        // initial per-lemma proof snippets are unaffected — they render the
        // root system (which already installs restrictions via
        // `formula_to_system`) and never graft precomputed sources.
        let ctx_restrictions: Vec<Guarded> = typed.restrictions()
            .filter_map(|r| formula_to_guarded(&r.formula).ok())
            .collect();
        let ctx = ProofContext::new_with_restrictions(maude, rules, ctx_restrictions);
        // Build the initial system for every lemma.
        let mut by_lemma: BTreeMap<String, LemmaProofState> = BTreeMap::new();
        // Per-lemma search settings HS installs before ranking each lemma's
        // applicable methods (mirrors `prove::prove_lemma` heuristic/
        // use_induction resolution).  Built once, read lock-free thereafter.
        let mut lemma_settings: BTreeMap<String, LemmaSearchSettings> = BTreeMap::new();
        for lemma in typed.lemmas() {
            let lname = lemma.name.clone();
            // --- Per-lemma search settings (prove.rs:601-623,749-753) -------
            // `use_induction`: forced on by `[use_induction]` or `[sources]`.
            let use_induction = if lemma.attributes.iter().any(|a| matches!(a,
                LemmaAttr::UseInduction | LemmaAttr::Sources))
            {
                UseInduction::UseInduction
            } else {
                UseInduction::AvoidInduction
            };
            // `heuristic`: per-lemma `[heuristic=..]` > theory `heuristic:`.
            // There is no CLI `--heuristic` on the web path, so the CLI
            // override branch of `prove::prove_lemma` is skipped entirely.
            let lemma_heuristic: Option<&str> = lemma.attributes.iter()
                .find_map(|a| match a {
                    LemmaAttr::Heuristic(s) => Some(s.as_str()),
                    _ => None,
                });
            let heuristic_raw: Option<String> = match lemma_heuristic {
                Some(h) => Some(h.to_string()),
                None => typed.heuristic.first().cloned(),
            };
            // NOTE: oracle-relative paths in a web `heuristic:` directive are
            // NOT yet prefixed with the theory dir (HS
            // `prepend_theory_dir_to_oracle_paths`, prove.rs:130, is private to
            // that module).  The observed web cases (`use_induction`, SAPiC
            // `p`) are not oracles; a future oracle-on-web `heuristic:` case
            // must thread that prefixing through here.
            let heuristic = heuristic_raw.map(|h| {
                tamarin_theory::constraint::solver::goals::parse_heuristic_str_with_tactics(
                    &h, &typed.in_file, &typed.tactic)
            });
            lemma_settings.insert(
                lname.clone(),
                LemmaSearchSettings { use_induction, heuristic });
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
            // HS `getProofContext` / `lemmaSourceKind` (ClosedTheory.hs:116,
            // Lemma.hs:38-41): a `sources` lemma is proved under RAW sources;
            // every other lemma under REFINED sources.  `mkSystem` builds the
            // initial system with `pcSourceKind ctxt` (Prover.hs:319-326), and
            // the system's `sSourceKind` shows in the sequent as
            // `allowed cases: raw|refined`.
            let source_kind = if lemma.attributes.iter()
                .any(|a| matches!(a, LemmaAttr::Sources))
            {
                SourceKind::RawSources
            } else {
                SourceKind::RefinedSources
            };
            let mut sys = formula_to_system(
                restrictions,
                source_kind,
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
            // Root method is the unproven `sorry` (no reason) until the
            // user (or autoprover) applies a method.  Mirrors HS
            // `unproven = sorry Nothing` (Proof.hs:255-256), which
            // `prettyProofMethod` renders as a plain `sorry`.
            let root = ProofNode {
                method: ProofMethod::Sorry(None),
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
            lemma_settings: Arc::new(lemma_settings),
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
            // Share the immutable per-lemma settings map (same theory).
            lemma_settings: self.lemma_settings.clone(),
        }
    }

    /// Read the root ProofNode for a lemma.
    pub fn get_root(&self, lemma: &str) -> Option<ProofNode> {
        self.by_lemma.lock().get(lemma).map(|lp| lp.root.clone())
    }

    /// Copy the lemma's per-lemma search settings ([`LemmaSearchSettings`])
    /// into a locked `ProofContext` before ranking that lemma's applicable
    /// proof methods.  A no-op when the lemma has no settings (unknown lemma).
    ///
    /// Call this on a `mut` ctx guard right after locking, at every display /
    /// method-index-mapping site — it makes the shared web `ProofContext`
    /// behave like HS's per-lemma `getProofContext` (`pcUseInduction` +
    /// `pcHeuristic`) for the ranking that follows.  The autoprove path builds
    /// its OWN correct per-lemma context via `prove_lemma`, so it must NOT call
    /// this.
    pub fn install_lemma_settings(&self, ctx: &mut ProofContext, lemma: &str) {
        if let Some(s) = self.lemma_settings.get(lemma) {
            ctx.use_induction = s.use_induction;
            ctx.heuristic = s.heuristic.clone();
        }
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

/// Port of HS `getProofPaths` (`Web/Theory.hs:2116-2120`):
///
/// ```haskell
/// getProofPaths proof = ([], psMethod . root $ proof) : go proof
///   where
///     go = concatMap paths . M.toList . children
///     paths (lbl, prf) = ([lbl], psMethod . root $ prf)
///                        : map (first (lbl:)) (go prf)
/// ```
///
/// Pre-order over the proof tree: each entry pairs the case-name path from
/// the root with the proof method stored at that node.  RS's `children` is a
/// `BTreeMap`, whose iteration order matches HS's `M.toList` (sorted by
/// `CaseName`).  Used by `next`/`prev` (`nextThyPath`/`nextSmartThyPath`) to
/// enumerate the navigable proof positions in order.
pub fn get_proof_paths(root: &ProofNode) -> Vec<(Vec<String>, ProofMethod)> {
    let mut out = vec![(Vec::new(), root.method.clone())];
    out.extend(proof_paths_go(root));
    out
}

fn proof_paths_go(node: &ProofNode) -> Vec<(Vec<String>, ProofMethod)> {
    let mut out = Vec::new();
    for (lbl, child) in &node.children {
        out.push((vec![lbl.clone()], child.method.clone()));
        for (mut p, m) in proof_paths_go(child) {
            p.insert(0, lbl.clone());
            out.push((p, m));
        }
    }
    out
}

/// Port of HS `isInterestingMethod` (`Web/Theory.hs:1875-1879`): the proof
/// methods that `nextSmartThyPath`/`prevSmartThyPath` stop on — an open
/// `Sorry` leaf, or a `Finished` `Solved`/`Unfinishable` terminal.
pub fn is_interesting_method(m: &ProofMethod) -> bool {
    use tamarin_theory::constraint::solver::proof_method::Result as R;
    matches!(
        m,
        ProofMethod::Sorry(_)
            | ProofMethod::Finished(R::Solved)
            | ProofMethod::Finished(R::Unfinishable)
    )
}

fn navigate_mut<'a>(node: &'a mut ProofNode, path: &[String]) -> Option<&'a mut ProofNode> {
    let mut cur = node;
    for seg in path {
        cur = cur.children.get_mut(seg)?;
    }
    Some(cur)
}

/// Combine two child statuses, mirroring Haskell's `instance Semigroup
/// ProofStatus` (`lib/theory/src/Theory/Proof.hs:409-420`).  Precedence:
/// `Solved` (TraceFound) > `Sorry` (IncompleteProof) > `Unfinishable`
/// (UnfinishableProof) > `Contradictory` (CompleteProof) > `Open`
/// (UndeterminedProof, the lowest).
fn combine_status(a: NodeStatus, b: NodeStatus) -> NodeStatus {
    use NodeStatus::*;
    match (&a, &b) {
        (Solved, _) | (_, Solved) => Solved,
        (Sorry, _) | (_, Sorry) => Sorry,
        (Unfinishable, _) | (_, Unfinishable) => Unfinishable,
        (Contradictory, _) | (_, Contradictory) => Contradictory,
        _ => Open,
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
/// Haskell's `prettyProof`.
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
/// `subProofSnippet` (`src/Web/Theory.hs:513-611`; the methods section follows
/// `prettyApplicableProofMethods`, `Web/Theory.hs:540`).  Emits:
///
///   1. The Applicable Proof Methods section — delegated to
///      `write_applicable_methods`.  It emits the numbered method links
///      together with the `a.`/`b.`/`s.` autoprove links, OR, when no method
///      applies, the `<h3>Constraint System is Solved/Unfinishable</h3>`
///      fallback.
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
    // Applicable Proof Methods (ranked at this node's proof depth, HS
    // `subProofSnippet` uses `length proofPath`).
    write_applicable_methods(&mut out, idx, lemma, &url_path, proof_path.len(),
                             &node.sys, ctx);
    // HS inserts a bare `text ""` (a `<br/>` the gate drops) here — no element.
    // Constraint system.
    out.push_str("<h3>Constraint system</h3>\n");
    if has_graph_content(&node.sys) {
        // HS `refDotInteractiveDynamicPath` → `<dynamic-graph graphSrc=…>`
        // pointing at `InteractiveDotGraphR` = the `intdot` route (the HTML
        // shell that in turn fetches `interactive-graph-def`), NOT the raw
        // DOT route directly (`Web/Theory.hs:174-177`).
        let src = format!(
            "/thy/trace/{idx}/intdot/proof/{lemma}{path}",
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
        out.push_str(&format!("<h4>Case {}</h4>\n", html_escape(case_name)));
        // HS `refDotInteractiveStaticPath` → `<static-graph graphSrc=…>`
        // pointing at `InteractiveDotGraphR` = the `intdot` route
        // (`Web/Theory.hs:168-171`).
        let src = format!(
            "/thy/trace/{idx}/intdot/proof/{lemma}{path}",
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

/// Mirror of Haskell `nonEmptyGraph` (`System.hs`):
///
/// ```text
/// nonEmptyGraph sys = not $
///     M.null sNodes && null (unsolvedActionAtoms sys) &&
///     null (unsolvedChains sys) &&
///     S.null sEdges && S.null sLessAtoms
/// ```
///
/// i.e. the dotted graph is non-empty iff ANY of: nodes, unsolved
/// action atoms, unsolved chains, edges, or less-atoms is present.
/// `unsolvedActionAtoms` / `unsolvedChains` are the unsolved-status
/// `ActionG` / `ChainG` goals (`System.hs:1568-1572,1601-1605`).
fn has_graph_content(sys: &System) -> bool {
    if !sys.nodes.is_empty() || !sys.edges.is_empty() || !sys.less_atoms.is_empty() {
        return true;
    }
    sys.goals.iter().any(|(g, st)| {
        !st.solved && (g.is_action() || g.is_chain())
    })
}

fn write_applicable_methods(
    out: &mut String,
    idx: usize,
    lemma: &str,
    url_path: &str,
    depth: usize,
    sys: &System,
    ctx: &ProofContext,
) {
    // The ranking used at this proof depth (HS `subProofSnippet`:
    // `ranking = useHeuristic heuristic (length proofPath)`,
    // `Web/Theory.hs:600-602`).  Round-robin over the heuristic list
    // exactly as `rank_goals_with_inner` (goals.rs) does, defaulting to
    // `SmartRanking False` when no heuristic is configured.
    let ranking = ranking_for_depth(ctx, depth);
    // Match Haskell `rankProofMethods` (`ProofMethod.hs:520-535`):
    //   stoppingMethod = Finished <$> isFinished ctxt sys
    //   in execMethods $ maybe proofMethods ((:[]) . (,"")) stoppingMethod
    // When `isFinished` yields a verdict the WHOLE method list is replaced
    // by the single stopping method `[Finished r]` (and `execProofMethod
    // (Finished _) = Just M.empty` always survives the `execMethods`
    // filter).  Otherwise the list is `proofMethods` (Simplify / Induction
    // / SolveGoal), filtered by `execProofMethod`.  In Rust,
    // `candidate_methods` is that un-filtered `proofMethods` list (used by
    // the search loop which tries each in order); for the UI we filter via
    // `exec_proof_method` so the user-visible numbering matches the actual
    // click semantics.
    // NOTE: this ranks at heuristic depth `0`, whereas Haskell
    // `subProofSnippet` uses `length proofPath` and the method-apply route
    // `apply_method_and_redirect` (theory.rs) passes `sub.len()`.  For
    // multi-ranking heuristics at depth>0 the displayed numbering here can
    // therefore disagree with the numbering the apply route selects from.
    // Left as-is to avoid changing observed output; see
    // `apply_method_and_redirect`'s `length proofPath` comment.
    // Each entry is `(method, expl)` — `expl` is HS's `rankProofMethods`
    // explanation string (`"nr. N …"` for SolveGoal, `""` otherwise),
    // rendered by `prettyPM` as a trailing `// <expl>` line comment.
    let methods: Vec<(ProofMethod, String)> = match is_finished(ctx, sys) {
        Some(r) => vec![(ProofMethod::Finished(r), String::new())],
        None => candidate_methods_with_expl(sys, ctx, depth)
            .into_iter()
            .filter(|(m, _)| exec_proof_method(ctx, m, sys).is_some())
            .collect(),
    };
    if methods.is_empty() {
        // Mirror Haskell `prettyApplicableProofMethods` (`Web/Theory.hs:540-542`):
        //   [] | finishedSubterms ctxt sys -> "Constraint System is Solved"
        //   []                             -> "Constraint System is Unfinishable"
        // We only reach here when `is_finished` returned `None` (the
        // `Some` case produced a non-empty `[Finished r]` above), so the
        // Solved/Unfinishable choice MUST come from `finished_subterms`
        // exactly as HS does — not from `is_finished` (which is `None`
        // here and would always pick "Solved").
        if finished_subterms(ctx, sys) {
            out.push_str("<h3>Constraint System is Solved</h3>\n");
        } else {
            out.push_str("<h3>Constraint System is Unfinishable</h3>\n");
        }
        return;
    }
    // HS `subProofSnippet` (`Web/Theory.hs:544-545`):
    //   withTag "h3" [] (text "Applicable Proof Methods:" <-> comment_ (goalRankingName ranking))
    // `comment_` wraps the ranking name in an `hl_comment` span the gate
    // unwraps to plain text, so we emit the text directly.
    out.push_str(&format!(
        "<h3>Applicable Proof Methods: {}</h3>\n",
        html_escape(&ranking.ranking_name()),
    ));
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
    // HS lays the whole list out as ONE HtmlDoc (`numbered' $ zipWith
    // prettyPM [1..] pms`, Web/Theory.hs:546): each item is
    // `flushRight nW (show i) <> ". " <> (link (prettyProofMethod m) <->
    // lineComment_ expl)` — so the method text wraps (a) at HTML-ENTITY
    // fill widths (renderHtmlDoc), (b) beside-shifted by the `N. ` prefix
    // (nW+2 cols), and (c) with the trailing `// expl` comment
    // participating in the last line's fits check.  Reproduce that layout
    // per item: build the method Doc under the entity-width guard and lay
    // it with `render_at(100, 67, nW+2)` (the beside-shift budget), then
    // split the never-wrapped `<->`-joined comment back off to place the
    // `</a>` boundary.  (Continuation-line indent bytes and the blank line
    // `numbered'` inserts between items are whitespace the parity gate
    // canonicalizes; the break POSITIONS are what must match.)
    let nw = methods.len().to_string().len();
    for (i, (m, expl)) in methods.iter().enumerate() {
        let nr = i + 1;
        let prefix = format!("{:>nw$}. ", nr);
        let rendered = {
            let _guard =
                tamarin_theory::pretty_hpj::HtmlEntityWidthGuard::enable();
            let label_doc =
                tamarin_theory::pretty_theory::pretty_proof_method_doc(m);
            let full_doc = if expl.is_empty() {
                label_doc
            } else {
                // `<-> lineComment_ expl` = ` // <expl>` beside the last line.
                label_doc.beside_sp(
                    tamarin_theory::pretty_hpj::Doc::text("//")
                        .beside_sp(tamarin_theory::pretty_hpj::Doc::text(
                            expl.clone(),
                        )),
                )
            };
            full_doc.render_at(
                tamarin_theory::pretty_hpj::WEB_LINE_LENGTH,
                tamarin_theory::pretty_hpj::WEB_RIBBON,
                prefix.chars().count(),
            )
        };
        // The comment is a pure `<->` (Beside) chain — never wrapped — so
        // it is exactly the trailing ` // {expl}` of the render.
        let suffix = format!(" // {expl}");
        let (label_txt, comment) = if !expl.is_empty() {
            match rendered.strip_suffix(&suffix) {
                Some(lbl) => (lbl.to_string(), format!(" // {}", html_escape(expl))),
                None => (rendered.clone(), String::new()),
            }
        } else {
            (rendered.clone(), String::new())
        };
        out.push_str(&format!(
            "{prefix}<a class=\"internal-link proof-method\" href=\"/thy/trace/{idx}/main/method/{lemma}/{nr}{path}\">{label}</a>{comment}\n",
            prefix = prefix,
            nr = nr,
            idx = idx,
            lemma = url_path_escape(lemma),
            path = url_path,
            label = html_escape(&label_txt),
            comment = comment,
        ));
    }
    out.push_str("</pre></div>\n");
    // Autoprove links — faithful port of HS `subProofSnippet`'s
    // `autoProverLinks` (`Web/Theory.hs:547-591`), in HS order a, b, [o], s.
    // Each `AutoProverR tidx cut bound oracleBool path` renders as
    //   /thy/trace/<idx>/autoprove/<cut>/<bound>/<oracleBool>/<path>
    // with cut ∈ {idfs=CutDFS, characterize=CutNothing}; `AutoProverAllR`
    // omits the oracle flag.  `linkToPath` prepends the `internal-link`
    // class (the gate sorts class tokens, so ordering is immaterial).
    let l = url_path_escape(lemma);
    let p = url_path;
    let bound = 5; // HS `fromMaybe 5 (apBound ti.autoProver)` — default depth bound.
    // a. autoprove  (A. for all solutions)
    out.push_str(&format!(
        "a. <a class=\"internal-link autoprove\" href=\"/thy/trace/{idx}/autoprove/idfs/0/False/proof/{l}{p}\">autoprove</a> \
         (A. <a class=\"internal-link characterization\" href=\"/thy/trace/{idx}/autoprove/characterize/0/False/proof/{l}{p}\">for all solutions</a>)\n",
    ));
    // b. bounded autoprove  (B. for all solutions) with proof-depth bound N
    out.push_str(&format!(
        "b. <a class=\"internal-link bounded-autoprove\" href=\"/thy/trace/{idx}/autoprove/idfs/{bound}/False/proof/{l}{p}\">autoprove</a> \
         (B. <a class=\"internal-link bounded-characterization\" href=\"/thy/trace/{idx}/autoprove/characterize/{bound}/False/proof/{l}{p}\">for all solutions</a>) with proof-depth bound {bound}\n",
    ));
    // o. oracle autoprove — only when the heuristic uses an oracle.
    if uses_oracle(ctx) {
        out.push_str(&format!(
            "o. <a class=\"internal-link oracle-autoprove\" href=\"/thy/trace/{idx}/autoprove/idfs/0/True/proof/{l}{p}\">autoprove</a> until oracle returns nothing\n",
        ));
    }
    // s. autoprove for all lemmas  (S. for all solutions)
    out.push_str(&format!(
        "s. <a class=\"internal-link autoprove-all\" href=\"/thy/trace/{idx}/autoproveAll/idfs/0/proof/{l}{p}\">autoprove</a> \
         (S. <a class=\"internal-link characterization-all\" href=\"/thy/trace/{idx}/autoproveAll/characterize/0/proof/{l}{p}\">for all solutions</a>) for all lemmas\n",
    ));
}

/// The `GoalRanking` used at proof `depth`, mirroring HS `useHeuristic
/// (Heuristic rankings) depth = rankings !! (depth mod n)`
/// (ProofMethod.hs:581-590) — the same selection `rank_goals_with_inner`
/// performs (goals.rs).  Defaults to `SmartRanking False`.
fn ranking_for_depth(ctx: &ProofContext, depth: usize) -> GoalRanking {
    ctx.heuristic
        .as_ref()
        .and_then(|h| {
            let n = h.len();
            if n == 0 { None } else { Some(h[depth % n].clone()) }
        })
        .unwrap_or(GoalRanking::Smart(false))
}

/// HS `usesOracle` (Web/Theory.hs) — whether any ranking in the
/// configured heuristic consults an oracle script.
fn uses_oracle(ctx: &ProofContext) -> bool {
    ctx.heuristic.as_ref().is_some_and(|h| {
        h.iter().any(|r| matches!(
            r,
            GoalRanking::Oracle { .. } | GoalRanking::OracleSmart { .. }
        ))
    })
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
        // Haskell's `goalNr` is 1-based on UNSOLVED goals; we mirror that
        // with a running counter incremented per unsolved goal (identical
        // to a `take(i+1).filter(unsolved).count()` recount, but O(n)).
        let mut nr = 0usize;
        for (g, st) in node.sys.goals.iter() {
            if st.solved { continue; }
            nr += 1;
            if shown >= 8 { break; }
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
                "<h4>Case {}</h4>\n",
                html_escape(case_name)));
            render_node(out, idx, lemma, &child_path, child);
        }
        out.push_str("</div>");
    }
}

/// Port of Haskell's `prettyProofMethod`
/// (`lib/theory/src/Theory/Constraint/Solver/ProofMethod.hs:1174`).
pub fn method_label(m: &ProofMethod) -> String {
    // Delegate to the byte-faithful `--prove` renderer (HS `prettyProofMethod`)
    // so the interactive method labels carry the same fact spacing
    // (`!KU( ~ltk )`), LVar dots (`#vk.2`), and contradiction reasons as the
    // text proof.  The earlier hand-rolled `goal_summary` dropped the fact
    // multiplicity `!`, the inner-paren spaces, and the LVar index dot.
    tamarin_theory::pretty_theory::pretty_proof_method_inline(m)
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

fn encode_path(path: &[String]) -> String {
    if path.is_empty() { return String::new(); }
    let mut s = String::new();
    for seg in path {
        s.push('/');
        s.push_str(&url_path_escape(&prefix_with_underscore(seg)));
    }
    s
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
        // Mirror Haskell `prettyGoal` (`Constraints.hs:279-280`):
        //   prettyGoal (SplitG x) = "splitEqs" <> parens (show (unSplitId x))
        Goal::Split(s) => format!("splitEqs({})", s.0),
        // Mirror Haskell `prettyGoal` (`Constraints.hs:275-278`):
        //   DisjG (Disj [])  -> text "Disj" <-> operator_ "(⊥)"   (`<->` = `<+>` inserts a space)
        //   DisjG (Disj gfs) -> punctuate "  ∥" (map (parens . prettyGuarded) gfs)
        Goal::Disj(d) => {
            if d.0.is_empty() {
                "Disj (\u{22A5})".to_string()
            } else {
                let parts: Vec<String> = d.0.iter()
                    .map(|c| format!("({})",
                        tamarin_theory::pretty_formula::pretty_guarded(c)))
                    .collect();
                parts.join("  \u{2225} ")
            }
        }
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

    // --- HS-parity pretty-printing regression tests --------------------
    //
    // Each pins a byte-for-byte form of a shared Haskell printer.

    #[test]
    fn sorry_method_label_has_no_initial_comment() {
        // HS `unproven = sorry Nothing` (Proof.hs:255-256) renders via
        // `prettyProofMethod (Sorry Nothing)` (ProofMethod.hs:1180-1181)
        // as a plain `sorry` (no `/* ... */` reason).  Confirmed against
        // the repo HS prover: an unproven lemma prints `by sorry`.
        assert_eq!(method_label(&ProofMethod::Sorry(None)), "sorry");
        // The fresh root built by ProofState::new must be Sorry(None).
        // (We only assert the label form here; building a full ProofState
        // requires Maude and is covered by build_state_for_trivial_theory.)
    }

    #[test]
    fn empty_disj_goal_summary_has_space() {
        use tamarin_theory::constraint::constraints::{Disj, Goal};
        // HS `prettyGoal (DisjG (Disj [])) = text "Disj" <-> operator_ "(⊥)"`
        // (Constraints.hs:275).  `<->` = HughesPJ `<+>` (Class.hs:176),
        // which inserts a single space: `Disj (⊥)`.
        assert_eq!(goal_summary(&Goal::Disj(Disj(vec![]))), "Disj (\u{22A5})");
    }

    // (Contradiction-reason rendering is now handled by the shared
    // `--prove` renderer `tamarin_theory::pretty_theory::pretty_proof_method_inline`
    // that `method_label` delegates to; the former duplicate
    // `pretty_contradiction` port here was removed.)
}
