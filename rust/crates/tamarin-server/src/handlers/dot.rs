//! Port of Haskell's `Theory.Constraint.System.Dot` +
//! `Theory.Constraint.System.Graph.*` — convert a `System` into a
//! Graphviz DOT representation suitable for `dot -Tsvg`.
//!
//! We render the same kinds of nodes / edges / clusters as a single
//! self-contained DOT document, including an HTML-table legend for the
//! chosen abbreviations and similar-name / role clustering. Node ids,
//! fact rendering (`prettyLNFact`), action-row filtering (Diff /
//! auto-source), the cluster/preamble attribute blocks, the `roleColor`
//! cluster styling and the less-edge rendering all now match HS byte-for-
//! byte. Two intentional approximations remain (each documented at its
//! site): the per-rule node FILL colours use four fixed placeholder hexes
//! instead of HS `nodeColorMap`'s size-dependent HSV palette (only the
//! group PARTITION is faithful; an explicit per-rule `color:` attribute IS
//! honoured exactly), and the cluster subgraph identifier uses the Rust
//! `cluster_<n>` form rather than HS `createClusterNodeId`.
//!
//! Reference:
//!   - `lib/theory/src/Theory/Constraint/System/Dot.hs` (605 lines)
//!   - `lib/theory/src/Theory/Constraint/System/Graph/Graph.hs`
//!   - `lib/theory/src/Theory/Constraint/System/Graph/GraphRepr.hs`
//!
//! The shape mirrors `systemToGraph` + `dotSystemCompact`:
//!   1. Collect nodes from `sNodes`, plus "missing" nodes referenced
//!      by edges but absent from `sNodes`.
//!   2. Add unsolved-action-atom nodes (KU goals at fresh ids).
//!   3. Add the `LastAtom` node, if any.
//!   4. Emit edges from `sEdges` (conclusion → premise) styled by
//!      fact tag.
//!   5. Emit less-edges from `sLessAtoms` (dashed, coloured by
//!      reason).
//!   6. Emit chain edges from unsolved Chain goals (dotted green).
//!
//! Each rule node is rendered as a Graphviz record:
//!
//! ```text
//!     +------------+------------+
//!     |  prem_0    |  prem_1    |
//!     +------------+------------+
//!     |     <#i> : RuleName     |
//!     +------------+------------+
//!     |  conc_0    |  conc_1    |
//!     +------------+------------+
//! ```
//!
//! with port names `p0`, `p1`, ..., `c0`, `c1`, ... so that edges from
//! the `sEdges` set can target the correct slots.

use std::collections::HashMap;
use std::fmt::Write as _;

use tamarin_theory::constraint::constraints::{LessAtom, Reason};
use tamarin_theory::constraint::system::System;
use tamarin_theory::fact::{FactTag, LNFact};
use tamarin_theory::rule::{
    rule_name_string, IntrRuleACInfo, ProtoRuleName, RuleACInst, RuleInfo,
};
use tamarin_term::lterm::{LNTerm, LVar};
use tamarin_term::pretty::pretty_lnterm;

use crate::graph::abbreviation::{
    apply_abbreviations_fact, compute_abbreviations, AbbreviationOptions,
    Abbreviations,
};
use crate::graph::options::GraphOptions;
use crate::graph::repr::{
    add_cluster_by_role, add_intelligent_cluster_using_similar_names,
    compute_basic_graph_repr, extract_base_name, GEdge, GNode, MissingHint,
    NodeType,
};
use crate::graph::simplify::{compress_system, simplify_system};

// ---------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------

/// Render a [`System`] into a Graphviz DOT document with default
/// graph options (Haskell `defaultGraphOptions`: SL2 + compress).
/// Returns a self-contained `digraph G { ... }` block.
pub fn system_to_dot(sys: &System) -> String {
    system_to_dot_with(sys, &GraphOptions::default())
}

/// Render a [`System`] into a Graphviz DOT document under the given
/// options.  Applies compression, simplification, role-clustering, and
/// abbreviation discovery before emitting DOT, mirroring Haskell's
/// `systemToGraph` + `dotSystemCompact`.
pub fn system_to_dot_with(sys: &System, opts: &GraphOptions) -> String {
    // 1. Pre-render simplification.
    let working = if opts.compress { compress_system(sys.clone()) } else { sys.clone() };
    let working = simplify_system(opts.simplification_level, working);
    // 2. Build the GraphRepr.
    let mut repr = compute_basic_graph_repr(&working);
    if opts.clustering_similar_names {
        add_intelligent_cluster_using_similar_names(&mut repr);
    } else {
        add_cluster_by_role(&mut repr);
    }
    // 3. Compute abbreviations.
    let abbrevs: Abbreviations = if opts.abbreviate {
        compute_abbreviations(&repr, &AbbreviationOptions::default())
    } else {
        Abbreviations::new()
    };
    // 4. Emit DOT.
    let mut g = DotBuilder::new();
    // HS `dotGraphCompact` (Dot.hs:503) switches the graph-level defaults to
    // `setDefaultAttributesIfCluster` when the repr has any clusters.
    g.preamble(!repr.clusters.is_empty());
    let abbrev_lookup = |t: &LNTerm| -> Option<LNTerm> {
        abbrevs.get(t).map(|(a, _)| a.clone())
    };
    // Precompute a node-id -> rule map so edge styling is O(1) per edge
    // instead of scanning `working.nodes` per edge.
    let node_map: HashMap<&LVar, &RuleACInst> =
        working.nodes.iter().map(|(id, ru)| (id, ru)).collect();
    // 4a. Clusters as subgraphs.
    //
    // HS `dotCluster` (Dot.hs:547-562): each cluster gets a `roleColor`
    // derived from `extractBaseName name`, the subgraph is `style=filled`
    // with that colour, and the colour is threaded to the child nodes as
    // their `manualNodeColor` (Dot.hs:562). HS also defers ALL of a
    // cluster's edges to `dotClustersEdges` (Dot.hs:507-510/517-522), which
    // runs `mergeLessEdges` over the concatenation of every cluster's edges
    // and emits them AFTER every node/cluster — so we collect them here.
    let mut cluster_edges: Vec<GEdge> = Vec::new();
    for (i, cluster) in repr.clusters.iter().enumerate() {
        // `baseName = fromMaybe "Undefined" (extractBaseName name)`.
        let base = extract_base_name(&cluster.name)
            .unwrap_or_else(|| "Undefined".to_string());
        let color = role_color(&base);
        g.open_subgraph(i, &cluster.name, &color);
        for node in &cluster.nodes {
            emit_node_colored(&mut g, node, &abbrev_lookup, opts, Some(&color));
        }
        g.close_subgraph();
        cluster_edges.extend(cluster.edges.iter().cloned());
    }
    // 4b. Top-level nodes.
    for node in &repr.nodes {
        emit_node(&mut g, node, &abbrev_lookup, opts);
    }
    // 4c. Edges. HS emits `restEdges` (non-less) before the merged
    // `lessEdges` within each scope (`dotGraphCompact`, Dot.hs:508-509),
    // then the cluster edges last (`dotClustersEdges`).
    emit_edges_merged(&mut g, &repr.edges, &node_map);
    emit_edges_merged(&mut g, &cluster_edges, &node_map);
    // 4c. Legend (if any abbreviations were chosen).
    if !abbrevs.is_empty() {
        g.legend(&abbrevs);
    }
    g.close();
    g.into_string()
}

fn emit_node(
    g: &mut DotBuilder,
    node: &GNode,
    abbrev: &dyn Fn(&LNTerm) -> Option<LNTerm>,
    opts: &GraphOptions,
) {
    emit_node_colored(g, node, abbrev, opts, None);
}

/// `emit_node` with an optional `manual_color` — the cluster `roleColor`
/// that HS `dotCluster` threads to its child nodes as `manualNodeColor`
/// (Dot.hs:562). Only the `SystemNode` branch consults it (HS
/// `dotNodeCompact`, Dot.hs:248-256); the other node kinds ignore it.
fn emit_node_colored(
    g: &mut DotBuilder,
    node: &GNode,
    abbrev: &dyn Fn(&LNTerm) -> Option<LNTerm>,
    opts: &GraphOptions,
    manual_color: Option<&str>,
) {
    match &node.ty {
        NodeType::System(ru) => {
            let ru_abbreviated = abbreviate_rule(ru, abbrev);
            g.rule_node(&node.id, &ru_abbreviated, opts, manual_color);
        }
        NodeType::UnsolvedAction(facts) => {
            let new_facts: Vec<LNFact> = facts.iter()
                .map(|fa| apply_abbreviations_fact(abbrev, fa))
                .collect();
            g.action_node(&node.id, &new_facts);
        }
        NodeType::LastAction => g.last_node(&node.id),
        NodeType::Missing(hint) => g.missing_node(&node.id, hint),
    }
}

/// Emit a scope's edges in HS `dotGraphCompact` order: every non-less edge
/// first (`restEdges`), then the merged less-edges (`mergeLessEdges`,
/// Dot.hs:567-597). Because `LessAtom` equality ignores the reason, the
/// system holds at most one less-atom per `(smaller, larger)` pair, so the
/// `eqClasses` grouping is a no-op (singleton groups) — we only need to
/// reproduce its SORT (by `(smaller, larger)`, via `Ord LVar`) and the
/// single-reason colour. The gradient/`;weight` share code only fires for
/// multi-reason groups, which cannot arise here.
fn emit_edges_merged(
    g: &mut DotBuilder,
    edges: &[GEdge],
    node_map: &HashMap<&LVar, &RuleACInst>,
) {
    // restEdges: keep original order, drop less-edges.
    for edge in edges {
        match edge {
            GEdge::System(src, tgt) => {
                g.edge(node_map, src, tgt);
            }
            GEdge::UnsolvedChain(src, tgt) => g.chain_edge(src, tgt),
            GEdge::Less(_) => {}
        }
    }
    // lessEdges: collect, sort by (smaller, larger) like `eqClasses`, emit one
    // merged edge per pair.
    let mut lesses: Vec<&LessAtom> = edges.iter()
        .filter_map(|e| match e { GEdge::Less(la) => Some(la), _ => None })
        .collect();
    lesses.sort_by(|a, b| (&a.smaller, &a.larger).cmp(&(&b.smaller, &b.larger)));
    for la in lesses {
        g.less_edge(la);
    }
}


fn abbreviate_rule(
    ru: &RuleACInst,
    abbrev: &dyn Fn(&LNTerm) -> Option<LNTerm>,
) -> RuleACInst {
    let mut new_ru = ru.clone();
    new_ru.premises = ru.premises.iter()
        .map(|fa| apply_abbreviations_fact(abbrev, fa))
        .collect();
    new_ru.actions = ru.actions.iter()
        .map(|fa| apply_abbreviations_fact(abbrev, fa))
        .collect();
    new_ru.conclusions = ru.conclusions.iter()
        .map(|fa| apply_abbreviations_fact(abbrev, fa))
        .collect();
    new_ru
}

/// Helper used by handlers to render the [`System`] as DOT and pipe it
/// through `/usr/bin/dot -Tsvg` (or whatever's on `$PATH`) under the given
/// graph options.  Returns the SVG bytes on success.  When `dot` is
/// missing or fails, returns the DOT source instead (the frontend's
/// `intdot-staticgraph` can render DOT client-side via viz.js, so this
/// stays a useful response).
pub fn render_svg_or_dot_with(sys: &System, opts: &GraphOptions) -> RenderResult {
    let dot = system_to_dot_with(sys, opts);
    match try_render_dot_to_svg(&dot) {
        Ok(svg) => RenderResult::Svg(svg),
        Err(_) => RenderResult::Dot(dot),
    }
}

/// What we got back from `dot`.
pub enum RenderResult {
    Svg(Vec<u8>),
    Dot(String),
}

fn try_render_dot_to_svg(dot: &str) -> std::io::Result<Vec<u8>> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new("dot")
        .args(["-Tsvg"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    // Write the full DOT to `dot`'s stdin on a separate thread while the
    // main thread drains stdout/stderr via `wait_with_output`.  Doing the
    // (blocking) `write_all` inline before reading stdout can deadlock on
    // large graphs: `dot` fills its stdout pipe and blocks, and so does our
    // `write_all` on a full stdin pipe.
    let writer = child.stdin.take().map(|mut sin| {
        let bytes = dot.as_bytes().to_vec();
        std::thread::spawn(move || sin.write_all(&bytes))
    });
    let out = child.wait_with_output()?;
    if let Some(handle) = writer {
        // Propagate any write error (ignore a panicked thread).
        if let Ok(res) = handle.join() {
            res?;
        }
    }
    if !out.status.success() {
        return Err(std::io::Error::other(
            format!("dot exited with status {:?}", out.status)));
    }
    Ok(out.stdout)
}

// ---------------------------------------------------------------------
// DOT construction
// ---------------------------------------------------------------------

struct DotBuilder {
    buf: String,
}

impl DotBuilder {
    fn new() -> Self {
        DotBuilder { buf: String::new() }
    }
    fn into_string(self) -> String { self.buf }
    fn preamble(&mut self, has_clusters: bool) {
        let _ = writeln!(self.buf, "digraph G {{");
        if has_clusters {
            // HS `setDefaultAttributesIfCluster` (Dot.hs:140-161): a richer
            // attribute block for clustered graphs.
            let _ = writeln!(self.buf, "  nodesep=0.8; ranksep=0.8;");
            let _ = writeln!(self.buf, "  sep=4;");
            let _ = writeln!(self.buf, "  splines=true;");
            let _ = writeln!(self.buf, "  overlap=false;");
            let _ = writeln!(self.buf, "  pack=true;");
            let _ = writeln!(self.buf, "  packmode=cluster;");
            let _ = writeln!(self.buf, "  concentrate=true;");
            let _ = writeln!(self.buf, "  compound=true;");
            let _ = writeln!(self.buf, "  remincross=true;");
            let _ = writeln!(self.buf, "  mclimit=10;");
            let _ = writeln!(self.buf, "  nslimit=20;");
            let _ = writeln!(self.buf, "  nslimit1=20;");
            let _ = writeln!(self.buf, "  ordering=out;");
            let _ = writeln!(self.buf, "  rankdir=TB;");
            let _ = writeln!(self.buf, "  showboxes=false;");
            let _ = writeln!(self.buf, "  clusterrank=local;");
            // HS sets the graph-level node default shape to `ellipse`; each
            // rule node overrides it with an explicit record label, so the
            // `shape=record` we keep on the rule node still wins per-node
            // (matching HS's per-node record attrs).
            let _ = writeln!(self.buf,
                "  node [fontsize=8,fontname=\"Helvetica\",width=0.3,height=0.2,margin=\"0.05,0.05\",shape=ellipse];");
            let _ = writeln!(self.buf,
                "  edge [fontsize=8,fontname=\"Helvetica\",penwidth=1.5,arrowsize=0.5,color=black,style=solid,weight=8];");
        } else {
            // HS `setDefaultAttributes` (Dot.hs:130-135). Note the node
            // `width=0.3,height=0.2` defaults HS emits; we additionally keep
            // `shape=record` because each rule node is rendered as a record
            // label (HS sets the record shape per-node via `D.record`).
            let _ = writeln!(self.buf, "  nodesep=0.3; ranksep=0.3;");
            let _ = writeln!(self.buf,
                "  node [fontsize=8,fontname=\"Helvetica\",width=0.3,height=0.2,shape=record];");
            let _ = writeln!(self.buf,
                "  edge [fontsize=8,fontname=\"Helvetica\"];");
        }
    }
    fn close(&mut self) {
        let _ = writeln!(self.buf, "}}");
    }
    fn dot_node_id(nid: &LVar) -> String {
        // Sanitise to a valid DOT identifier.
        let raw = format!("{}_{}", nid.name, nid.idx);
        raw.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
            .collect()
    }
    fn rule_node(&mut self, nid: &LVar, ru: &RuleACInst, opts: &GraphOptions,
                 manual_color: Option<&str>) {
        let id = Self::dot_node_id(nid);
        // Build prems / acts / concs rows.
        let prems = enumerate_label_row(&ru.premises, "p");
        let concs = enumerate_label_row(&ru.conclusions, "c");
        // HS `ruleLabelM`: `prettyNodeId v <-> colon <-> showDotRuleCaseName`
        // (Dot.hs:336-337). `prettyNodeId = text . show` (LTerm.hs:849), so the
        // id renders as `show v` (e.g. `#i` / `#i.2`) via `Display for LVar`.
        let header = format!("{} : {}", nid,
            escape_dot(&rule_case_name(ru)));
        // HS `ruleLabelM` filters the action facts before rendering
        // (Dot.hs:330-354): always drop the synthetic `Diff<rulename>`
        // annotation, and — only when `goShowAutoSource` is set — drop the
        // `AUTO_{IN,OUT}_{TERM,FACT}_*` auto-source labels.
        let acts: Vec<&LNFact> = ru.actions.iter()
            .filter(|fa| is_not_diff_annotation(ru, fa))
            .filter(|fa| !opts.show_auto_source || !is_auto_source(fa))
            .collect();
        let mid = if acts.is_empty() {
            header.clone()
        } else {
            let acts: Vec<String> = acts.iter()
                .map(|fa| format_fact(fa))
                .collect();
            format!("{} [{}]", header, escape_dot(&acts.join(", ")))
        };
        // Record label: `{ prems | mid | concs }`.  When a section is
        // empty we omit it to avoid a stray `|`.
        let mut sections = Vec::new();
        if !prems.is_empty() {
            sections.push(format!("{{ {} }}", prems));
        }
        sections.push(escape_dot(&mid).to_string());
        if !concs.is_empty() {
            sections.push(format!("{{ {} }}", concs));
        }
        let lbl = sections.join(" | ");
        let color = rule_fillcolor(ru, manual_color);
        let _ = writeln!(self.buf,
            "  {} [label=\"{}\",style=\"filled\",fillcolor=\"{}\"];",
            id, lbl, color);
    }
    fn action_node(&mut self, nid: &LVar, facts: &[LNFact]) {
        let id = Self::dot_node_id(nid);
        let mut s = facts.iter()
            .map(format_fact)
            .collect::<Vec<_>>()
            .join(", ");
        // HS `lblPre <-> opAction <-> text (show v)` (Dot.hs:269):
        // `opAction = operator_ "@"`, `<->` is space-joined, and `show v`
        // renders via `Display for LVar` (e.g. `#i` / `#i.2`).
        let _ = write!(s, " @ {}", nid);
        let color = if facts.iter().any(|f| matches!(f.tag, FactTag::Ku)) {
            "gray"
        } else { "darkblue" };
        let _ = writeln!(self.buf,
            "  {} [shape=ellipse,label=\"{}\",color=\"{}\"];",
            id, escape_dot(&s), color);
    }
    fn last_node(&mut self, nid: &LVar) {
        let id = Self::dot_node_id(nid);
        // HS `LastActionAtom -> mkSimpleNode (show v) []` (Dot.hs:273): the
        // label is `show v`, rendered via `Display for LVar` (`#i` / `#i.2`).
        let _ = writeln!(self.buf,
            "  {} [shape=ellipse,label=\"{}\"];",
            id, escape_dot(&nid.to_string()));
    }
    fn missing_node(&mut self, nid: &LVar, hint: &MissingHint) {
        let id = Self::dot_node_id(nid);
        // Mirror Haskell `dotNodeCompact` (Dot.hs:274-282): a
        // missing-conclusion node is a `trapezium` labelled `prettyNodeConc`,
        // a missing-premise node is an `invtrapezium` labelled `prettyNodePrem`.
        // Both labels are `parens (prettyNodeId v <> comma <-> int i)`
        // (Constraints.hs:251/255), i.e. `(<show v>, <i>)` — the conclusion /
        // premise index is part of the label, not dropped.
        let (shape, idx) = match hint {
            MissingHint::Conc(ci) => ("trapezium", ci.0),
            MissingHint::Prem(pi) => ("invtrapezium", pi.0),
        };
        let label = format!("({}, {})", nid, idx);
        let _ = writeln!(self.buf,
            "  {} [shape={},label=\"{}\"];",
            id, shape, escape_dot(&label));
    }
    fn edge(&mut self,
            node_map: &HashMap<&LVar, &RuleACInst>,
            src: &tamarin_theory::constraint::constraints::NodeConc,
            tgt: &tamarin_theory::constraint::constraints::NodePrem) {
        let src_id = Self::dot_node_id(&src.0);
        let tgt_id = Self::dot_node_id(&tgt.0);
        // Look up the target premise's fact tag so we can colour
        // the edge.
        let style = edge_style(node_map, src, tgt);
        let _ = writeln!(self.buf,
            "  {}:c{} -> {}:p{} [{}];",
            src_id, src.1.0, tgt_id, tgt.1.0, style);
    }
    fn chain_edge(&mut self,
                  src: &tamarin_theory::constraint::constraints::NodeConc,
                  tgt: &tamarin_theory::constraint::constraints::NodePrem) {
        let s = Self::dot_node_id(&src.0);
        let t = Self::dot_node_id(&tgt.0);
        let _ = writeln!(self.buf,
            "  {}:c{} -> {}:p{} [style=\"dotted\",color=\"green\"];",
            s, src.1.0, t, tgt.1.0);
    }
    /// Open a subgraph (Graphviz `subgraph cluster_<n> { ... }`).
    /// `idx` is a numeric disambiguator; `name` is shown as the label and
    /// `color` is the cluster's `roleColor` (HS `dotCluster`, Dot.hs:547-562).
    ///
    /// The attribute block mirrors HS `dotCluster`'s sequence exactly:
    /// `nodesep=0.6`, `ranksep=0.6`, `label`, `style=filled`, `color`,
    /// `penwidth=2`, `fillcolor`, `overlap=false`, `sep=4`. (The subgraph id
    /// `cluster_<n>` is the Rust convention — HS uses
    /// `createClusterNodeId roleName` — but the styling attributes are now
    /// byte-faithful.)
    fn open_subgraph(&mut self, idx: usize, name: &str, color: &str) {
        let _ = writeln!(self.buf, "  subgraph cluster_{} {{", idx);
        let _ = writeln!(self.buf, "    nodesep=\"0.6\";");
        let _ = writeln!(self.buf, "    ranksep=\"0.6\";");
        let _ = writeln!(self.buf, "    label=\"{}\";", escape_dot(name));
        let _ = writeln!(self.buf, "    style=\"filled\";");
        let _ = writeln!(self.buf, "    color=\"{}\";", color);
        let _ = writeln!(self.buf, "    penwidth=\"2\";");
        let _ = writeln!(self.buf, "    fillcolor=\"{}\";", color);
        let _ = writeln!(self.buf, "    overlap=\"false\";");
        let _ = writeln!(self.buf, "    sep=\"4\";");
    }
    fn close_subgraph(&mut self) {
        let _ = writeln!(self.buf, "  }}");
    }
    /// Emit a single merged less-edge. HS `dotLessEdge` (Dot.hs:406-410)
    /// emits the attributes `[("color",color),("style","dashed")]` — colour
    /// FIRST, then style. The colour is `allRtoColors` of the group's
    /// reasons; since at most one less-atom survives per node pair (LessAtom
    /// equality ignores the reason), the group is a singleton and the colour
    /// reduces to the single reason's `toColor` (`reason_color`).
    fn less_edge(&mut self, la: &LessAtom) {
        let s = Self::dot_node_id(&la.smaller);
        let t = Self::dot_node_id(&la.larger);
        let _ = writeln!(self.buf,
            "  {} -> {} [color=\"{}\",style=\"dashed\"];",
            s, t, reason_color(la.reason));
    }
    /// Emit a legend node listing the chosen abbreviations.
    /// Mirror of Haskell's `generateLegend` (Dot.hs:415-474) — produces a
    /// single DOT node with an HTML-table label of `name = expansion` rows.
    /// Rows are ordered by `topoSortAbbrevs` applied to a descending sort
    /// of the rendered abbreviation names, so that an abbreviation used
    /// inside another's expansion is printed first.
    fn legend(&mut self, abbrevs: &Abbreviations) {
        // sortOn (Down . render . prettyLNTerm . fst) $ M.elems abbrevs
        // M.elems iterates by key (orig term) order; sortOn is stable.
        let mut entries: Vec<(&LNTerm, &LNTerm)> = abbrevs.iter()
            .map(|(_orig, (name, exp))| (name, exp))
            .collect();
        // Descending by rendered name (stable); key cached per element.
        entries.sort_by_key(|x| std::cmp::Reverse(pretty_lnterm(x.0)));
        let order = topo_sort_abbrevs(&entries);
        // Mirror Haskell `abbrevLabel`: tableAttributes =
        //   [Border 1, CellBorder 0, CellSpacing 3, CellPadding 1].
        let mut html = String::new();
        html.push_str(
            "<<TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"3\" CELLPADDING=\"1\">");
        for &i in &order {
            let (name, exp) = entries[i];
            html.push_str("<TR>");
            html.push_str(&format!("<TD ALIGN=\"LEFT\" VALIGN=\"TOP\">{}</TD>",
                html_escape(&pretty_lnterm(name))));
            html.push_str("<TD ALIGN=\"LEFT\" VALIGN=\"TOP\">=</TD>");
            html.push_str(&format!("<TD ALIGN=\"LEFT\" VALIGN=\"TOP\">{}</TD>",
                html_escape(&pretty_lnterm(exp))));
            html.push_str("</TR>");
        }
        html.push_str("</TABLE>>");
        // Haskell emits shape "plain".
        let _ = writeln!(self.buf,
            "  legend [shape=plain,label={}];", html);
    }
}

/// Mirror Haskell `topoSortAbbrevs` (Dot.hs:459-474).
///
/// `entries` is the descending-name-sorted list of `(name, expansion)`.
/// We build a graph with an edge `v -> u` whenever `entries[v].name` is a
/// proper subterm of `entries[u].expansion` (i.e. abbreviation `v` is used
/// inside abbreviation `u`), then return vertices in topological order so
/// that used-inside abbreviations are printed first.
///
/// This reproduces `Data.Graph.graphFromEdges` + `Data.Graph.topSort`:
/// keys are `[0..]` in the given order (already sorted), so vertex `i`
/// corresponds to `entries[i]`; `topSort = reverse . postorder` of the DFS
/// forest taken over vertices `0..n-1` in order.
fn topo_sort_abbrevs(entries: &[(&LNTerm, &LNTerm)]) -> Vec<usize> {
    use tamarin_term::term::is_proper_subterm;
    let n = entries.len();
    // Adjacency: successors of v in ascending vertex order (findLegendEdges
    // iterates keyedElems in order, so target keys/vertices are ascending).
    let adj: Vec<Vec<usize>> = (0..n)
        .map(|v| {
            (0..n)
                .filter(|&u| is_proper_subterm(entries[v].0, entries[u].1))
                .collect()
        })
        .collect();
    // DFS forest over vertices 0..n-1, collecting postorder.
    let mut visited = vec![false; n];
    let mut postorder: Vec<usize> = Vec::with_capacity(n);
    // Iterative DFS that emits a vertex on exit (postorder).
    for start in 0..n {
        if visited[start] {
            continue;
        }
        // Stack of (vertex, next-successor-index).
        let mut stack: Vec<(usize, usize)> = Vec::new();
        visited[start] = true;
        stack.push((start, 0));
        while let Some(&(v, idx)) = stack.last() {
            if idx < adj[v].len() {
                let w = adj[v][idx];
                stack.last_mut().unwrap().1 += 1;
                if !visited[w] {
                    visited[w] = true;
                    stack.push((w, 0));
                }
            } else {
                postorder.push(v);
                stack.pop();
            }
        }
    }
    // topSort = reverse postorder.
    postorder.reverse();
    postorder
}

/// HTML-escape a string for use in a Graphviz HTML-like label.
fn html_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '&' => out.push_str("&amp;"),
            '"' => out.push_str("&quot;"),
            _ => out.push(c),
        }
    }
    out
}

fn enumerate_label_row(facts: &[LNFact], port_prefix: &str) -> String {
    facts.iter().enumerate()
        .map(|(i, fa)| format!("<{}{}> {}",
            port_prefix, i, escape_dot(&format_fact(fa))))
        .collect::<Vec<_>>()
        .join(" | ")
}

/// Render an `LNFact` exactly as Haskell `prettyLNFact` (Fact.hs:551), via
/// the shared faithful printer in `tamarin-theory`. This reproduces
/// `showFactTag` (the persistent `!` prefix, Fact.hs:519-523), the
/// `nestShort'` parenthesisation that always emits `name(...)` even for a
/// zero-arity fact (Class.hs:221-223 / Fact.hs:542), and the
/// `[+]/[-]/[no_precomp]` annotation block (`ppAnn`, Fact.hs:543-545). The
/// dot path reaches the same printer in HS via
/// `renderLNFact -> prettyLNFact` (Dot.hs:225-233).
fn format_fact(fa: &LNFact) -> String {
    tamarin_theory::pretty_system::pretty_fact(fa)
}

/// Mirror Haskell `ruleLabelM.isNotDiffAnnotation` (Dot.hs:341): the action
/// fact equal to the synthetic diff annotation
/// `Fact (ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0) S.empty []`
/// is dropped before rendering. `getRuleNameDiff` (Rule.hs:784-798) prefixes
/// the rule's `getRuleName` with `"Intr"`/`"Proto"` depending on the rule
/// kind. Returns `true` when the fact should be KEPT.
fn is_not_diff_annotation(ru: &RuleACInst, fa: &LNFact) -> bool {
    // `getRuleNameDiff` (Rule.hs:784-798) = `getRuleName` prefixed with
    // `"Intr"`/`"Proto"`; the synthetic fact name is `"Diff" ++` that.
    let rule_name_diff = match &ru.info {
        RuleInfo::Intr(_) => format!("Intr{}", rule_name_string(ru)),
        RuleInfo::Proto(_) => format!("Proto{}", rule_name_string(ru)),
    };
    let diff_fact_name = format!("Diff{}", rule_name_diff);
    let is_diff = matches!(&fa.tag,
        FactTag::Proto(tamarin_theory::fact::Multiplicity::Linear, n, 0)
            if *n == diff_fact_name)
        && fa.terms.is_empty();
    !is_diff
}

/// Mirror Haskell `ruleLabelM.isAutoSource`/`hasAutoLabel` (Dot.hs:343-354):
/// a fact whose `showFactTag` begins with one of the auto-source label
/// prefixes is an auto-source fact. These labels are linear proto facts, so
/// `showFactTag` reduces to the bare proto name here (no `!` prefix), which
/// `fact_tag_name` returns.
fn is_auto_source(fa: &LNFact) -> bool {
    use tamarin_theory::fact::fact_tag_name;
    let name = fact_tag_name(&fa.tag);
    name.starts_with("AUTO_IN_TERM_")
        || name.starts_with("AUTO_IN_FACT_")
        || name.starts_with("AUTO_OUT_TERM_")
        || name.starts_with("AUTO_OUT_FACT_")
}

/// Mirror Haskell's `showDotRuleCaseName` for `RuleACInst`
/// (Theory/Model/Rule.hs:1220-1222 via `prettyDotProtoRuleName`,
/// Rule.hs:1169-1185).
fn rule_case_name(ru: &RuleACInst) -> String {
    match &ru.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Stand(s) => {
                if p.attributes.is_sapic_rule {
                    if s.starts_with("new") {
                        // chr 957 (ν) : ' ' : drop 3 (trimSapicName s)
                        let trimmed = trim_sapic_name(s);
                        let dropped: String = trimmed.chars().skip(3).collect();
                        format!("\u{3bd} {}", dropped)
                    } else {
                        trim_sapic_name(s)
                    }
                } else {
                    prefix_if_reserved(s)
                }
            }
            ProtoRuleName::Fresh => "Fresh".to_string(),
        }
        RuleInfo::Intr(i) => intr_case_name(i),
    }
}

/// Mirror Haskell `trimSapicName` (Theory/Model/Rule.hs:1175-1185): strips a
/// trailing `_<digits>_<digits>` suffix from a SAPiC rule name.
fn trim_sapic_name(name: &str) -> String {
    // splitString: reverse (splitOn "_" name); if >= 3 parts, the prefix is
    // intercalate "_" (reverse (drop 2 parts)), and the last two parts are
    // parts[1] (n) and parts[0] (m).
    let parts: Vec<&str> = name.split('_').collect();
    if parts.len() >= 3 {
        let m = parts[parts.len() - 1];
        let n = parts[parts.len() - 2];
        // Haskell `all isDigit s` is True for the empty string too.
        let all_digits = |s: &str| s.chars().all(|c| c.is_ascii_digit());
        if all_digits(n) && all_digits(m) {
            return parts[..parts.len() - 2].join("_");
        }
    }
    name.to_string()
}

fn intr_case_name(i: &IntrRuleACInfo) -> String {
    // Mirror Haskell `prettyIntrRuleACInfo` (Theory/Model/Rule.hs:1225-1234).
    // Note: ConstrRule/DestrRule names already carry a leading `_` (e.g.
    // `_exp`), so the Haskell `'c' : name` yields e.g. `c_exp` (a single
    // underscore), then `prefixIfReserved` is applied.
    match i {
        IntrRuleACInfo::IRecv      => "irecv".into(),
        IntrRuleACInfo::ISend      => "isend".into(),
        IntrRuleACInfo::Coerce     => "coerce".into(),
        IntrRuleACInfo::FreshConstr=> "fresh".into(),
        IntrRuleACInfo::PubConstr  => "pub".into(),
        IntrRuleACInfo::NatConstr  => "nat".into(),
        IntrRuleACInfo::IEquality  => "iequality".into(),
        IntrRuleACInfo::ConstrRule(n) =>
            prefix_if_reserved(&format!("c{}", String::from_utf8_lossy(n))),
        IntrRuleACInfo::DestrRule(n, _, _, _) =>
            prefix_if_reserved(&format!("d{}", String::from_utf8_lossy(n))),
    }
}

/// Mirror Haskell `prefixIfReserved` (Theory/Model/Rule.hs:1154-1162):
/// prefixes with `_` if the name is reserved or already starts with `_`.
fn prefix_if_reserved(n: &str) -> String {
    use tamarin_theory::rule::reserved_rule_names;
    if reserved_rule_names().contains(n) || n.starts_with('_') {
        format!("_{}", n)
    } else {
        n.to_string()
    }
}

/// HS `ruleColor'` (Dot.hs:248-253): `rgbToHex` of the proto rule's explicit
/// `color:` attribute, if any. `None` for intruder rules / no attribute.
fn explicit_rule_color(ru: &RuleACInst) -> Option<String> {
    if let RuleInfo::Proto(p) = &ru.info {
        if let Some(rgb) = p.attributes.color {
            return Some(tamarin_utils::color::rgb_to_hex(rgb));
        }
    }
    None
}

/// Pick a rule node's fill colour with HS `dotNodeCompact`'s priority
/// (Dot.hs:248-256): `fromMaybe (maybe "white" rgbToHex color)
/// (ruleColor' <|> manualNodeColor)` — the explicit `color:` attribute wins,
/// then the cluster's `manualNodeColor`, then the colormap fallback.
fn rule_fillcolor(ru: &RuleACInst, manual_color: Option<&str>) -> String {
    explicit_rule_color(ru)
        .or_else(|| manual_color.map(|c| c.to_string()))
        .unwrap_or_else(|| rule_group_color(ru))
}

fn rule_group_color(ru: &RuleACInst) -> String {
    // APPROXIMATION (not byte-faithful): the fall-back below mirrors only the
    // GROUP PARTITION of HS `nodeColorMap`/`groupIdx` (Dot.hs:196-205), NOT its
    // colour values. HS computes a per-rule HSV palette via
    // `lightColorGroups intruderHue (map (length.snd) groups)` keyed by
    // (groupIdx, memberIdx); we substitute four fixed placeholder hexes and
    // emit "white" for the proto "otherwise" group (HS gives that group a real
    // HSV colour). A faithful port would need the whole rule set to size the
    // groups — out of scope here; only the explicit-`color` attribute above is
    // byte-exact against HS.
    match &ru.info {
        RuleInfo::Intr(i) => {
            // Mirror HS `groupIdx` (Dot.hs:196-200): group 0 (destrs) is
            // `isDestrRule`, True for both DestrRule and IEqualityRule
            // (Rule.hs:671-675); group 2 (constrs) is `isConstrRule`, True for
            // ConstrRule, Fresh/Pub/Nat constr AND CoerceRule (Rule.hs:684-691).
            if tamarin_theory::rule::is_destr_rule_info(i)
                || tamarin_theory::rule::is_iequality_rule_info(i) {
                "#c0d4ff".to_string()
            } else if tamarin_theory::rule::is_constr_rule_info(i)
                || tamarin_theory::rule::is_pub_constr_rule_info(i)
                || tamarin_theory::rule::is_nat_constr_rule_info(i)
                || tamarin_theory::rule::is_fresh_constr_rule_info(i)
                || tamarin_theory::rule::is_coerce_rule_info(i) {
                "#ffd0c0".to_string()
            } else if tamarin_theory::rule::is_isend_rule_info(i) {
                "#e0e0e0".to_string()
            } else {
                "white".to_string()
            }
        }
        RuleInfo::Proto(p) => {
            // Fresh proto-rule maps to gray (HS group 3).
            if p.name == ProtoRuleName::Fresh { "#e0e0e0".to_string() }
            else { "white".to_string() }
        }
    }
}

fn edge_style(node_map: &HashMap<&LVar, &RuleACInst>,
              src: &tamarin_theory::constraint::constraints::NodeConc,
              tgt: &tamarin_theory::constraint::constraints::NodePrem) -> String {
    // Look up tag of the source-conclusion or target-premise.
    let conc_tag = lookup_conc_tag(node_map, src);
    let prem_tag = lookup_prem_tag(node_map, tgt);
    let is_proto = |t: Option<&FactTag>| -> bool {
        matches!(t, Some(FactTag::Proto(_, _, _)))
    };
    let is_persistent = |t: Option<&FactTag>| -> bool {
        matches!(t, Some(FactTag::Proto(tamarin_theory::fact::Multiplicity::Persistent, _, _)))
    };
    let is_k = |t: Option<&FactTag>| -> bool {
        matches!(t, Some(FactTag::Ku) | Some(FactTag::Kd))
    };
    if is_proto(conc_tag.as_ref()) || is_proto(prem_tag.as_ref()) {
        let mut s = String::from("style=\"bold\",weight=10");
        if is_persistent(conc_tag.as_ref()) || is_persistent(prem_tag.as_ref()) {
            s.push_str(",color=\"gray50\"");
        }
        s
    } else if is_k(conc_tag.as_ref()) || is_k(prem_tag.as_ref()) {
        "color=\"orangered2\"".to_string()
    } else {
        "color=\"gray30\"".to_string()
    }
}

fn lookup_conc_tag(
    node_map: &HashMap<&LVar, &RuleACInst>,
    nc: &tamarin_theory::constraint::constraints::NodeConc,
) -> Option<FactTag> {
    let (nid, idx) = nc;
    let ru = node_map.get(nid)?;
    ru.conclusions.get(idx.0).map(|fa| fa.tag.clone())
}

fn lookup_prem_tag(
    node_map: &HashMap<&LVar, &RuleACInst>,
    np: &tamarin_theory::constraint::constraints::NodePrem,
) -> Option<FactTag> {
    let (nid, idx) = np;
    let ru = node_map.get(nid)?;
    ru.premises.get(idx.0).map(|fa| fa.tag.clone())
}

fn reason_color(r: Reason) -> &'static str {
    match r {
        Reason::Adversary => "red",
        Reason::Formula => "black",
        Reason::Fresh => "blue3",
        Reason::InjectiveFacts => "purple",
        Reason::NormalForm => "darkorange3",
    }
}

/// Port of Haskell `roleColor` (Dot.hs:534-544): a deterministic per-role
/// `#RRGGBBAA` colour. `simpleHash name = foldl (\acc c -> acc*31 + ord c) 7`
/// over the role's base name (Haskell `Int`, i.e. 64-bit two's-complement
/// wrapping), `generateValue = (hash `mod` 360) / 360` (Haskell `mod` is
/// non-negative for a positive divisor — `rem_euclid` here), then
/// `hsvToRGB (HSV (v*360) 0.75 0.85)` with each channel `floor(f*255)` and a
/// fixed alpha `floor(255*0.3) = 76`. Hex digits are UPPERCASE (`%02X`), and
/// the channel scale is `*255` (not `*256` as in `rgb_to_hex`), so this does
/// not reuse `rgb_to_hex`.
fn role_color(name: &str) -> String {
    // simpleHash: `Int` arithmetic, wraps on overflow.
    let hash: i64 = name.chars().fold(7i64, |acc, c| {
        acc.wrapping_mul(31).wrapping_add(c as i64)
    });
    let v = (hash.rem_euclid(360)) as f64 / 360.0;
    let rgb = tamarin_utils::color::hsv_to_rgb(
        tamarin_utils::color::Hsv::new(v * 360.0, 0.75, 0.85));
    let chan = |f: f64| -> i64 { (f * 255.0).floor() as i64 };
    let alpha: i64 = (255.0 * 0.3_f64).floor() as i64; // = 76
    format!("#{:02X}{:02X}{:02X}{:02X}",
        chan(rgb.r), chan(rgb.g), chan(rgb.b), alpha)
}

fn escape_dot(s: &str) -> String {
    // Escape `"`, `\`, `{`, `}`, `|`, `<`, `>` for the Graphviz record
    // string syntax.
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"'  => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '{'  => out.push_str("\\{"),
            '}'  => out.push_str("\\}"),
            '|'  => out.push_str("\\|"),
            '<'  => out.push_str("\\<"),
            '>'  => out.push_str("\\>"),
            '\n' => out.push_str("\\n"),
            _    => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_theory::constraint::system::System;

    #[test]
    fn dot_for_empty_system() {
        let sys = System::empty();
        let s = system_to_dot(&sys);
        assert!(s.starts_with("digraph G {"));
        assert!(s.contains("nodesep"));
        assert!(s.trim_end().ends_with('}'));
    }

    #[test]
    fn dot_for_node_with_rule() {
        use tamarin_theory::fact::{out_fact, fresh_fact};
        use tamarin_theory::rule::{
            ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, RuleInfo, Rule,
        };
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let mut sys = System::empty();
        let kvar = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let info: RuleInfo<ProtoRuleACInstInfo,
            tamarin_theory::rule::IntrRuleACInfo> =
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Setup".into()),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            });
        let rule = Rule::new(info,
            vec![fresh_fact(kvar.clone())],
            vec![out_fact(kvar.clone())],
            Vec::new());
        let nid = LVar::new("i", LSort::Node, 0);
        sys.add_node(nid, rule);
        let s = system_to_dot(&sys);
        assert!(s.contains("Setup"));
        assert!(s.contains("Fr"));
        assert!(s.contains("Out"));
    }

    #[test]
    fn dot_uses_pretty_printing_for_terms() {
        // Two pub var literals shoult render as $a, $b not as cryptic
        // M:0 placeholders.
        use tamarin_theory::fact::{out_fact, fresh_fact};
        use tamarin_theory::rule::{
            ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, RuleInfo, Rule,
        };
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let mut sys = System::empty();
        let a = Term::Lit(Lit::Var(LVar::new("a", LSort::Pub, 0)));
        let info: RuleInfo<ProtoRuleACInstInfo,
            tamarin_theory::rule::IntrRuleACInfo> =
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Setup".into()),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            });
        let rule = Rule::new(info,
            vec![fresh_fact(a.clone())],
            vec![out_fact(a.clone())],
            Vec::new());
        let nid = LVar::new("i", LSort::Node, 0);
        sys.add_node(nid, rule);
        let s = system_to_dot(&sys);
        assert!(s.contains("$a"), "expected $a in DOT output: {}", s);
    }

    #[test]
    fn dot_emits_cluster_for_role() {
        use tamarin_theory::fact::out_fact;
        use tamarin_theory::rule::{
            ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, RuleInfo, Rule,
        };
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let mut sys = System::empty();
        let kvar = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let mk = |name: &str, role: Option<&str>| -> RuleACInst {
            let attrs = RuleAttributes {
                role: role.map(|r| r.to_string()),
                ..Default::default()
            };
            Rule::new(
                RuleInfo::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(name.to_string()),
                    attributes: attrs,
                    loop_breakers: Vec::new(),
                }),
                Vec::new(),
                vec![out_fact(kvar.clone())],
                // Action to prevent compression from hiding it.
                vec![out_fact(kvar.clone())],
            )
        };
        sys.add_node(LVar::new("a", LSort::Node, 1), mk("InitA", Some("Alice")));
        sys.add_node(LVar::new("b", LSort::Node, 2), mk("InitB", Some("Bob")));
        let s = system_to_dot(&sys);
        // Each role yields a cluster subgraph.
        assert!(s.contains("subgraph cluster_"), "missing cluster: {}", s);
        assert!(s.contains("Alice"), "missing Alice cluster label: {}", s);
        assert!(s.contains("Bob"), "missing Bob cluster label: {}", s);
    }

    #[test]
    fn dot_with_sl0_does_not_collapse_less() {
        // Construct a system with a transitive less-chain; verify SL2/SL3
        // drops the redundant edge and SL0 keeps it.
        use tamarin_theory::constraint::constraints::LessAtom;
        let mut sys = System::empty();
        let a = LVar::new("a", tamarin_term::lterm::LSort::Node, 0);
        let b = LVar::new("b", tamarin_term::lterm::LSort::Node, 0);
        let c = LVar::new("c", tamarin_term::lterm::LSort::Node, 0);
        sys.less_atoms.push(LessAtom::new(a.clone(), b.clone(), Reason::Fresh));
        sys.less_atoms.push(LessAtom::new(b.clone(), c.clone(), Reason::Fresh));
        sys.less_atoms.push(LessAtom::new(a.clone(), c.clone(), Reason::Fresh));
        let opts_sl0 = crate::graph::GraphOptions {
            simplification_level: crate::graph::SimplificationLevel::SL0,
            compress: false,
            ..crate::graph::GraphOptions::default()
        };
        let s0 = system_to_dot_with(&sys, &opts_sl0);
        // Count dashed less-edges by `style=\"dashed\"` occurrences.
        let dashed_sl0 = s0.matches("style=\"dashed\"").count();
        let opts_sl3 = crate::graph::GraphOptions {
            simplification_level: crate::graph::SimplificationLevel::SL3,
            compress: false,
            ..crate::graph::GraphOptions::default()
        };
        let s3 = system_to_dot_with(&sys, &opts_sl3);
        let dashed_sl3 = s3.matches("style=\"dashed\"").count();
        assert!(dashed_sl3 < dashed_sl0,
            "SL3 should drop the redundant transitive edge: SL0={} SL3={}",
            dashed_sl0, dashed_sl3);
    }

    #[test]
    fn dot_query_params_select_simplification() {
        // Smoke test for graph_options_from_query, matching HS `getOptions`
        // (Handler.hs): the `simplification` param reads `SL0..SL3` via the
        // derived `Read`, and `uncompress` presence turns compression off.
        let opts = crate::graph::graph_options_from_query(
            "simplification=SL3&uncompress=");
        assert_eq!(opts.simplification_level,
            crate::graph::SimplificationLevel::SL3);
        assert!(!opts.compress);
    }

    #[test]
    fn dot_with_cluster_passes_graphviz_lint() {
        // Render a small system with a cluster and (if `dot` is on
        // PATH) verify the output parses without errors.
        use tamarin_theory::fact::out_fact;
        use tamarin_theory::rule::{
            ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, RuleInfo, Rule,
        };
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let mut sys = System::empty();
        let kvar = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let mk = |name: &str, role: Option<&str>| -> RuleACInst {
            let attrs = RuleAttributes {
                role: role.map(|r| r.to_string()),
                ..Default::default()
            };
            Rule::new(
                RuleInfo::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(name.to_string()),
                    attributes: attrs,
                    loop_breakers: Vec::new(),
                }),
                Vec::new(),
                vec![out_fact(kvar.clone())],
                vec![out_fact(kvar.clone())],
            )
        };
        sys.add_node(LVar::new("a", LSort::Node, 1), mk("InitA", Some("Alice")));
        sys.add_node(LVar::new("b", LSort::Node, 2), mk("InitB", Some("Bob")));
        let s = system_to_dot(&sys);
        // Try piping through `dot` if it's available; otherwise skip.
        use std::io::Write;
        use std::process::{Command, Stdio};
        let child = Command::new("dot")
            .args(["-Tplain", "/dev/null"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn();
        let Ok(mut child) = child else { return; };
        if let Some(mut sin) = child.stdin.take() {
            let _ = sin.write_all(s.as_bytes());
        }
        let out = child.wait_with_output().expect("dot wait");
        // If dot complains, the stderr would be non-empty.
        if !out.status.success() {
            panic!("graphviz `dot` rejected our output:\nstderr=\n{}\nDOT was:\n{}",
                String::from_utf8_lossy(&out.stderr), s);
        }
    }

    #[test]
    fn dot_emits_legend_when_abbreviating_long_terms() {
        // Build a System whose nodes carry a long, frequently-repeated
        // compound term -- the abbreviation algorithm should emit a legend.
        use tamarin_theory::fact::{Fact, FactTag};
        use tamarin_theory::rule::{
            ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, RuleInfo, Rule,
        };
        use tamarin_term::function_symbols::{NoEqSym, Privacy, Constructability};
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::{f_app_no_eq, Term};
        use tamarin_term::vterm::Lit;
        let mut sys = System::empty();
        let a = Term::Lit(Lit::Var(LVar::new("argument", LSort::Msg, 0)));
        let b = Term::Lit(Lit::Var(LVar::new("payload", LSort::Msg, 0)));
        let k = Term::Lit(Lit::Var(LVar::new("session_key", LSort::Msg, 0)));
        let senc = NoEqSym::new(b"senc".to_vec(), 2,
            Privacy::Public, Constructability::Constructor);
        // A long-ish term to abbreviate.
        let big = f_app_no_eq(senc.clone(),
            vec![f_app_no_eq(senc, vec![a, b]), k]);
        let mk = |name: &str| -> RuleACInst {
            Rule::new(
                RuleInfo::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(name.to_string()),
                    attributes: RuleAttributes::empty(),
                    loop_breakers: Vec::new(),
                }),
                Vec::new(),
                vec![Fact::new(FactTag::Out, vec![big.clone()])],
                vec![Fact::new(FactTag::Out, vec![big.clone()])],
            )
        };
        sys.add_node(LVar::new("a", LSort::Node, 1), mk("R1"));
        sys.add_node(LVar::new("b", LSort::Node, 2), mk("R2"));
        sys.add_node(LVar::new("c", LSort::Node, 3), mk("R3"));
        let s = system_to_dot(&sys);
        // The legend is emitted as a `plain`-shaped node with a TABLE
        // label (Haskell `generateLegend` emits no heading row).
        assert!(s.contains("legend ["), "no legend node: {}", s);
        assert!(s.contains("<TABLE"), "no abbreviations table: {}", s);
    }

    // Build a simple proto rule node with the given premises/actions/concs.
    #[cfg(test)]
    fn proto_node(name: &str, prems: Vec<LNFact>, acts: Vec<LNFact>,
                  concs: Vec<LNFact>) -> RuleACInst {
        use tamarin_theory::rule::{
            ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, Rule,
        };
        Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand(name.to_string()),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            prems, concs, acts,
        )
    }

    #[test]
    fn dot_persistent_fact_keeps_bang_prefix_and_zero_arity_parens() {
        // HS `prettyLNFact`: a persistent proto fact gets the `!` prefix
        // (showFactTag, Fact.hs:519-523), and a zero-arity fact still renders
        // `Name()` (nestShort', Class.hs:221-223 / Fact.hs:542).
        //
        // Authenticated against the repo's HS prover (v1.13.0) on a minimal
        // theory: `--prove` shows `[ Fr( ~k ) ] --> [ !Reg( ~k ), Started( ) ]`
        // — i.e. the `!` prefix on `!Reg` and the empty parens on `Started`.
        use tamarin_theory::fact::{fresh_fact, proto_fact, Multiplicity};
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let mut sys = System::empty();
        let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let reg = proto_fact(Multiplicity::Persistent, "Reg", vec![k.clone()]);
        let started = proto_fact(Multiplicity::Linear, "Started", vec![]);
        let ru = proto_node("Setup", vec![fresh_fact(k)],
            vec![started], vec![reg]);
        sys.add_node(LVar::new("i", LSort::Node, 0), ru);
        // Disable compression so the action node / facts are not collapsed.
        let opts = GraphOptions { compress: false, abbreviate: false,
            ..GraphOptions::default() };
        let s = system_to_dot_with(&sys, &opts);
        assert!(s.contains("!Reg("), "persistent `!` prefix missing: {}", s);
        assert!(s.contains("Started()"),
            "zero-arity fact should render `Started()`: {}", s);
    }

    #[test]
    fn dot_node_id_uses_show_lvar_format() {
        // HS `prettyNodeId = text . show`: a node id renders `#i` when idx==0
        // and `#i.2` when idx==2 (`instance Show LVar`, LTerm.hs:525-532;
        // sortPrefix LSortNode = "#", LTerm.hs:194). The rule-node header is
        // `prettyNodeId v <-> colon <-> showDotRuleCaseName` (Dot.hs:336).
        use tamarin_theory::fact::out_fact;
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let opts = GraphOptions { compress: false, abbreviate: false,
            ..GraphOptions::default() };
        let mk = || {
            let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
            proto_node("R", vec![], vec![out_fact(k.clone())],
                vec![out_fact(k)])
        };
        let mut sys0 = System::empty();
        sys0.add_node(LVar::new("i", LSort::Node, 0), mk());
        let s0 = system_to_dot_with(&sys0, &opts);
        assert!(s0.contains("#i : R"), "idx==0 should render `#i`: {}", s0);
        assert!(!s0.contains("#i0"), "idx==0 must not append the index: {}", s0);

        let mut sys2 = System::empty();
        sys2.add_node(LVar::new("i", LSort::Node, 2), mk());
        let s2 = system_to_dot_with(&sys2, &opts);
        assert!(s2.contains("#i.2 : R"), "idx==2 should render `#i.2`: {}", s2);
    }

    #[test]
    fn dot_drops_diff_annotation_action_fact() {
        // HS `ruleLabelM.isNotDiffAnnotation` (Dot.hs:341) drops the synthetic
        // `Diff<getRuleNameDiff ru>` linear proto fact from the action row.
        // For a standard proto rule `R`, getRuleNameDiff = "ProtoR", so the
        // dropped fact is `ProtoFact Linear "DiffProtoR" 0`.
        use tamarin_theory::fact::{out_fact, proto_fact, Multiplicity};
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let mut sys = System::empty();
        let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let diff = proto_fact(Multiplicity::Linear, "DiffProtoR", vec![]);
        let real = proto_fact(Multiplicity::Linear, "Visible", vec![]);
        let ru = proto_node("R", vec![], vec![diff, real],
            vec![out_fact(k)]);
        sys.add_node(LVar::new("i", LSort::Node, 0), ru);
        let opts = GraphOptions { compress: false, abbreviate: false,
            ..GraphOptions::default() };
        let s = system_to_dot_with(&sys, &opts);
        assert!(s.contains("Visible()"),
            "non-diff action fact must remain: {}", s);
        assert!(!s.contains("DiffProtoR"),
            "Diff annotation fact must be filtered out: {}", s);
    }

    #[test]
    fn dot_explicit_rule_color_attribute_sets_fillcolor() {
        // HS `dotNodeCompact` prefers `ruleColor'` (the explicit `color:`
        // attribute) over the colormap (Dot.hs:248-256). The hex is
        // `rgbToHex` of the attribute's Rgb.
        use tamarin_theory::fact::out_fact;
        use tamarin_theory::rule::{
            ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, Rule,
        };
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        use tamarin_utils::color::Rgb;
        let mut sys = System::empty();
        let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let rgb = Rgb::new(1.0, 0.5, 0.0);
        let expected = tamarin_utils::color::rgb_to_hex(rgb); // "#ff7f00"
        let attrs = RuleAttributes { color: Some(rgb), ..Default::default() };
        let ru = Rule::new(
            RuleInfo::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Coloured".into()),
                attributes: attrs,
                loop_breakers: Vec::new(),
            }),
            Vec::new(), vec![out_fact(k.clone())], vec![out_fact(k)]);
        sys.add_node(LVar::new("i", LSort::Node, 0), ru);
        let opts = GraphOptions { compress: false, abbreviate: false,
            ..GraphOptions::default() };
        let s = system_to_dot_with(&sys, &opts);
        assert!(s.contains(&format!("fillcolor=\"{}\"", expected)),
            "explicit rule colour {} must be used as fillcolor: {}",
            expected, s);
    }

    #[test]
    fn dot_no_cluster_preamble_sets_node_size_and_less_edge_color_first() {
        // No-cluster preamble mirrors HS setDefaultAttributes (Dot.hs:130-135)
        // — including `width=0.3,height=0.2` on the node defaults. The less
        // edge emits `color` before `style` (HS dotLessEdge, Dot.hs:410).
        use tamarin_theory::constraint::constraints::LessAtom;
        use tamarin_term::lterm::{LSort, LVar};
        let mut sys = System::empty();
        let a = LVar::new("a", LSort::Node, 0);
        let b = LVar::new("b", LSort::Node, 0);
        sys.less_atoms.push(LessAtom::new(a, b, Reason::Fresh));
        let opts = GraphOptions { compress: false, abbreviate: false,
            simplification_level: crate::graph::SimplificationLevel::SL0,
            ..GraphOptions::default() };
        let s = system_to_dot_with(&sys, &opts);
        assert!(s.contains("width=0.3,height=0.2"),
            "no-cluster preamble must set node width/height: {}", s);
        // `Reason::Fresh` -> "blue3"; color must precede style.
        assert!(s.contains("[color=\"blue3\",style=\"dashed\"]"),
            "less edge must emit color before style: {}", s);
    }

    #[test]
    fn dot_cluster_preamble_uses_cluster_attributes() {
        // When clusters exist HS switches to setDefaultAttributesIfCluster
        // (Dot.hs:140-161), which sets `packmode`/`pack`/etc.
        use tamarin_theory::fact::out_fact;
        use tamarin_theory::rule::{
            ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, Rule,
        };
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        let mut sys = System::empty();
        let k = Term::Lit(Lit::Var(LVar::new("k", LSort::Fresh, 0)));
        let mk = |name: &str, role: &str| -> RuleACInst {
            let attrs = RuleAttributes { role: Some(role.to_string()),
                ..Default::default() };
            Rule::new(
                RuleInfo::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(name.to_string()),
                    attributes: attrs,
                    loop_breakers: Vec::new(),
                }),
                Vec::new(), vec![out_fact(k.clone())], vec![out_fact(k.clone())])
        };
        sys.add_node(LVar::new("a", LSort::Node, 1), mk("InitA", "Alice"));
        sys.add_node(LVar::new("b", LSort::Node, 2), mk("InitB", "Bob"));
        let s = system_to_dot(&sys);
        assert!(s.contains("packmode=cluster"),
            "cluster preamble must set packmode: {}", s);
        // Cluster subgraph styling: filled with the roleColor.
        assert!(s.contains("style=\"filled\";"),
            "cluster must be style=filled: {}", s);
    }
}
