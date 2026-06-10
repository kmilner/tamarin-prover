//! Port of Haskell's `Theory.Constraint.System.Dot` +
//! `Theory.Constraint.System.Graph.*` — convert a `System` into a
//! Graphviz DOT representation suitable for `dot -Tsvg`.
//!
//! This is a deliberately conservative subset of the Haskell pipeline:
//! we render the same kinds of nodes / edges / clusters, but using
//! plain DOT records (no HTML tables for the legend, no clustering by
//! similar-name) so the result is a single self-contained DOT
//! document. The Tamarin frontend's `intdot-staticgraph.es.js` /
//! `intdot-dynamicgraph.es.js` are forgiving about the exact DOT
//! syntax — they parse the standard Graphviz attributes we emit.
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

use std::fmt::Write as _;

use tamarin_theory::constraint::constraints::{Edge, LessAtom, Reason};
use tamarin_theory::constraint::system::System;
use tamarin_theory::fact::{fact_tag_name, FactTag, LNFact};
use tamarin_theory::rule::{
    IntrRuleACInfo, ProtoRuleName, RuleACInst, RuleInfo,
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
    compute_basic_graph_repr, GEdge, GNode, NodeType,
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
    g.preamble();
    let abbrev_lookup = |t: &LNTerm| -> Option<LNTerm> {
        abbrevs.get(t).map(|(a, _)| a.clone())
    };
    // 4a. Clusters as subgraphs.
    for (i, cluster) in repr.clusters.iter().enumerate() {
        g.open_subgraph(i, &cluster.name);
        for node in &cluster.nodes {
            emit_node(&mut g, node, &working, &abbrev_lookup);
        }
        for edge in &cluster.edges {
            emit_edge(&mut g, edge, &working);
        }
        g.close_subgraph();
    }
    // 4b. Top-level nodes / edges.
    for node in &repr.nodes {
        emit_node(&mut g, node, &working, &abbrev_lookup);
    }
    for edge in &repr.edges {
        emit_edge(&mut g, edge, &working);
    }
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
    sys: &System,
    abbrev: &dyn Fn(&LNTerm) -> Option<LNTerm>,
) {
    let _ = sys;
    match &node.ty {
        NodeType::System(ru) => {
            let ru_abbreviated = abbreviate_rule(ru, abbrev);
            g.rule_node(&node.id, &ru_abbreviated);
        }
        NodeType::UnsolvedAction(facts) => {
            let new_facts: Vec<LNFact> = facts.iter()
                .map(|fa| apply_abbreviations_fact(abbrev, fa))
                .collect();
            g.action_node(&node.id, &new_facts);
        }
        NodeType::LastAction => g.last_node(&node.id),
        NodeType::Missing(_hint) => g.missing_node(&node.id),
    }
}

fn emit_edge(g: &mut DotBuilder, edge: &GEdge, sys: &System) {
    match edge {
        GEdge::System(src, tgt) => {
            let e = Edge { src: src.clone(), tgt: tgt.clone() };
            g.edge(sys, &e);
        }
        GEdge::Less(la) => g.less_edge(la),
        GEdge::UnsolvedChain(src, tgt) => g.chain_edge(src, tgt),
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
/// through `/usr/bin/dot -Tsvg` (or whatever's on `$PATH`).  Returns
/// the SVG bytes on success.  When `dot` is missing or fails, returns
/// the DOT source instead (the frontend's `intdot-staticgraph` can
/// render DOT client-side via viz.js, so this stays a useful response).
pub fn render_svg_or_dot(sys: &System) -> RenderResult {
    render_svg_or_dot_with(sys, &GraphOptions::default())
}

/// As `render_svg_or_dot`, but using an explicit set of graph options.
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
    if let Some(mut sin) = child.stdin.take() {
        sin.write_all(dot.as_bytes())?;
    }
    let out = child.wait_with_output()?;
    if !out.status.success() {
        return Err(std::io::Error::new(
            std::io::ErrorKind::Other,
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
    fn preamble(&mut self) {
        let _ = writeln!(self.buf, "digraph G {{");
        let _ = writeln!(self.buf, "  nodesep=0.3; ranksep=0.3;");
        let _ = writeln!(self.buf,
            "  node [fontsize=8,fontname=\"Helvetica\",shape=record];");
        let _ = writeln!(self.buf,
            "  edge [fontsize=8,fontname=\"Helvetica\"];");
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
    fn rule_node(&mut self, nid: &LVar, ru: &RuleACInst) {
        let id = Self::dot_node_id(nid);
        // Build prems / acts / concs rows.
        let prems = enumerate_label_row(&ru.premises, "p");
        let concs = enumerate_label_row(&ru.conclusions, "c");
        let header = format!("#{}{} : {}", nid.name, nid.idx,
            escape_dot(&rule_case_name(ru)));
        let mid = if ru.actions.is_empty() {
            header.clone()
        } else {
            let acts: Vec<String> = ru.actions.iter()
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
        sections.push(format!("{}", escape_dot(&mid)));
        if !concs.is_empty() {
            sections.push(format!("{{ {} }}", concs));
        }
        let lbl = sections.join(" | ");
        let color = rule_fillcolor(ru);
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
        let _ = write!(s, " @ #{}{}", nid.name, nid.idx);
        let color = if facts.iter().any(|f| matches!(f.tag, FactTag::Ku)) {
            "gray"
        } else { "darkblue" };
        let _ = writeln!(self.buf,
            "  {} [shape=ellipse,label=\"{}\",color=\"{}\"];",
            id, escape_dot(&s), color);
    }
    fn last_node(&mut self, nid: &LVar) {
        let id = Self::dot_node_id(nid);
        let _ = writeln!(self.buf,
            "  {} [shape=ellipse,label=\"#{}{}\"];",
            id, nid.name, nid.idx);
    }
    fn missing_node(&mut self, nid: &LVar) {
        let id = Self::dot_node_id(nid);
        let _ = writeln!(self.buf,
            "  {} [shape=invtrapezium,label=\"?{}{}\"];",
            id, nid.name, nid.idx);
    }
    fn edge(&mut self, sys: &System, e: &Edge) {
        let src_id = Self::dot_node_id(&e.src.0);
        let tgt_id = Self::dot_node_id(&e.tgt.0);
        // Look up the target premise's fact tag so we can colour
        // the edge.
        let style = edge_style(sys, e);
        let _ = writeln!(self.buf,
            "  {}:c{} -> {}:p{} [{}];",
            src_id, e.src.1.0, tgt_id, e.tgt.1.0, style);
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
    /// `idx` is a numeric disambiguator; `name` is shown as the label.
    fn open_subgraph(&mut self, idx: usize, name: &str) {
        let _ = writeln!(self.buf, "  subgraph cluster_{} {{", idx);
        let _ = writeln!(self.buf, "    label=\"{}\";", escape_dot(name));
        let _ = writeln!(self.buf, "    style=\"rounded,dashed\";");
        let _ = writeln!(self.buf, "    color=\"gray70\";");
    }
    fn close_subgraph(&mut self) {
        let _ = writeln!(self.buf, "  }}");
    }
    /// Emit a single less-edge.  Used by the GraphRepr path where
    /// less-atoms have already been individually filtered.
    fn less_edge(&mut self, la: &LessAtom) {
        let s = Self::dot_node_id(&la.smaller);
        let t = Self::dot_node_id(&la.larger);
        let _ = writeln!(self.buf,
            "  {} -> {} [style=\"dashed\",color=\"{}\"];",
            s, t, reason_color(la.reason));
    }
    /// Emit a legend node listing the chosen abbreviations.
    /// Mirror of Haskell's `generateLegend` — produces a single DOT
    /// node with an HTML-table label of `t_i = ...` rows.
    fn legend(&mut self, abbrevs: &Abbreviations) {
        // Stable ordering by abbreviation name.
        let mut entries: Vec<(&LNTerm, &LNTerm, &LNTerm)> = abbrevs.iter()
            .map(|(orig, (name, exp))| (orig, name, exp))
            .collect();
        entries.sort_by_key(|(_, name, _)| pretty_lnterm(*name));
        let mut html = String::new();
        html.push_str("<<TABLE BORDER=\"0\" CELLBORDER=\"0\" CELLSPACING=\"0\">");
        html.push_str("<TR><TD COLSPAN=\"3\"><B>Abbreviations</B></TD></TR>");
        for (_orig, name, exp) in entries {
            html.push_str("<TR>");
            html.push_str(&format!("<TD ALIGN=\"LEFT\">{}</TD>",
                html_escape(&pretty_lnterm(name))));
            html.push_str("<TD ALIGN=\"CENTER\"> = </TD>");
            html.push_str(&format!("<TD ALIGN=\"LEFT\">{}</TD>",
                html_escape(&pretty_lnterm(exp))));
            html.push_str("</TR>");
        }
        html.push_str("</TABLE>>");
        let _ = writeln!(self.buf,
            "  legend [shape=plaintext,label={}];", html);
    }
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

fn format_fact(fa: &LNFact) -> String {
    let tag = match &fa.tag {
        FactTag::Proto(_, n, _) => n.clone(),
        _ => fact_tag_name(&fa.tag),
    };
    if fa.terms.is_empty() {
        tag
    } else {
        let args: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
        format!("{}({})", tag, args.join(", "))
    }
}

/// Mirror Haskell's `showDotRuleCaseName` for `RuleACInst`.
fn rule_case_name(ru: &RuleACInst) -> String {
    match &ru.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Stand(s) => s.clone(),
            ProtoRuleName::Fresh => "Fresh".to_string(),
        }
        RuleInfo::Intr(i) => intr_case_name(i),
    }
}

fn intr_case_name(i: &IntrRuleACInfo) -> String {
    match i {
        IntrRuleACInfo::IRecv      => "irecv".into(),
        IntrRuleACInfo::ISend      => "isend".into(),
        IntrRuleACInfo::Coerce     => "coerce".into(),
        IntrRuleACInfo::FreshConstr=> "fresh".into(),
        IntrRuleACInfo::PubConstr  => "pub".into(),
        IntrRuleACInfo::NatConstr  => "nat".into(),
        IntrRuleACInfo::IEquality  => "iequality".into(),
        IntrRuleACInfo::ConstrRule(n) =>
            format!("c_{}", String::from_utf8_lossy(n)),
        IntrRuleACInfo::DestrRule(n, _, _, _) =>
            format!("d_{}", String::from_utf8_lossy(n)),
    }
}

fn rule_fillcolor(ru: &RuleACInst) -> &'static str {
    // Mirrors Haskell `nodeColorMap`'s `groupIdx` colour-class
    // partitioning in `Theory/Constraint/System/Dot.hs:196-205`:
    //   destrs       → light blue
    //   constrs      → light red/pink
    //   fresh/isend  → light gray
    //   proto rules  → white
    match &ru.info {
        RuleInfo::Intr(i) => {
            if tamarin_theory::rule::is_destr_rule_info(i) {
                "#c0d4ff"
            } else if tamarin_theory::rule::is_constr_rule_info(i)
                || tamarin_theory::rule::is_pub_constr_rule_info(i)
                || tamarin_theory::rule::is_nat_constr_rule_info(i)
                || tamarin_theory::rule::is_fresh_constr_rule_info(i) {
                "#ffd0c0"
            } else if tamarin_theory::rule::is_isend_rule_info(i) {
                "#e0e0e0"
            } else {
                "white"
            }
        }
        RuleInfo::Proto(p) => {
            // Fresh proto-rule maps to gray.
            if p.name == ProtoRuleName::Fresh { "#e0e0e0" }
            else { "white" }
        }
    }
}

fn edge_style(sys: &System, e: &Edge) -> String {
    // Look up tag of the source-conclusion or target-premise.
    let conc_tag = lookup_conc_tag(sys, &e.src);
    let prem_tag = lookup_prem_tag(sys, &e.tgt);
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
    sys: &System,
    nc: &tamarin_theory::constraint::constraints::NodeConc,
) -> Option<FactTag> {
    let (nid, idx) = nc;
    let ru = sys.nodes.iter().find(|(id, _)| id == nid)?;
    ru.1.conclusions.get(idx.0).map(|fa| fa.tag.clone())
}

fn lookup_prem_tag(
    sys: &System,
    np: &tamarin_theory::constraint::constraints::NodePrem,
) -> Option<FactTag> {
    let (nid, idx) = np;
    let ru = sys.nodes.iter().find(|(id, _)| id == nid)?;
    ru.1.premises.get(idx.0).map(|fa| fa.tag.clone())
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
        // Smoke test for graph_options_from_query.
        let opts = crate::graph::graph_options_from_query("simp=3&compress=0");
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
        // The legend is emitted as a plaintext shape with TABLE label.
        assert!(s.contains("legend ["), "no legend node: {}", s);
        assert!(s.contains("Abbreviations"), "no abbreviations heading: {}", s);
    }
}
