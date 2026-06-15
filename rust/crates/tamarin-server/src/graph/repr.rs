//! Port of `Theory.Constraint.System.Graph.GraphRepr` —
//! intermediate representation of a `System` as nodes/edges/clusters
//! that can be rendered to DOT/JSON.
//!
//! See `lib/theory/src/Theory/Constraint/System/Graph/GraphRepr.hs`.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_theory::constraint::constraints::{Edge as SysEdge, LessAtom, NodeId, NodePrem, NodeConc};
use tamarin_theory::fact::LNFact;
use tamarin_theory::rule::{ConcIdx, PremIdx, ProtoRuleName, RuleACInst, RuleInfo};

/// Mirrors Haskell `NodeType` from `GraphRepr.hs:58-63`.
#[derive(Debug, Clone, PartialEq)]
pub enum NodeType {
    /// Node corresponding to a `RuleACInst` from `sNodes`.
    System(RuleACInst),
    /// Unsolved adversary-knowledge action (KU goals at fresh ids).
    UnsolvedAction(Vec<LNFact>),
    /// Last-action atom (induction).
    LastAction,
    /// Referenced by an edge but absent from `sNodes`.
    Missing(MissingHint),
}

/// Mirror of `Either ConcIdx PremIdx` in Haskell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MissingHint {
    Conc(ConcIdx),
    Prem(PremIdx),
}

/// Mirror of `Node` from `GraphRepr.hs:51-55`.
#[derive(Debug, Clone, PartialEq)]
pub struct GNode {
    pub id: NodeId,
    pub ty: NodeType,
}

/// Mirror of `Edge` from `GraphRepr.hs:67-71`.
#[derive(Debug, Clone, PartialEq)]
pub enum GEdge {
    System(NodeConc, NodePrem),
    Less(LessAtom),
    UnsolvedChain(NodeConc, NodePrem),
}

/// Mirror of `Cluster` from `GraphRepr.hs:74-79`.
#[derive(Debug, Clone, PartialEq)]
pub struct Cluster {
    pub name: String,
    pub nodes: Vec<GNode>,
    pub edges: Vec<GEdge>,
}

/// Mirror of `GraphRepr` from `GraphRepr.hs:82-87`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct GraphRepr {
    pub clusters: Vec<Cluster>,
    pub nodes: Vec<GNode>,
    pub edges: Vec<GEdge>,
}

impl GraphRepr {
    pub fn new() -> Self { GraphRepr::default() }
}

// ---------------------------------------------------------------------
// Cluster construction
// ---------------------------------------------------------------------

/// Return the `role` attribute of a `RuleACInst`, if any.
/// Mirror of `extractRole` from `GraphRepr.hs:136-137`.
pub fn extract_role(ru: &RuleACInst) -> Option<&str> {
    match &ru.info {
        RuleInfo::Proto(p) => p.attributes.role.as_deref(),
        _ => None,
    }
}

/// Return a node's role, if it's a `SystemNode` with a `role`
/// attribute.  Mirror of `getNodeRole`.
pub fn node_role(n: &GNode) -> Option<&str> {
    match &n.ty {
        NodeType::System(ru) => extract_role(ru),
        _ => None,
    }
}

/// Group nodes by role.  Mirror of `groupNodesByRole`.
pub fn group_nodes_by_role<'a>(
    nodes: &'a [GNode],
) -> BTreeMap<String, Vec<&'a GNode>> {
    let mut by_role: BTreeMap<String, Vec<&'a GNode>> = BTreeMap::new();
    for n in nodes {
        if let Some(r) = node_role(n) {
            by_role.entry(r.to_string()).or_default().push(n);
        }
    }
    by_role
}

/// `extractBaseName name` returns `Just base` when `name = base_<digits>`.
/// Mirror of `extractBaseName` (GraphRepr.hs:217-225).
pub fn extract_base_name(name: &str) -> Option<String> {
    let parts: Vec<&str> = name.split('_').collect();
    if parts.len() < 2 { return None; }
    let last = parts.last().unwrap();
    if !last.is_empty() && last.chars().all(|c| c.is_ascii_digit()) {
        Some(parts[..parts.len() - 1].join("_"))
    } else {
        None
    }
}

/// Return the rule's case-name (e.g. `Setup_1`) for proto-rules, else None.
/// Mirror of `getRuleNameByNode`.
pub fn rule_name_by_node(n: &GNode) -> Option<String> {
    if let NodeType::System(ru) = &n.ty {
        if let RuleInfo::Proto(p) = &ru.info {
            return Some(match &p.name {
                ProtoRuleName::Stand(s) => s.clone(),
                ProtoRuleName::Fresh => "Fresh".to_string(),
            });
        }
    }
    None
}

/// Mirror of `groupBySimilarName` — group nodes by their rule's base name.
pub fn group_by_similar_name<'a>(
    nodes: &'a [GNode],
) -> BTreeMap<String, Vec<&'a GNode>> {
    let mut out: BTreeMap<String, Vec<&'a GNode>> = BTreeMap::new();
    for n in nodes {
        if let Some(rn) = rule_name_by_node(n) {
            if let Some(base) = extract_base_name(&rn) {
                out.entry(base).or_default().push(n);
            }
        }
    }
    out
}

/// Filter edges keeping only those whose endpoints are both in `node_ids`.
/// Mirror of `filterEdgesForCluster`.
pub fn filter_edges_for_cluster(
    node_ids: &BTreeSet<NodeId>,
    edges: &[GEdge],
) -> Vec<GEdge> {
    edges.iter().filter(|e| match e {
        GEdge::System(s, t) | GEdge::UnsolvedChain(s, t) =>
            node_ids.contains(&s.0) && node_ids.contains(&t.0),
        GEdge::Less(la) =>
            node_ids.contains(&la.smaller) && node_ids.contains(&la.larger),
    }).cloned().collect()
}

/// Group `nodes` into weakly-connected components under the projection
/// from `edges`.  Mirror of `findConnectedComponents`.
pub fn find_connected_components<'a>(
    nodes: &'a [&'a GNode],
    edges: &[GEdge],
) -> Vec<Vec<&'a GNode>> {
    // Build undirected adjacency.
    let mut adj: BTreeMap<NodeId, BTreeSet<NodeId>> = BTreeMap::new();
    for e in edges {
        let (a, b) = match e {
            GEdge::System(s, t) | GEdge::UnsolvedChain(s, t) =>
                (s.0.clone(), t.0.clone()),
            GEdge::Less(la) => (la.smaller.clone(), la.larger.clone()),
        };
        adj.entry(a.clone()).or_default().insert(b.clone());
        adj.entry(b).or_default().insert(a);
    }
    let mut visited: BTreeSet<NodeId> = BTreeSet::new();
    let mut components: Vec<Vec<&'a GNode>> = Vec::new();
    let by_id: BTreeMap<NodeId, &'a GNode> =
        nodes.iter().map(|n| (n.id.clone(), *n)).collect();
    for n in nodes {
        if visited.contains(&n.id) { continue; }
        let mut stack = vec![n.id.clone()];
        let mut comp_ids: Vec<NodeId> = Vec::new();
        while let Some(cur) = stack.pop() {
            if !visited.insert(cur.clone()) { continue; }
            comp_ids.push(cur.clone());
            if let Some(neighbors) = adj.get(&cur) {
                for nb in neighbors {
                    if !visited.contains(nb) && by_id.contains_key(nb) {
                        stack.push(nb.clone());
                    }
                }
            }
        }
        let comp: Vec<&'a GNode> = comp_ids.iter()
            .filter_map(|nid| by_id.get(nid).copied())
            .collect();
        if !comp.is_empty() { components.push(comp); }
    }
    components
}

/// Generic `addCluster` from `GraphRepr.hs:117-130`.  Given a grouping
/// of nodes (one group per cluster), it:
///   1. computes connected components within each group,
///   2. emits one cluster per component named `<group><suffix><N>`,
///   3. removes those nodes and the intra-cluster edges from the
///      top-level `GraphRepr` fields,
///   4. leaves cross-cluster + non-clustered nodes/edges in place.
pub fn add_cluster(
    repr: &mut GraphRepr,
    nodes_by_group: BTreeMap<String, Vec<&GNode>>,
    name_suffix: &str,
) {
    let all_edges = repr.edges.clone();
    let mut sub_clusters: Vec<Cluster> = Vec::new();
    for (group_name, group_nodes) in &nodes_by_group {
        let group_node_ids: BTreeSet<NodeId> =
            group_nodes.iter().map(|n| n.id.clone()).collect();
        let edges_for_group = filter_edges_for_cluster(&group_node_ids, &all_edges);
        let components = find_connected_components(group_nodes, &edges_for_group);
        for (i, comp) in components.into_iter().enumerate() {
            let comp_ids: BTreeSet<NodeId> =
                comp.iter().map(|n| n.id.clone()).collect();
            let edges_in_comp = filter_edges_for_cluster(&comp_ids, &all_edges);
            sub_clusters.push(Cluster {
                name: format!("{}{}{}", group_name, name_suffix, i + 1),
                nodes: comp.into_iter().cloned().collect(),
                edges: edges_in_comp,
            });
        }
    }
    // Collect all the edges and node ids absorbed by sub_clusters.
    // The cloned cluster edges live at different addresses than the
    // elements of `all_edges`, so absorbed edges must be filtered by
    // structural equality (not pointer identity).
    let absorbed_node_ids: BTreeSet<NodeId> = sub_clusters.iter()
        .flat_map(|c| c.nodes.iter().map(|n| n.id.clone()))
        .collect();
    let absorbed_edges_struct: Vec<GEdge> = sub_clusters.iter()
        .flat_map(|c| c.edges.iter().cloned())
        .collect();
    let remaining_edges: Vec<GEdge> = all_edges.into_iter()
        .filter(|e| !absorbed_edges_struct.iter().any(|ae| ae == e))
        .collect();
    let remaining_nodes: Vec<GNode> = repr.nodes.iter()
        .filter(|n| !absorbed_node_ids.contains(&n.id))
        .cloned()
        .collect();
    repr.clusters = sub_clusters;
    repr.edges = remaining_edges;
    repr.nodes = remaining_nodes;
}

/// Mirror of `addClusterByRole` — wrap `add_cluster` over role groupings.
pub fn add_cluster_by_role(repr: &mut GraphRepr) {
    // Clone nodes from `repr` so the grouping borrows from owned data
    // and doesn't alias `repr`'s nodes field.
    let nodes_owned: Vec<GNode> = repr.nodes.clone();
    let groups: BTreeMap<String, Vec<&GNode>> = group_nodes_by_role(&nodes_owned);
    add_cluster(repr, groups, "_Session_");
}

/// Mirror of `addIntelligentClusterUsingSimilarNames`.
pub fn add_intelligent_cluster_using_similar_names(repr: &mut GraphRepr) {
    let nodes_owned: Vec<GNode> = repr.nodes.clone();
    let groups: BTreeMap<String, Vec<&GNode>> = group_by_similar_name(&nodes_owned);
    add_cluster(repr, groups, "_Session_");
}

// ---------------------------------------------------------------------
// Building a basic repr from a System
// ---------------------------------------------------------------------

use tamarin_theory::constraint::constraints::Goal;
use tamarin_theory::constraint::system::System;

/// Port of `computeBasicGraphRepr` from `Graph.hs:140-150`.
/// Collects from a `System`:
///   - rule nodes,
///   - unsolved-action atoms (KU goals etc.),
///   - the optional last-atom node,
///   - missing nodes referenced by edges.
pub fn compute_basic_graph_repr(sys: &System) -> GraphRepr {
    let mut nodes: Vec<GNode> = Vec::new();
    let mut seen_ids: BTreeSet<NodeId> = BTreeSet::new();
    // 1. System rule instances.
    for (nid, ru) in sys.nodes.iter() {
        nodes.push(GNode { id: nid.clone(), ty: NodeType::System(ru.clone()) });
        seen_ids.insert(nid.clone());
    }
    // 2. Unsolved action atoms — collect by node id.
    let mut by_node: BTreeMap<NodeId, Vec<LNFact>> = BTreeMap::new();
    for (g, st) in sys.goals.iter() {
        if st.solved { continue; }
        if let Goal::Action(nid, fa) = g {
            if seen_ids.contains(nid) { continue; }
            by_node.entry(nid.clone()).or_default().push(fa.clone());
        }
    }
    for (nid, facts) in by_node {
        nodes.push(GNode {
            id: nid.clone(),
            ty: NodeType::UnsolvedAction(facts),
        });
        seen_ids.insert(nid);
    }
    // 3. Last-atom node.
    if let Some(la) = &sys.last_atom {
        if !seen_ids.contains(la) {
            nodes.push(GNode { id: la.clone(), ty: NodeType::LastAction });
            seen_ids.insert(la.clone());
        }
    }
    // 4. Missing nodes referenced by edges.
    for e in &sys.edges {
        if !seen_ids.contains(&e.src.0) {
            nodes.push(GNode {
                id: e.src.0.clone(),
                ty: NodeType::Missing(MissingHint::Conc(e.src.1)),
            });
            seen_ids.insert(e.src.0.clone());
        }
        if !seen_ids.contains(&e.tgt.0) {
            nodes.push(GNode {
                id: e.tgt.0.clone(),
                ty: NodeType::Missing(MissingHint::Prem(e.tgt.1)),
            });
            seen_ids.insert(e.tgt.0.clone());
        }
    }
    // Missing endpoints from less atoms.
    for la in &sys.less_atoms {
        if !seen_ids.contains(&la.smaller) {
            nodes.push(GNode {
                id: la.smaller.clone(),
                ty: NodeType::Missing(MissingHint::Prem(PremIdx(0))),
            });
            seen_ids.insert(la.smaller.clone());
        }
        if !seen_ids.contains(&la.larger) {
            nodes.push(GNode {
                id: la.larger.clone(),
                ty: NodeType::Missing(MissingHint::Prem(PremIdx(0))),
            });
            seen_ids.insert(la.larger.clone());
        }
    }
    // 5. Edges.
    let mut edges: Vec<GEdge> = Vec::new();
    for e in &sys.edges {
        edges.push(GEdge::System(e.src.clone(), e.tgt.clone()));
    }
    for la in &sys.less_atoms {
        edges.push(GEdge::Less(la.clone()));
    }
    for (g, st) in sys.goals.iter() {
        if st.solved { continue; }
        if let Goal::Chain(src, tgt) = g {
            edges.push(GEdge::UnsolvedChain(src.clone(), tgt.clone()));
        }
    }
    GraphRepr { clusters: Vec::new(), nodes, edges }
}

// ---------------------------------------------------------------------
// Convert SysEdge -> GEdge for tests / shared helpers
// ---------------------------------------------------------------------

impl GEdge {
    pub fn from_sys_edge(e: &SysEdge) -> Self {
        GEdge::System(e.src.clone(), e.tgt.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_theory::rule::{ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes, Rule};
    use tamarin_term::lterm::{LSort, LVar};

    fn proto_rule(name: &str, role: Option<&str>) -> RuleACInst {
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
            Vec::new(), Vec::new(), Vec::new(),
        )
    }

    fn nid(name: &str, idx: u64) -> NodeId {
        LVar::new(name, LSort::Node, idx)
    }

    #[test]
    fn extract_base_name_drops_numeric_suffix() {
        assert_eq!(extract_base_name("Setup_1"), Some("Setup".to_string()));
        assert_eq!(extract_base_name("Long_Name_3"), Some("Long_Name".to_string()));
        assert_eq!(extract_base_name("NoSuffix"), None);
        assert_eq!(extract_base_name("Name_NotNumber"), None);
        assert_eq!(extract_base_name(""), None);
    }

    #[test]
    fn cluster_by_role_partitions_nodes() {
        let mut repr = GraphRepr::new();
        repr.nodes.push(GNode {
            id: nid("i", 1),
            ty: NodeType::System(proto_rule("Init", Some("Alice"))),
        });
        repr.nodes.push(GNode {
            id: nid("i", 2),
            ty: NodeType::System(proto_rule("Respond", Some("Bob"))),
        });
        repr.nodes.push(GNode {
            id: nid("i", 3),
            ty: NodeType::System(proto_rule("Init2", Some("Alice"))),
        });
        // No role -> stays at top level
        repr.nodes.push(GNode {
            id: nid("i", 4),
            ty: NodeType::System(proto_rule("Setup", None)),
        });
        add_cluster_by_role(&mut repr);
        // 2 Alice nodes with no connecting edge => 2 separate
        // Alice clusters; 1 Bob => 1 Bob cluster; the roleless node
        // stays at the top level.
        assert_eq!(repr.clusters.len(), 3);
        let cluster_names: Vec<&str> = repr.clusters.iter().map(|c| c.name.as_str()).collect();
        let alice_count = cluster_names.iter()
            .filter(|n| n.starts_with("Alice")).count();
        assert_eq!(alice_count, 2);
        assert!(cluster_names.iter().any(|n| n.starts_with("Bob")));
        // The roleless node stays in repr.nodes.
        assert_eq!(repr.nodes.len(), 1);
    }

    #[test]
    fn cluster_by_role_keeps_connected_alice_together() {
        let mut repr = GraphRepr::new();
        repr.nodes.push(GNode {
            id: nid("i", 1),
            ty: NodeType::System(proto_rule("Init", Some("Alice"))),
        });
        repr.nodes.push(GNode {
            id: nid("i", 3),
            ty: NodeType::System(proto_rule("Init2", Some("Alice"))),
        });
        // Edge connecting the two Alice nodes via a SystemEdge
        repr.edges.push(GEdge::System(
            (nid("i", 1), ConcIdx(0)),
            (nid("i", 3), PremIdx(0)),
        ));
        add_cluster_by_role(&mut repr);
        // One Alice cluster containing both nodes.
        assert_eq!(repr.clusters.len(), 1);
        assert_eq!(repr.clusters[0].nodes.len(), 2);
        assert_eq!(repr.clusters[0].edges.len(), 1);
    }
}
