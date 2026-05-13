//! Loop breakers for the premise-conclusion dataflow graph.
//!
//! Port of `Theory.Tools.LoopBreakers`. The full Haskell function
//! `useAutoLoopBreakersAC` builds a relation over `(rule, prem-idx)`
//! pairs where solving one premise might lead to another premise
//! becoming open, then computes a minimum cycle-breaking set with
//! DFS.
//!
//! For the Rust port we expose the cycle-breaking algorithm
//! (`dfs_loop_breakers`) and the abstraction over data-flow
//! relations. Computing the actual relation requires Maude-backed
//! unifiability — that piece is wired in by callers once the typed
//! rule layer is in place.

use std::collections::{BTreeMap, BTreeSet};

/// Compute a set of edges to remove from a relation so that the
/// remaining graph is acyclic. The strategy mirrors Haskell's
/// `dfsLoopBreakers`: walk the relation in DFS order; whenever a
/// back-edge is encountered, mark its target node as a "loop
/// breaker" and remove all edges with that target.
///
/// The function returns the loop-breaker nodes — *target* sides of
/// removed edges — sorted in deterministic order for reproducibility.
pub fn dfs_loop_breakers<N: Clone + Ord>(
    relation: &[(N, N)],
) -> Vec<N> {
    // Build adjacency map.
    let mut adj: BTreeMap<N, Vec<N>> = BTreeMap::new();
    for (src, dst) in relation {
        adj.entry(src.clone()).or_default().push(dst.clone());
    }
    let mut breakers: BTreeSet<N> = BTreeSet::new();

    // Stable DFS visiting all sources.
    loop {
        let cur_relation: Vec<(N, N)> = relation.iter()
            .filter(|(_, d)| !breakers.contains(d))
            .cloned()
            .collect();
        let mut adj_now: BTreeMap<N, Vec<N>> = BTreeMap::new();
        for (src, dst) in &cur_relation {
            adj_now.entry(src.clone()).or_default().push(dst.clone());
        }
        // Detect any cycle in the current adjacency. If found, pick
        // the lexicographically smallest node in that cycle as a
        // breaker and continue.
        if let Some(cycle_node) = find_cycle_node(&adj_now) {
            breakers.insert(cycle_node);
        } else {
            break;
        }
    }
    breakers.into_iter().collect()
}

/// DFS that returns one node belonging to a cycle, if any.
fn find_cycle_node<N: Clone + Ord>(adj: &BTreeMap<N, Vec<N>>) -> Option<N> {
    // 0=white, 1=gray, 2=black
    let mut color: BTreeMap<N, u8> = BTreeMap::new();
    let nodes: Vec<N> = adj.keys().cloned().collect();
    fn dfs<N: Clone + Ord>(
        n: &N,
        adj: &BTreeMap<N, Vec<N>>,
        color: &mut BTreeMap<N, u8>,
    ) -> Option<N> {
        color.insert(n.clone(), 1);
        if let Some(succs) = adj.get(n) {
            for s in succs {
                match color.get(s).copied().unwrap_or(0) {
                    1 => return Some(s.clone()),  // back-edge → cycle
                    0 => if let Some(c) = dfs(s, adj, color) { return Some(c); },
                    _ => {}
                }
            }
        }
        color.insert(n.clone(), 2);
        None
    }
    for n in &nodes {
        if color.get(n).copied().unwrap_or(0) == 0 {
            if let Some(c) = dfs(n, adj, &mut color) { return Some(c); }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_relation_no_breakers() {
        let r: Vec<(u32, u32)> = vec![];
        assert!(dfs_loop_breakers(&r).is_empty());
    }

    #[test]
    fn dag_no_breakers() {
        // 1 → 2 → 3, no cycle.
        let r = vec![(1, 2), (2, 3)];
        assert!(dfs_loop_breakers(&r).is_empty());
    }

    #[test]
    fn simple_cycle_breaks_one() {
        // 1 → 2 → 1. Breaking either makes it acyclic.
        let r = vec![(1, 2), (2, 1)];
        let breakers = dfs_loop_breakers(&r);
        assert_eq!(breakers.len(), 1);
        assert!(breakers[0] == 1 || breakers[0] == 2);
    }

    #[test]
    fn three_cycle_breaks_one() {
        // 1 → 2 → 3 → 1.
        let r = vec![(1, 2), (2, 3), (3, 1)];
        let breakers = dfs_loop_breakers(&r);
        assert_eq!(breakers.len(), 1);
    }

    #[test]
    fn two_independent_cycles_break_both() {
        let r = vec![(1, 2), (2, 1), (3, 4), (4, 3)];
        let breakers = dfs_loop_breakers(&r);
        assert_eq!(breakers.len(), 2);
    }
}
