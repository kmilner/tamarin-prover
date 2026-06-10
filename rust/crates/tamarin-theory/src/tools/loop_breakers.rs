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

use std::collections::BTreeSet;

/// Compute a minimal set of loop-breakers using a greedy DFS strategy.
///
/// **Faithful port of Haskell's `Data.DAG.Simple.dfsLoopBreakers`**
/// (`lib/utils/src/Data/DAG/Simple.hs:111-128`):
///
/// ```haskell
/// dfsLoopBreakers rel =
///     D.toList $ snd $ execRWS (mapM_ (visit . fst) rel) () S.empty
///   where
///     visit x = do
///         visited <- gets (S.member x)
///         unless visited $ findLoopBreakers S.empty x
///     findLoopBreakers parents0 x = do
///         modify (S.insert x)
///         let parents = S.insert x parents0
///             ys      = x `image` rel
///         if any (`S.member` parents) ys
///           then tell (return x)
///           else forM_ ys $ \y -> do
///                    visited <- gets (S.member y)
///                    unless visited $ findLoopBreakers parents y
/// ```
///
/// Key semantics replicated exactly:
/// - Iterate the relation in **list order** (`mapM_ (visit . fst) rel`),
///   using each tuple's first component as a DFS root.  The relation
///   ordering therefore matters; callers must build it in HS's order.
/// - A single **monotonic `visited` set** shared across all DFS roots
///   (`execRWS ... S.empty`): once a node is visited it is never
///   re-explored, even from a later root.  (RS's prior implementation
///   re-ran the whole DFS after each pick — not faithful.)
/// - On the **first** successor that is already a parent (back-edge),
///   emit the **current node `x`** (the back-edge SOURCE) as a loop
///   breaker and STOP descending.  (RS's prior implementation emitted
///   the back-edge TARGET / gray ancestor — not faithful.)
/// - Emission order = DFS discovery order (`tell`/`DList` append);
///   we mirror it with a `Vec` so the returned list matches HS's
///   `D.toList`.
///
/// `image x rel = [ y' | (x', y') <- rel, x == x' ]` preserves the
/// relation's list order for successor iteration, so we recompute it
/// per node from the slice (matching HS — no pre-sorted adjacency map).
pub fn dfs_loop_breakers<N: Clone + Ord>(
    relation: &[(N, N)],
) -> Vec<N> {
    let mut visited: BTreeSet<N> = BTreeSet::new();
    let mut breakers: Vec<N> = Vec::new();

    // `image x rel` — successors of `x` in relation list order.
    fn image<'a, N: Clone + Ord>(x: &N, rel: &'a [(N, N)]) -> Vec<N> {
        rel.iter()
            .filter(|(a, _)| a == x)
            .map(|(_, b)| b.clone())
            .collect()
    }

    // PRE: x0 is not yet visited.
    fn find_loop_breakers<N: Clone + Ord>(
        parents0: &BTreeSet<N>,
        x: &N,
        rel: &[(N, N)],
        visited: &mut BTreeSet<N>,
        breakers: &mut Vec<N>,
    ) {
        visited.insert(x.clone());
        let mut parents = parents0.clone();
        parents.insert(x.clone());
        let ys = image(x, rel);
        if ys.iter().any(|y| parents.contains(y)) {
            // Back-edge to a parent: emit `x` and stop descending.
            breakers.push(x.clone());
        } else {
            for y in &ys {
                if !visited.contains(y) {
                    find_loop_breakers(&parents, y, rel, visited, breakers);
                }
            }
        }
    }

    for (x, _) in relation {
        if !visited.contains(x) {
            find_loop_breakers(&BTreeSet::new(), x, relation, &mut visited, &mut breakers);
        }
    }
    breakers
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
