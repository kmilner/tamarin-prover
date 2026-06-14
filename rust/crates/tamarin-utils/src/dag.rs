//! Port of `Data.DAG.Simple` from `lib/utils/src/Data/DAG/Simple.hs`.
//!
//! Vertex-list-based DAG operations. A `Relation<T>` is `Vec<(T, T)>`.

use std::collections::BTreeSet;
use std::hash::Hash;

pub type Relation<T> = Vec<(T, T)>;

/// `restrict p rel`: keep edges where both endpoints satisfy `p`.
pub fn restrict<T: Clone, F: FnMut(&T) -> bool>(rel: &Relation<T>, mut p: F) -> Relation<T> {
    rel.iter()
        .filter(|(x, y)| p(x) && p(y))
        .cloned()
        .collect()
}

/// `image x rel`: every successor of `x` in `rel`.
pub fn image<T: Eq + Clone>(x: &T, rel: &Relation<T>) -> Vec<T> {
    rel.iter()
        .filter_map(|(a, b)| if a == x { Some(b.clone()) } else { None })
        .collect()
}

/// `inverse rel`: every edge reversed.
pub fn inverse<T: Clone>(rel: &Relation<T>) -> Relation<T> {
    rel.iter().map(|(a, b)| (b.clone(), a.clone())).collect()
}

/// `reachableSet start rel`: every node reachable from any element of `start`.
pub fn reachable_set<T: Ord + Clone>(start: &[T], rel: &Relation<T>) -> BTreeSet<T> {
    let mut visited: BTreeSet<T> = BTreeSet::new();
    let mut stack: Vec<T> = start.to_vec();
    while let Some(x) = stack.pop() {
        if visited.insert(x.clone()) {
            for y in image(&x, rel) {
                if !visited.contains(&y) {
                    stack.push(y);
                }
            }
        }
    }
    visited
}

/// `cyclic rel`: whether `rel` contains a directed cycle.
pub fn cyclic<T: Ord + Clone>(rel: &Relation<T>) -> bool {
    fn find_loop<T: Ord + Clone>(
        rel: &Relation<T>,
        parents: &mut BTreeSet<T>,
        visited: &mut BTreeSet<T>,
        x: T,
    ) -> bool {
        if parents.contains(&x) { return true; }
        if visited.contains(&x) { return false; }
        parents.insert(x.clone());
        let next = image(&x, rel);
        for y in next {
            if find_loop(rel, parents, visited, y) {
                return true;
            }
        }
        parents.remove(&x);
        visited.insert(x);
        false
    }

    let mut visited = BTreeSet::new();
    for (src, _) in rel {
        let mut parents = BTreeSet::new();
        if !visited.contains(src)
            && find_loop(rel, &mut parents, &mut visited, src.clone()) {
                return true;
            }
    }
    false
}

/// `toposort rel`: topological order. If `rel` is cyclic the returned order
/// is some permutation of all vertices but is not guaranteed to be a valid
/// topological sort — matching the Haskell semantics.
pub fn toposort<T: Ord + Clone>(rel: &Relation<T>) -> Vec<T> {
    let inv = inverse(rel);

    // Collect all vertices in source-then-target order, like Haskell's
    // `map fst dag ++ map snd dag`.
    let mut order_input: Vec<T> = Vec::with_capacity(rel.len() * 2);
    for (a, _) in rel { order_input.push(a.clone()); }
    for (_, b) in rel { order_input.push(b.clone()); }

    let mut visited: BTreeSet<T> = BTreeSet::new();
    let mut out: Vec<T> = Vec::new();

    fn visit<T: Ord + Clone>(
        rel: &Relation<T>,
        inv: &Relation<T>,
        visited: &mut BTreeSet<T>,
        out: &mut Vec<T>,
        x: T,
    ) {
        if visited.contains(&x) { return; }
        visited.insert(x.clone());
        for p in image(&x, inv) {
            visit(rel, inv, visited, out, p);
        }
        out.push(x);
    }

    for x in order_input {
        visit(rel, &inv, &mut visited, &mut out, x);
    }
    out
}

/// `dfsLoopBreakers rel`: a minimal set of vertices whose removal breaks
/// every cycle, found by greedy DFS. Determinism follows the order of
/// `rel`'s source vertices.
pub fn dfs_loop_breakers<T: Ord + Clone + Hash>(rel: &Relation<T>) -> Vec<T> {
    let mut visited: BTreeSet<T> = BTreeSet::new();
    let mut breakers: Vec<T> = Vec::new();

    fn find<T: Ord + Clone>(
        rel: &Relation<T>,
        parents: &mut BTreeSet<T>,
        visited: &mut BTreeSet<T>,
        breakers: &mut Vec<T>,
        x: T,
    ) {
        visited.insert(x.clone());
        parents.insert(x.clone());
        let ys = image(&x, rel);
        if ys.iter().any(|y| parents.contains(y)) {
            breakers.push(x.clone());
        } else {
            for y in ys {
                if !visited.contains(&y) {
                    find(rel, parents, visited, breakers, y);
                }
            }
        }
        parents.remove(&x);
    }

    for (src, _) in rel {
        if !visited.contains(src) {
            let mut parents = BTreeSet::new();
            find(rel, &mut parents, &mut visited, &mut breakers, src.clone());
        }
    }
    breakers
}

/// `transRed dag`: transitive reduction of a DAG. Pre: `dag` is acyclic.
pub fn trans_red<T: Ord + Clone>(dag: &Relation<T>) -> Relation<T> {
    let topo = toposort(dag);
    let n = topo.len();
    if n < 2 { return Vec::new(); }

    let dag_set: BTreeSet<(T, T)> = dag.iter().cloned().collect();

    // Pairs (j, i) with j < i, longest gap first, mirroring the Haskell
    // `[reverse [0..x-1] zip repeat x | x <- [1..n-1]]`.
    let mut indexed: Vec<(usize, usize)> = Vec::new();
    for i in 1..n {
        for j in (0..i).rev() {
            indexed.push((j, i));
        }
    }

    let mut new_edges: Relation<T> = Vec::new();
    for (j, i) in indexed {
        let edge = (topo[j].clone(), topo[i].clone());
        if !dag_set.contains(&edge) { continue; }
        let starts = vec![edge.0.clone()];
        let reachable = reachable_set(&starts, &new_edges);
        if !reachable.contains(&edge.1) {
            new_edges.push(edge);
        }
    }
    new_edges
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rel<T: Clone>(es: &[(T, T)]) -> Relation<T> { es.to_vec() }

    #[test]
    fn image_and_inverse() {
        let r = rel(&[(1, 2), (1, 3), (2, 3)]);
        let mut img = image(&1, &r);
        img.sort();
        assert_eq!(img, vec![2, 3]);
        let inv = inverse(&r);
        assert!(inv.contains(&(2, 1)));
        assert!(inv.contains(&(3, 1)));
        assert!(inv.contains(&(3, 2)));
    }

    #[test]
    fn restrict_filters() {
        let r = rel(&[(1, 2), (2, 3), (3, 4)]);
        let r2 = restrict(&r, |x| *x != 3);
        assert_eq!(r2, vec![(1, 2)]);
    }

    #[test]
    fn reachable_basic() {
        let r = rel(&[(1, 2), (2, 3), (4, 5)]);
        let s = reachable_set(&[1], &r);
        assert_eq!(s, BTreeSet::from([1, 2, 3]));
        let s = reachable_set(&[4], &r);
        assert_eq!(s, BTreeSet::from([4, 5]));
    }

    #[test]
    fn cyclic_detection() {
        assert!(!cyclic(&rel(&[(1, 2), (2, 3)])));
        assert!(cyclic(&rel(&[(1, 2), (2, 1)])));
        assert!(cyclic(&rel(&[(1, 1)]))); // self-loop
        assert!(cyclic(&rel(&[(1, 2), (2, 3), (3, 1)])));
        assert!(!cyclic(&rel::<i32>(&[])));
    }

    #[test]
    fn toposort_acyclic_is_valid() {
        let r = rel(&[(1, 2), (1, 3), (3, 4), (2, 4)]);
        let order = toposort(&r);
        for (a, b) in &r {
            let pa = order.iter().position(|x| x == a).unwrap();
            let pb = order.iter().position(|x| x == b).unwrap();
            assert!(pa < pb, "{} should come before {} in {:?}", a, b, order);
        }
    }

    #[test]
    fn loop_breakers_break_cycles() {
        let r = rel(&[(1, 2), (2, 3), (3, 1), (3, 4)]);
        let breakers = dfs_loop_breakers(&r);
        assert!(!breakers.is_empty());
        let kept: Relation<i32> = restrict(&r, |x| !breakers.contains(x));
        assert!(!cyclic(&kept));
    }

    #[test]
    fn loop_breakers_empty_for_acyclic() {
        let r = rel(&[(1, 2), (2, 3)]);
        assert_eq!(dfs_loop_breakers(&r), Vec::<i32>::new());
    }

    #[test]
    fn trans_red_removes_redundant_edges() {
        // 1 -> 2 -> 3, plus shortcut 1 -> 3
        let r = rel(&[(1, 2), (2, 3), (1, 3)]);
        let red = trans_red(&r);
        let red_set: BTreeSet<(i32, i32)> = red.iter().cloned().collect();
        // The reduction must drop (1,3) and keep (1,2),(2,3).
        assert!(red_set.contains(&(1, 2)));
        assert!(red_set.contains(&(2, 3)));
        assert!(!red_set.contains(&(1, 3)));
    }
}
