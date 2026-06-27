//! Port of `Theory.Tools.SubtermStore`.
//!
//! The subterm store accumulates `t1 << t2` constraints during proof
//! search, propagating them and detecting contradictions. This module
//! holds the store data type plus the pieces the solver calls directly:
//! constraint accumulation (`add`/`add_neg`), `conjoin` (HS
//! `conjoinSubtermStores`), the subterm-cycle check `has_subterm_cycle`
//! (HS `hasSubtermCycle`, the CR-rule S_chain test), and the
//! `elem_not_below_reducible` predicate (HS `Term.elemNotBelowReducible`).
//! The simplification passes that depend on AC-unification —
//! `simpSubtermStore`, `simpSplitNegSt`, and the recursive `splitSubterm`
//! — are ported in `constraint::solver::simplify` rather than here.

use tamarin_term::function_symbols::FunSym;
use tamarin_utils::FastSet;
use tamarin_term::lterm::LNTerm;
use tamarin_term::term::Term;

/// One stored subterm constraint: `small ⊏ big`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubtermConstraint {
    pub small: LNTerm,
    pub big: LNTerm,
    /// Whether this constraint has already been propagated.
    pub propagated: bool,
}

/// Subterm store. Mirrors HS's 5-field `SubtermStore`
/// (SubtermStore.hs:90-96):
///   negSubterms / posSubterms / solvedSubterms / isContradictory /
///   oldNegSubterms.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SubtermStore {
    pub subterms: Vec<SubtermConstraint>,
    pub solved_subterms: Vec<SubtermConstraint>,
    /// Whether the store has been determined contradictory.
    pub contradictory: bool,
    /// Negative subterm constraints `¬(small ⊏ big)` — HS `_negSubterms`
    /// (S.Set, so kept sorted by the LNTerm pair Ord for HS-faithful
    /// `S.toList` iteration order).
    pub neg_subterms: Vec<(LNTerm, LNTerm)>,
    /// Copy of `neg_subterms` that is NOT changed by apply/HasFrees/
    /// add_neg — HS `_oldNegSubterms` (SubtermStore.hs:95).  Only the
    /// `simpSplitNegSt` pass updates it; the set difference
    /// `neg_subterms \ old_neg_subterms` is the change-detection
    /// mechanism deciding which negative subterms get (re-)split.
    pub old_neg_subterms: Vec<(LNTerm, LNTerm)>,
}

impl SubtermStore {
    pub fn empty() -> Self { Self::default() }

    /// Record a new `small << big` constraint.
    pub fn add(&mut self, small: LNTerm, big: LNTerm) {
        self.subterms.push(SubtermConstraint { small, big, propagated: false });
    }

    /// `addNegSubterm` (SubtermStore.hs:125-126): set-insert into
    /// negSubterms.  Sorted insert keeps HS `S.toList` iteration order.
    /// Returns true if the pair was newly added.
    pub fn add_neg(&mut self, small: LNTerm, big: LNTerm) -> bool {
        let pair = (small, big);
        match self.neg_subterms.binary_search(&pair) {
            Ok(_) => false,
            Err(pos) => { self.neg_subterms.insert(pos, pair); true }
        }
    }

    pub fn is_false(&self) -> bool { self.contradictory }

    /// `conjoinSubtermStores` — HS-faithful port of
    /// `Theory.Tools.SubtermStore.conjoinSubtermStores` (SubtermStore.hs:108):
    /// ```haskell
    /// conjoinSubtermStores (SubtermStore a1 b1 c1 d1 e1) (SubtermStore a2 b2 c2 d2 e2)
    ///   = SubtermStore (a1 `S.union` a2) (b1 `S.union` b2)
    ///                  (c1 `S.union` c2) (d1 || d2) (e1 `S.union` e2)
    /// ```
    /// All five HS fields union per HS semantics: neg/pos/solved set-union,
    /// `isContradictory` OR, `oldNegSubterms` set-union.
    pub fn conjoin(&mut self, other: &SubtermStore) {
        for st in &other.subterms {
            if !self.subterms.contains(st) {
                self.subterms.push(st.clone());
            }
        }
        for st in &other.solved_subterms {
            if !self.solved_subterms.contains(st) {
                self.solved_subterms.push(st.clone());
            }
        }
        self.contradictory = self.contradictory || other.contradictory;
        for (s, t) in &other.neg_subterms {
            self.add_neg(s.clone(), t.clone());
        }
        for p in &other.old_neg_subterms {
            if let Err(pos) = self.old_neg_subterms.binary_search(p) {
                self.old_neg_subterms.insert(pos, p.clone());
            }
        }
    }
}

/// `elemNotBelowReducible reducible inner outer` — port of Haskell's
/// `Term.Term.elemNotBelowReducible` (`Term.hs:248`).  True iff
/// `inner` occurs syntactically in `outer` and never below a
/// reducible function symbol.
///
/// Used by `has_subterm_cycle` and (indirectly) by the subterm-store
/// simplification.  The "below reducible" exception is sound under
/// the equational theory: once you cross a reducible head, the
/// subterm could disappear under rewriting.
pub fn elem_not_below_reducible(
    reducible: &FastSet<FunSym>,
    inner: &LNTerm,
    outer: &LNTerm,
) -> bool {
    if inner == outer { return true; }
    match outer {
        Term::App(sym, args) => {
            if reducible.contains(sym) { return false; }
            args.iter().any(|a| elem_not_below_reducible(reducible, inner, a))
        }
        _ => false,
    }
}

/// `hasSubtermCycle` — port of Haskell's
/// `Theory.Tools.SubtermStore.hasSubtermCycle` (`SubtermStore.hs:223`).
///
/// Detects a cycle `t0 ⊏ x0, ..., tn ⊏ xn = t0 ⊏ x0` in the positive
/// subterm dag, where each next edge `(t_i+1, x_i+1)` follows from
/// `elem_not_below_reducible reducible x_i t_i+1`.
///
/// Returns `true` if any such cycle exists.  The DFS uses (entry,
/// parent-set) tracking to avoid revisiting already-finished nodes
/// while still detecting back-edges into the current recursion
/// stack.
pub fn has_subterm_cycle(
    reducible: &FastSet<FunSym>,
    store: &SubtermStore,
) -> bool {
    // Build the dag from positive subterms — every active (small, big)
    // constraint is an edge in the dependency dag.
    let dag: Vec<(LNTerm, LNTerm)> = store.subterms.iter()
        .map(|c| (c.small.clone(), c.big.clone()))
        .collect();
    if dag.is_empty() { return false; }
    let mut visited: std::collections::BTreeSet<(LNTerm, LNTerm)>
        = std::collections::BTreeSet::new();
    for edge in &dag {
        let mut parents = std::collections::BTreeSet::new();
        if find_loop(reducible, &dag, edge, &mut parents, &mut visited).is_none() {
            return true;
        }
    }
    false
}

/// DFS helper: returns `None` on a detected back-edge (cycle),
/// `Some(())` otherwise.  Marks the edge as visited on completion.
fn find_loop(
    reducible: &FastSet<FunSym>,
    dag: &[(LNTerm, LNTerm)],
    x: &(LNTerm, LNTerm),
    parents: &mut std::collections::BTreeSet<(LNTerm, LNTerm)>,
    visited: &mut std::collections::BTreeSet<(LNTerm, LNTerm)>,
) -> Option<()> {
    if parents.contains(x) { return None; }
    if visited.contains(x) { return Some(()); }
    parents.insert(x.clone());
    // Successors: edges (e, e') in the dag such that `x.1` (the big
    // side of x's subterm) appears in `e` not below a reducible head.
    let next: Vec<&(LNTerm, LNTerm)> = dag.iter()
        .filter(|e| elem_not_below_reducible(reducible, &x.1, &e.0))
        .collect();
    for n in next {
        find_loop(reducible, dag, n, parents, visited)?;
    }
    parents.remove(x);
    visited.insert(x.clone());
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::Lit;
    use tamarin_term::term::Term;

    fn var(name: &str) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Msg, 0)))
    }

    #[test]
    fn empty_store_is_consistent() {
        let s = SubtermStore::empty();
        assert!(!s.is_false());
        assert!(s.subterms.is_empty());
    }

    #[test]
    fn add_records_constraint() {
        let mut s = SubtermStore::empty();
        s.add(var("x"), var("y"));
        assert_eq!(s.subterms.len(), 1);
        assert!(!s.subterms[0].propagated);
    }
}
