//! Port of `Term.LTerm.renamePrecise` applied to a `System`.
//!
//! Haskell `cleanup` (ProofMethod.hs:443-444):
//! ```haskell
//! cleanup s = L.set sSubst emptySubst (Precise.evalFresh (renamePrecise s) Precise.nothingUsed)
//! ```
//!
//! `renamePrecise` walks every free `LVar` in a value in a deterministic
//! traversal order and rebinds each *unique* `LVar` to a freshly-allocated
//! `LVar` keyed by name. The result is canonical for two values that differ
//! only by variable indices — exactly the property `M.fromListWith` needs in
//! `process` (ProofMethod.hs:440) to dedup variant-divergent case maps.
//!
//! In Rust we don't have a single `mapFrees` typeclass that covers `System`,
//! so we walk each field by hand. The walk-order mirrors
//! `Reduction::subst_system_once` so any future cross-checks stay aligned.

use std::collections::HashMap;

use tamarin_term::lterm::{HasFrees, LVar, LNTerm};
use tamarin_term::subst::Subst;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;
use tamarin_utils::fresh::PreciseFreshState;

use crate::constraint::constraints::Goal;
use crate::constraint::system::System;
use crate::guarded::{subst_guarded, VarSubst};

/// Canonicalise the free `LVar`s of `sys` so that two systems differing
/// only by variable numbering compare equal.
///
/// Mirrors Haskell's `renamePrecise` over the `System` record.
pub fn rename_precise_system(sys: &mut System) {
    let mut state = RenameState::new();

    // ----------------------------------------------------------------------
    // Phase 1 — walk every free LVar in deterministic traversal order so the
    // import-binding map is populated independent of how we apply later.
    //
    // HS-faithful order — matches `instance HasFrees System` field walk
    // (System.hs:383-397 declaration order, traversed by foldFrees):
    //   sNodes → sEdges → sLessAtoms → sLastAtom → sSubtermStore →
    //   sEqStore → sFormulas → sSolvedFormulas → sLemmas → sGoals
    //
    // This MUST match HS's renamePrecise to keep per-name idx assignment
    // in lockstep.  Previously Rust visited goals BEFORE formulas, which
    // for Helper_Loop_and_success caused formula[0]'s free `k2` to end
    // up at idx 4 (because 4 other "k2" LVars in goals' Disjs were
    // imported first) — making it a DIFFERENT LVar from the action term
    // `k2` (which got idx 0 elsewhere), so the impl pass's match against
    // `∀ t. ChainKey(k2) @ t ⇒ ⊥` failed and no gfalse was emitted at
    // case_3 entry — forcing Rust to solve an inner disj before reaching
    // contradiction.
    // ----------------------------------------------------------------------

    // HS-faithful: HS's `instance HasFrees (Map k v)` uses
    // `M.foldrWithKey` which walks the map keyed by `Ord k` ascending
    // (Term/LTerm.hs:829-836).  Rust's `sys.nodes` is a `Vec<(NodeId,
    // RuleACInst)>` in insertion order — that order is NOT the same as
    // NodeId-ascending.  Without this sort, the walk visits a newly-grafted
    // source-case Gen_Step (high pre-rename idx but inserted last) AFTER
    // pre-existing Check nodes — yet then `state.import` allocates per-name
    // counters in *visit* order, so the newly-grafted Gen_Step gets the
    // FIRST fresh "vr" slot if walked first / LAST if walked last.  For
    // Helper_Loop_and_success this controls whether vr.0 ends up Check
    // (HS pattern) or Gen_Step (Rust pre-fix pattern), which in turn flips
    // impliedFormulas' sysActions iteration order and the Disj goal-nrs.
    let mut nodes_sorted: Vec<&(crate::constraint::constraints::NodeId, crate::rule::RuleACInst)>
        = sys.nodes.iter().collect();
    nodes_sorted.sort_by(|a, b| a.0.cmp(&b.0));
    for (id, rule) in nodes_sorted {
        state.import(id);
        rule.for_each_free(&mut |v| { state.import(v); });
    }
    for e in &sys.edges {
        state.import(&e.src.0);
        state.import(&e.tgt.0);
    }
    for la in &sys.less_atoms {
        state.import(&la.smaller);
        state.import(&la.larger);
    }
    if let Some(la) = &sys.last_atom { state.import(la); }
    for c in &sys.subterm_store.subterms {
        c.small.for_each_free(&mut |v| { state.import(v); });
        c.big.for_each_free(&mut |v| { state.import(v); });
    }
    for c in &sys.subterm_store.solved_subterms {
        c.small.for_each_free(&mut |v| { state.import(v); });
        c.big.for_each_free(&mut |v| { state.import(v); });
    }
    // eq_store.subst: visit keys (dom) and values (range).
    for (k, t) in sys.eq_store.subst.to_list() {
        state.import(&k);
        t.for_each_free(&mut |v| { state.import(v); });
    }
    // eq_store.conj: HS-faithful `HasFrees (SubstVFresh n LVar)` only
    // walks DOMAIN (keys), NOT values (SubstVFresh.hs:196-202).  This
    // preserves the witness idxs in values — crucial for
    // sort-discriminating across variants at perform_split.
    for d in &sys.eq_store.conj {
        for s in &d.substs {
            for (k, _t) in s.to_list() {
                state.import(&k);
                // Note: value vars NOT imported (HS-faithful).
            }
        }
    }
    for f in &sys.formulas { guarded_for_each_free(f, &mut |v| { state.import(v); }); }
    for f in &sys.solved_formulas { guarded_for_each_free(f, &mut |v| { state.import(v); }); }
    for f in &sys.lemmas { guarded_for_each_free(f, &mut |v| { state.import(v); }); }
    for (g, _) in &sys.goals {
        goal_for_each_free(g, &mut |v| { state.import(v); });
    }

    // ----------------------------------------------------------------------
    // Phase 2 — apply the renaming map.
    //
    // For LVar-only fields we look up directly. For term-bearing fields we
    // build a `Subst` (LVar → Var-term) and apply via `apply_vterm`. For
    // guarded formulas we use the parser-level `VarSubst`.
    // ----------------------------------------------------------------------

    let map = state.into_map();
    if map.is_empty() { return; }

    let term_subst: Subst<tamarin_term::lterm::Name, LVar> = Subst::from_list(
        map.iter().map(|(old, new)| {
            (old.clone(), Term::Lit(Lit::Var(new.clone())))
        }),
    );
    let formula_subst: VarSubst = map.iter().map(|(old, new)| {
        let sort = lvar_sort_to_sort_hint(new.sort);
        (
            (old.name.clone(), old.idx),
            tamarin_parser::ast::Term::Var(tamarin_parser::ast::VarSpec {
                name: new.name.clone(),
                idx: new.idx,
                sort,
                typ: None,
            }),
        )
    }).collect();

    let map_var = |v: LVar| -> LVar {
        map.get(&v).cloned().unwrap_or(v)
    };

    // 1. Nodes — id + rule.
    let nodes = std::mem::take(&mut sys.nodes);
    sys.nodes = nodes.into_iter().map(|(id, rule)| {
        let new_id = map_var(id);
        let new_rule = rule.map_free(&mut |v| map_var(v));
        (new_id, new_rule)
    }).collect();

    // 2. Edges.
    for e in sys.edges.iter_mut() {
        e.src.0 = map_var(e.src.0.clone());
        e.tgt.0 = map_var(e.tgt.0.clone());
    }
    // Dedup after rename — sort + dedup (matches subst_system).
    let mut tmp: Vec<_> = std::mem::take(&mut sys.edges);
    tmp.sort();
    tmp.dedup();
    sys.edges = tmp;

    // 3. Last atom.
    if let Some(la) = sys.last_atom.take() {
        sys.last_atom = Some(map_var(la));
    }

    // 4. Less atoms.
    for la in sys.less_atoms.iter_mut() {
        la.smaller = map_var(la.smaller.clone());
        la.larger  = map_var(la.larger.clone());
    }

    // 5. Goals — per-variant rewrite.
    let goals = std::mem::take(&mut sys.goals);
    let apply_term = |t: LNTerm| -> LNTerm {
        tamarin_term::subst::apply_vterm(&term_subst, t)
    };
    let apply_fact = |fa: crate::fact::LNFact| -> crate::fact::LNFact {
        crate::fact::Fact {
            tag: fa.tag,
            annotations: fa.annotations,
            terms: fa.terms.into_iter().map(|t| apply_term(t)).collect(),
        }
    };
    let mut new_goals: Vec<(Goal, crate::constraint::system::GoalStatus)> =
        Vec::with_capacity(goals.len());
    for (g, st) in goals {
        let g2 = match g {
            Goal::Action(i, fa) => Goal::Action(map_var(i), apply_fact(fa)),
            Goal::Premise(p, fa) => Goal::Premise((map_var(p.0), p.1), apply_fact(fa)),
            Goal::Chain(c, p) => Goal::Chain(
                (map_var(c.0), c.1),
                (map_var(p.0), p.1),
            ),
            Goal::Disj(d) => {
                let items: Vec<crate::guarded::Guarded> = d.0.into_iter()
                    .map(|g| subst_guarded(&g, &formula_subst))
                    .collect();
                Goal::Disj(crate::constraint::constraints::Disj(items))
            }
            Goal::Split(s) => Goal::Split(s),
            Goal::Subterm((s, t)) => Goal::Subterm((apply_term(s), apply_term(t))),
        };
        if !new_goals.iter().any(|(eg, _)| eg == &g2) {
            new_goals.push((g2, st));
        }
    }
    sys.goals = new_goals;

    // 6. Formulas / solved / lemmas — via parser-level VarSubst.
    if !formula_subst.is_empty() {
        for f in sys.formulas.iter_mut() {
            *f = subst_guarded(f, &formula_subst);
        }
        for f in sys.solved_formulas.iter_mut() {
            *f = subst_guarded(f, &formula_subst);
        }
        for f in sys.lemmas.iter_mut() {
            *f = subst_guarded(f, &formula_subst);
        }
    }

    // 7. eq_store — rewrite the subst (dom + range) and the conj.
    let old_subst = std::mem::replace(
        &mut sys.eq_store.subst,
        crate::tools::equation_store::LNSubst::empty(),
    );
    let pairs: Vec<(LVar, LNTerm)> = old_subst.to_list().into_iter()
        .map(|(k, v)| (map_var(k), apply_term(v)))
        .collect();
    sys.eq_store.subst = Subst::from_list(pairs);

    // HS-faithful: `HasFrees (SubstVFresh n LVar)` only maps DOMAIN
    // (keys), NOT values.  From Term.Substitution.SubstVFresh.hs:196-202:
    //
    //   instance HasFrees (SubstVFresh n LVar) where
    //       foldFrees f = foldFrees f . M.keys . svMap
    //       foldFreesOcc _ _ = const mempty
    //       mapFrees f =
    //           (substFromListVFresh <$>) . traverse mapDomain
    //                                     . substToListVFresh
    //         where mapDomain (v, t) = (,t) <$> mapFrees f v
    //
    // So renamePrecise renames variant subst KEYS but PRESERVES the
    // witness idxs in VALUES.  This preserves the AES-output witness
    // idxs at perform_split time — which is what gives HS the
    // sort-discriminating idx differences across variants (e.g.,
    // ~k.11 vs ~k.14 for test4's CHECKSIGN vs SIGN).
    //
    // Rust previously renamed values too, collapsing all to small
    // PreciseFresh idxs (1, 2) and reversing the sort order vs HS.
    for d in sys.eq_store.conj.iter_mut() {
        for s in d.substs.iter_mut() {
            let pairs: Vec<(LVar, LNTerm)> = s.to_list().into_iter()
                .map(|(k, v)| (map_var(k), v))  // keep VALUE unchanged
                .collect();
            *s = tamarin_term::subst_vfresh::SubstVFresh::from_list(pairs);
        }
    }

    // 8. Subterm store.
    for c in sys.subterm_store.subterms.iter_mut() {
        c.small = apply_term(c.small.clone());
        c.big = apply_term(c.big.clone());
    }
    for c in sys.subterm_store.solved_subterms.iter_mut() {
        c.small = apply_term(c.small.clone());
        c.big = apply_term(c.big.clone());
    }
}

// =============================================================================
// Helpers
// =============================================================================

struct RenameState {
    fresh: PreciseFreshState,
    map: HashMap<LVar, LVar>,
}

impl RenameState {
    fn new() -> Self {
        RenameState { fresh: PreciseFreshState::nothing_used(), map: HashMap::new() }
    }
    /// `importBinding`: idempotent — first call for `v` allocates a fresh
    /// LVar keyed by `v.name`; later calls return the same binding.
    fn import(&mut self, v: &LVar) {
        if self.map.contains_key(v) { return; }
        let idx = self.fresh.fresh_ident(&v.name);
        let new_v = LVar { name: v.name.clone(), sort: v.sort, idx };
        self.map.insert(v.clone(), new_v);
    }
    fn into_map(self) -> HashMap<LVar, LVar> { self.map }
}

fn lvar_sort_to_sort_hint(s: tamarin_term::lterm::LSort) -> tamarin_parser::ast::SortHint {
    use tamarin_term::lterm::LSort;
    use tamarin_parser::ast::SortHint;
    match s {
        LSort::Msg => SortHint::Msg,
        LSort::Pub => SortHint::Pub,
        LSort::Fresh => SortHint::Fresh,
        LSort::Node => SortHint::Node,
        LSort::Nat => SortHint::Nat,
    }
}

fn goal_for_each_free(g: &Goal, f: &mut dyn FnMut(&LVar)) {
    match g {
        Goal::Action(i, fa) => {
            f(i);
            fa.for_each_free(f);
        }
        Goal::Premise(p, fa) => {
            f(&p.0);
            fa.for_each_free(f);
        }
        Goal::Chain(c, p) => {
            f(&c.0);
            f(&p.0);
        }
        Goal::Disj(d) => {
            for item in &d.0 { guarded_for_each_free(item, f); }
        }
        Goal::Split(_) => {}
        Goal::Subterm((a, b)) => {
            a.for_each_free(f);
            b.for_each_free(f);
        }
    }
}

/// Walk every free `LVar` of a `Guarded` formula. With DeBruijn bindings,
/// `BVar::Bound` leaves carry no LVar identity and are auto-skipped; only
/// `BVar::Free` leaves get visited.
fn guarded_for_each_free(g: &crate::guarded::Guarded, f: &mut dyn FnMut(&LVar)) {
    use crate::guarded::Guarded;
    match g {
        Guarded::Atom(a) => atom_for_each_free(a, f),
        Guarded::Disj(xs) | Guarded::Conj(xs) => {
            for x in xs { guarded_for_each_free(x, f); }
        }
        Guarded::GGuarded { guards, body, .. } => {
            for a in guards { atom_for_each_free(a, f); }
            guarded_for_each_free(body, f);
        }
    }
}

fn atom_for_each_free(a: &crate::guarded::GAtom, f: &mut dyn FnMut(&LVar)) {
    use crate::guarded::GAtom;
    match a {
        GAtom::Eq(x, y) | GAtom::Less(x, y)
        | GAtom::LessMset(x, y) | GAtom::Subterm(x, y) => {
            term_for_each_free(x, f);
            term_for_each_free(y, f);
        }
        GAtom::Action(fa, t) => {
            for arg in &fa.args { term_for_each_free(arg, f); }
            term_for_each_free(t, f);
        }
        GAtom::Last(t) => term_for_each_free(t, f),
        GAtom::Pred(fa) => { for arg in &fa.args { term_for_each_free(arg, f); } }
    }
}

fn term_for_each_free(t: &crate::guarded::GTerm, f: &mut dyn FnMut(&LVar)) {
    use crate::guarded::{GTerm, BVar};
    match t {
        GTerm::Var(BVar::Free(v)) => {
            let sort = parser_sort_to_lsort(v.sort);
            f(&LVar { name: v.name.clone(), sort, idx: v.idx });
        }
        GTerm::Var(BVar::Bound(_)) => {}
        GTerm::PubLit(_) | GTerm::FreshLit(_) | GTerm::NatLit(_)
        | GTerm::Number(_) | GTerm::NumberOne | GTerm::NatOne | GTerm::DhNeutral => {}
        GTerm::App(_, args) | GTerm::Pair(args) => {
            for a in args { term_for_each_free(a, f); }
        }
        GTerm::AlgApp(_, a, b) | GTerm::Diff(a, b) | GTerm::BinOp(_, a, b) => {
            term_for_each_free(a, f);
            term_for_each_free(b, f);
        }
        GTerm::PatMatch(t) => term_for_each_free(t, f),
    }
}

fn parser_sort_to_lsort(s: tamarin_parser::ast::SortHint) -> tamarin_term::lterm::LSort {
    use tamarin_parser::ast::{SortHint, SuffixSort};
    use tamarin_term::lterm::LSort;
    match s {
        SortHint::Msg | SortHint::Untagged => LSort::Msg,
        SortHint::Pub => LSort::Pub,
        SortHint::Fresh => LSort::Fresh,
        SortHint::Node => LSort::Node,
        SortHint::Nat => LSort::Nat,
        SortHint::Suffix(SuffixSort::Msg) => LSort::Msg,
        SortHint::Suffix(SuffixSort::Pub) => LSort::Pub,
        SortHint::Suffix(SuffixSort::Fresh) => LSort::Fresh,
        SortHint::Suffix(SuffixSort::Node) => LSort::Node,
        SortHint::Suffix(SuffixSort::Nat) => LSort::Nat,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};

    fn node(name: &str, idx: u64) -> LVar { LVar::new(name, LSort::Node, idx) }

    #[test]
    fn rename_idempotent_on_empty_system() {
        let mut sys = System::empty();
        rename_precise_system(&mut sys);
        assert_eq!(sys, System::empty());
    }

    #[test]
    fn rename_normalises_node_ids() {
        // Two systems that differ only by node-id indices should compare
        // equal after rename_precise_system.
        use crate::constraint::constraints::{LessAtom, Reason};

        let mk_sys = |i_a: u64, i_b: u64| -> System {
            let mut sys = System::empty();
            sys.less_atoms.push(LessAtom::new(
                node("i", i_a), node("i", i_b), Reason::Fresh,
            ));
            sys
        };
        let mut a = mk_sys(0, 5);
        let mut b = mk_sys(7, 99);
        rename_precise_system(&mut a);
        rename_precise_system(&mut b);
        assert_eq!(a.less_atoms[0].smaller, b.less_atoms[0].smaller);
        assert_eq!(a.less_atoms[0].larger,  b.less_atoms[0].larger);
        // The two distinct node names should still differ.
        assert_ne!(a.less_atoms[0].smaller, a.less_atoms[0].larger);
    }
}
