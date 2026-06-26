//! Port of `Term.LTerm.renamePrecise` applied to a `System`.
//!
//! Haskell `cleanup` (ProofMethod.hs):
//! ```haskell
//! cleanup s = L.set sSubst emptySubst (Precise.evalFresh (renamePrecise s) Precise.nothingUsed)
//! ```
//!
//! `renamePrecise` walks every free `LVar` in a value in a deterministic
//! traversal order and rebinds each *unique* `LVar` to a freshly-allocated
//! `LVar` keyed by name. The result is canonical for two values that differ
//! only by variable indices. `process` (ProofMethod.hs) relies on that
//! canonical form when it `removeRedundantCases`-collapses variant-divergent
//! case maps and when the `Simplify` method compares `sys' /= cleanup sys`;
//! note `M.fromListWith (error "case names not unique")` there *errors* on a
//! duplicate case name rather than deduping.
//!
//! In Rust we don't have a single `mapFrees` typeclass that covers `System`,
//! so we walk each field by hand. The walk-order mirrors
//! `Reduction::subst_system_once` so any future cross-checks stay aligned.

use tamarin_utils::FastMap;

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
    // Rewrites every free LVar through a deterministic alpha-rename;
    // the resulting max-var-idx is almost always smaller.  Invalidate.
    sys.invalidate_max_var_idx_cache();
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
    // in lockstep: formulas must be visited before goals so that a free
    // LVar shared between a formula and a goal Disj is bound to the same
    // fresh idx HS would assign, otherwise the two become distinct LVars.
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
    // HS-faithful: `instance HasFrees (S.Set a)` (Term/LTerm.hs:824-827)
    // walks the set via `foldMap (foldFrees f)` — i.e. ascending Ord
    // order.  HS's `_sEdges` / `_sLessAtoms` / `_sSubtermStore` fields
    // are `S.Set` (System.hs:385-388 + SubtermStore.hs:546-548) and HS
    // visits them sorted by their derived `Ord`.  RS's `Vec` is in
    // insertion order, which DIVERGES from HS for `requiresKU`-driven
    // Less-atom inserts whose new vk-LVars get appended later but sort
    // earlier by `(smaller, larger)` than older atoms.  Sort copies here
    // ONLY for the rename-precise walk so the per-name "vk" counter
    // assigns canonical idxs in HS Set-order — matching HS's
    // `evalFresh ... nothingUsed`-canonicalised numbering exactly —
    // without touching the live `less_atoms` / `edges` Vec used
    // elsewhere.
    let mut edges_sorted: Vec<&crate::constraint::constraints::Edge>
        = sys.edges.iter().collect();
    edges_sorted.sort();
    for e in edges_sorted {
        state.import(&e.src.0);
        state.import(&e.tgt.0);
    }
    let mut less_sorted: Vec<&crate::constraint::constraints::LessAtom>
        = sys.less_atoms.iter().collect();
    less_sorted.sort();
    for la in less_sorted {
        state.import(&la.smaller);
        state.import(&la.larger);
    }
    if let Some(la) = &sys.last_atom { state.import(la); }
    // HS `HasFrees SubtermStore` (SubtermStore.hs:546-548) walks
    // `negSt <> st <> solvedSt`; each summand is a `S.Set` — sorted.
    // `neg_subterms` (negSt) must be visited FIRST to match HS order.
    // HS `neg_subterms` is `S.Set (LNTerm, LNTerm)` — sorted by pair Ord.
    let mut neg_sorted: Vec<&(tamarin_term::lterm::LNTerm, tamarin_term::lterm::LNTerm)>
        = sys.subterm_store.neg_subterms.iter().collect();
    neg_sorted.sort();
    for (s, b) in neg_sorted {
        s.for_each_free(&mut |v| { state.import(v); });
        b.for_each_free(&mut |v| { state.import(v); });
    }
    // SubtermConstraint isn't `Ord` in RS so sort by `(small, big)`
    // which mirrors HS's derived ordering on the analogous field pair.
    let mut sub_sorted: Vec<&crate::tools::subterm_store::SubtermConstraint>
        = sys.subterm_store.subterms.iter().collect();
    sub_sorted.sort_by(|a, b| (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    for c in sub_sorted {
        c.small.for_each_free(&mut |v| { state.import(v); });
        c.big.for_each_free(&mut |v| { state.import(v); });
    }
    let mut solved_sorted: Vec<&crate::tools::subterm_store::SubtermConstraint>
        = sys.subterm_store.solved_subterms.iter().collect();
    solved_sorted.sort_by(|a, b| (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    for c in solved_sorted {
        c.small.for_each_free(&mut |v| { state.import(v); });
        c.big.for_each_free(&mut |v| { state.import(v); });
    }
    // eq_store.subst: visit keys (dom) and values (range).  RS's
    // `Subst` is `BTreeMap`-backed, so `to_list()` already returns
    // pairs in ascending-key order — matches HS's `HasFrees (LSubst c)
    // = foldFrees f . sMap` walking `M.Map LVar Term` ascending
    // (SubstVFree.hs:221).
    for (k, t) in sys.eq_store.subst.to_list() {
        state.import(&k);
        t.for_each_free(&mut |v| { state.import(v); });
    }
    // eq_store.conj: HS-faithful `HasFrees (SubstVFresh n LVar)` only
    // walks DOMAIN (keys), NOT values (SubstVFresh.hs:196-202).  This
    // preserves the witness idxs in values — crucial for
    // sort-discriminating across variants at perform_split.
    //
    // The outer container `Conj (SplitId, S.Set LNSubstVFresh)`
    // (EquationStore.hs:118) is a `Conj`-list (insertion order — match
    // with RS's `Vec<EqDisj>`).  The INNER `S.Set LNSubstVFresh` is Ord
    // ascending — sort to match.
    for d in &sys.eq_store.conj {
        let mut substs_sorted: Vec<&tamarin_term::subst_vfresh::SubstVFresh<tamarin_term::lterm::Name, LVar>>
            = d.substs.iter().collect();
        substs_sorted.sort();
        for s in substs_sorted {
            for (k, _t) in s.to_list() {
                state.import(&k);
                // Note: value vars NOT imported (HS-faithful).
            }
        }
    }
    // HS-faithful: `_sFormulas` / `_sSolvedFormulas` / `_sLemmas` are
    // `S.Set LNGuarded` (System.hs:390-392), walked via `HasFrees (S.Set
    // a) = foldMap (foldFrees f)` in Ord-ascending.  RS's
    // `Vec<Guarded>` is in insertion order — sort via the existing
    // `cmp_guarded` helper (guarded.rs:67) which mirrors HS's derived
    // `Ord Guarded` (Guarded.hs:121-129).
    let mut formulas_sorted: Vec<&crate::guarded::Guarded>
        = sys.formulas.iter().collect();
    formulas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for f in formulas_sorted { guarded_for_each_free(f, &mut |v| { state.import(v); }); }
    let mut solved_formulas_sorted: Vec<&crate::guarded::Guarded>
        = sys.solved_formulas.iter().collect();
    solved_formulas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for f in solved_formulas_sorted { guarded_for_each_free(f, &mut |v| { state.import(v); }); }
    let mut lemmas_sorted: Vec<&crate::guarded::Guarded>
        = sys.lemmas.iter().collect();
    lemmas_sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    for f in lemmas_sorted { guarded_for_each_free(f, &mut |v| { state.import(v); }); }
    // HS-faithful: `_sGoals` is `M.Map Goal GoalStatus` (System.hs:393),
    // walked via `HasFrees (M.Map k v) = M.foldrWithKey combine`
    // (Term/LTerm.hs:829-836) in ascending key order (`Ord Goal`).
    // `goal_cmp` matches HS's derived `Ord Goal`
    // (System/Constraints.hs:156-168); see
    // `goal_cmp_tag_order_matches_haskell_declaration` test in goals.rs.
    let mut goals_sorted: Vec<&(Goal, crate::constraint::system::GoalStatus)>
        = sys.goals.iter().collect();
    goals_sorted.sort_by(|a, b|
        crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
    for (g, _) in goals_sorted {
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
            (old.name.to_string(), old.idx),
            tamarin_parser::ast::Term::Var(tamarin_parser::ast::VarSpec {
                name: new.name.to_string(),
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
    //
    // HS-faithful: `mapFrees (M.Map NodeId RuleACInst)`
    // = `fmap M.fromList . mapFrees f . M.toList` (Term/LTerm.hs:836).
    // `M.fromList` builds a Map keyed by Ord NodeId, so post-rename the
    // entries land in ascending NEW NodeId order.  Without this sort,
    // RS's `Vec<(NodeId, _)>` keeps the pre-rename insertion order — which
    // diverges from HS for any downstream consumer that walks `sys.nodes`
    // in storage order rather than re-sorting (most do their own sort, but
    // some iterate directly).  Mirror HS by sorting here.
    let nodes = std::sync::Arc::unwrap_or_clone(std::mem::take(&mut sys.nodes));
    let mut renamed: Vec<(crate::constraint::constraints::NodeId, crate::rule::RuleACInst)>
        = nodes.into_iter().map(|(id, rule)| {
            let new_id = map_var(id);
            let new_rule = rule.map_free(&mut |v| map_var(v));
            (new_id, new_rule)
        }).collect();
    renamed.sort_by(|a, b| a.0.cmp(&b.0));
    sys.nodes = std::sync::Arc::new(renamed);

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
    //
    // HS-faithful dedup post-rename: HS's `sLessAtoms :: Set LessAtom`
    // is reconstructed via `S.map (apply subst)` on every rewrite,
    // collapsing duplicates whose images coincide.  Mirror by deduping
    // after the in-place rename.  See `subst_system_once`'s comment for
    // detailed rationale.
    // HS `mapFrees (S.Set LessAtom)`: sort + dedup post-rename
    // (Term/LTerm.hs:827 `fmap S.fromList . mapFrees f . S.toList`).
    let mut new_less: Vec<crate::constraint::constraints::LessAtom>
        = Vec::with_capacity(sys.less_atoms.len());
    for la in std::mem::take(&mut sys.less_atoms) {
        let mut la = la;
        la.smaller = map_var(la.smaller.clone());
        la.larger  = map_var(la.larger.clone());
        new_less.push(la);
    }
    // Sort + dedup (O(n log n)), matching HS's `S.fromList` over the renamed
    // set rather than an O(n^2) membership scan.
    new_less.sort();
    new_less.dedup();
    sys.less_atoms = new_less;

    // 5. Goals — per-variant rewrite.
    let goals = std::sync::Arc::unwrap_or_clone(std::mem::take(&mut sys.goals));
    let apply_term = |t: LNTerm| -> LNTerm {
        tamarin_term::subst::apply_vterm(&term_subst, t)
    };
    let apply_fact = |fa: crate::fact::LNFact| -> crate::fact::LNFact {
        crate::fact::Fact {
            tag: fa.tag,
            annotations: fa.annotations,
            terms: fa.terms.into_iter().map(&apply_term).collect(),
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
        new_goals.push((g2, st));
    }
    // HS-faithful: `mapFrees (M.Map Goal GoalStatus)`
    // = `fmap M.fromList . mapFrees f . M.toList` (Term/LTerm.hs:836).
    // `M.fromList` builds a Map keyed by Ord Goal, so post-rename the
    // entries land in ascending NEW Goal order.
    //
    // Sort + dedup (O(n log n)) instead of an O(n^2) membership scan. We
    // dedup on structural `Goal` equality (the old `any(eg == &g2)`
    // relation) — NOT on `goal_cmp == Equal`, because `goal_cmp` orders
    // Disj goals by len + canonical string and would over-collapse.
    new_goals.sort_by(|a, b|
        crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
    new_goals.dedup_by(|a, b| a.0 == b.0);
    sys.goals = std::sync::Arc::new(new_goals);

    // 6. Formulas / solved / lemmas — via parser-level VarSubst.
    //
    // HS-faithful: `_sFormulas` / `_sSolvedFormulas` / `_sLemmas` are
    // `S.Set LNGuarded`. `mapFrees (S.Set a) = fmap S.fromList . mapFrees
    // f . S.toList` (Term/LTerm.hs:827) — rebuilds the set after mapping,
    // so post-rename entries are sorted by NEW Ord Guarded AND
    // collision-deduped.  Mirror by sorting+deduping after the in-place
    // rename: post-rename two formulas that became equal collapse.
    if !formula_subst.is_empty() {
        let sort_dedup_guarded = |v: &mut Vec<crate::guarded::Guarded>, sub: &VarSubst| {
            for f in v.iter_mut() {
                *f = subst_guarded(f, sub);
            }
            v.sort_by(crate::guarded::cmp_guarded);
            v.dedup_by(|a, b| crate::guarded::cmp_guarded(a, b)
                == std::cmp::Ordering::Equal);
        };
        sort_dedup_guarded(&mut sys.formulas, &formula_subst);
        sort_dedup_guarded(&mut sys.solved_formulas, &formula_subst);
        sort_dedup_guarded(&mut sys.lemmas, &formula_subst);
    }

    // 7. eq_store — rewrite the subst (dom + range) and the conj.
    let old_subst = std::mem::replace(
        &mut sys.eq_store_mut().subst,
        crate::tools::equation_store::LNSubst::empty(),
    );
    let pairs: Vec<(LVar, LNTerm)> = old_subst.to_list().into_iter()
        .map(|(k, v)| (map_var(k), apply_term(v)))
        .collect();
    sys.eq_store_mut().subst = Subst::from_list(pairs);

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
    // witness idxs in VALUES.  This preserves the variant witness idxs at
    // perform_split time — which is what gives HS the sort-discriminating
    // idx differences across variants.
    for d in sys.eq_store_mut().conj.iter_mut() {
        for s in d.substs.iter_mut() {
            let pairs: Vec<(LVar, LNTerm)> = s.to_list().into_iter()
                .map(|(k, v)| (map_var(k), v))  // keep VALUE unchanged
                .collect();
            *s = tamarin_term::subst_vfresh::SubstVFresh::from_list(pairs);
        }
    }

    // 8. Subterm store.
    //
    // HS-faithful: `_sSubtermStore` summands are `S.Set` (SubtermStore.hs
    // `Set SubtermD` for both pos and neg).  `mapFrees (S.Set a) =
    // fmap S.fromList . mapFrees f . S.toList` — sort + dedup post-rename.
    for c in sys.subterm_store_mut().subterms.iter_mut() {
        c.small = apply_term(c.small.clone());
        c.big = apply_term(c.big.clone());
    }
    sys.subterm_store_mut().subterms.sort_by(|a, b|
        (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    sys.subterm_store_mut().subterms.dedup_by(|a, b|
        (&a.small, &a.big) == (&b.small, &b.big));
    for c in sys.subterm_store_mut().solved_subterms.iter_mut() {
        c.small = apply_term(c.small.clone());
        c.big = apply_term(c.big.clone());
    }
    sys.subterm_store_mut().solved_subterms.sort_by(|a, b|
        (&a.small, &a.big).cmp(&(&b.small, &b.big)));
    sys.subterm_store_mut().solved_subterms.dedup_by(|a, b|
        (&a.small, &a.big) == (&b.small, &b.big));
    // negSubterms are mapped too; oldNegSubterms are NOT (HS mapFrees
    // keeps `oldNegSt` with `pure` — SubtermStore.hs:550-555).
    for p in sys.subterm_store_mut().neg_subterms.iter_mut() {
        p.0 = apply_term(p.0.clone());
        p.1 = apply_term(p.1.clone());
    }
    sys.subterm_store_mut().neg_subterms.sort();
    sys.subterm_store_mut().neg_subterms.dedup();
}

// =============================================================================
// Helpers
// =============================================================================

struct RenameState {
    fresh: PreciseFreshState,
    // Lookup-only: keyed by the original `LVar`, queried via
    // `contains_key`/`insert`, and the eventual `into_map` is consumed
    // only by `Subst::from_list` (a `BTreeMap`, re-sorted) and a
    // distinct-key `VarSubst` applied by lookup — so iteration order is
    // never observed.
    map: FastMap<LVar, LVar>,
}

impl RenameState {
    fn new() -> Self {
        RenameState { fresh: PreciseFreshState::nothing_used(), map: FastMap::default() }
    }
    /// `importBinding`: idempotent — first call for `v` allocates a fresh
    /// LVar keyed by `v.name`; later calls return the same binding.
    fn import(&mut self, v: &LVar) {
        if self.map.contains_key(v) { return; }
        let idx = self.fresh.fresh_ident(&v.name);
        let new_v = LVar { name: v.name, sort: v.sort, idx };
        self.map.insert(v.clone(), new_v);
    }
    fn into_map(self) -> FastMap<LVar, LVar> { self.map }
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
            // HS `Traversable ProtoAtom` visits the timepoint BEFORE the
            // fact: `traverse f (Action i fa) = Action <$> f i <*> traverse f fa`
            // (Atom.hs).  renamePrecise allocates fresh per-name indices
            // in visit order, so the timepoint must be walked first to
            // match HS's idx assignment.
            term_for_each_free(t, f);
            for arg in &fa.args { term_for_each_free(arg, f); }
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
            f(&LVar { name: tamarin_term::intern::intern_str(v.name.as_str()), sort, idx: v.idx });
        }
        GTerm::Var(BVar::Bound(_)) => {}
        GTerm::PubLit(_) | GTerm::FreshLit(_) | GTerm::NatLit(_)
        | GTerm::Number(_) | GTerm::NumberOne | GTerm::NatOne | GTerm::DhNeutral => {}
        GTerm::App(_, args) | GTerm::Pair(args) => {
            for a in args.iter() { term_for_each_free(a, f); }
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
