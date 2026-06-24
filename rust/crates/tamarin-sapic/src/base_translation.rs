//! Port of `Sapic.Basetranslation` (`lib/sapic/src/Sapic/Basetranslation.hs`)
//! for the CORE LINEAR subset:
//!   - `baseInit`       (Basetranslation.hs:312-318)
//!   - `baseTransNull`  (Basetranslation.hs:81)
//!   - `baseTransAction` New (103) / Event (197) / plain ChOut (155) / null-chan
//!   - `baseRestr`      (449-485) — the always-on `single_session` restriction.
//!
//! Combinators, channels-with-secret, locks, inserts, lookups, replication,
//! reliable channels and progress are deferred to Phase 2+.

use std::collections::BTreeSet;

use tamarin_term::lterm::{LVar, LNTerm};
use tamarin_term::vterm::{Lit, VTerm};

use tamarin_theory::sapic::{SapicAction, SapicLVar, SapicTerm, ProcessPosition};

use crate::annotation::ProcessAnnotation;
use crate::facts::{
    AnnotatedRule, RulePosition, SpecialPosition, StateKind, TransAction, TransFact,
};

/// A single translation "rule body": `(prems, acts, concs, restr)`.
/// HS `([TransFact],[TransAction],[TransFact],[SyntacticLNFormula])`; the
/// linear subset never emits an embedded restriction, so `restr` is `Vec<()>`.
pub type RuleBody = (Vec<TransFact>, Vec<TransAction>, Vec<TransFact>, Vec<()>);

/// `baseTransNull` (Basetranslation.hs:81):
///   `[([State LState p tildex], [], [], [])]`
pub fn base_trans_null(p: &ProcessPosition, tildex: &BTreeSet<LVar>) -> Vec<RuleBody> {
    let st = TransFact::State(StateKind::LState, p.clone(), tildex.iter().cloned().collect());
    vec![(vec![st], vec![], vec![], vec![])]
}

/// `lol`-erase: HS works over `LNTerm` (untyped) for the rule facts; the
/// translation calls `toLNTerm` / `toLVar` on SAPIC terms.  Convert a typed
/// SAPIC term to a plain `LNTerm` (drop the type tag).
pub fn to_ln_term(t: &SapicTerm) -> LNTerm {
    match t {
        VTerm::Lit(Lit::Var(sv)) => VTerm::Lit(Lit::Var(sv.var.clone())),
        VTerm::Lit(Lit::Con(c)) => VTerm::Lit(Lit::Con(c.clone())),
        VTerm::App(sym, args) => {
            let new_args: Vec<LNTerm> = args.iter().map(to_ln_term).collect();
            use tamarin_term::function_symbols::FunSym;
            match sym {
                FunSym::Ac(o) => tamarin_term::term::f_app_ac(*o, new_args),
                FunSym::C(o) => tamarin_term::term::f_app_c(*o, new_args),
                FunSym::NoEq(o) => tamarin_term::term::f_app_no_eq(o.clone(), new_args),
                FunSym::List => tamarin_term::term::f_app_list(new_args),
            }
        }
    }
}

/// `toLNFact` over a SAPIC fact (drop type tags from every term).
pub fn to_ln_fact(f: &tamarin_theory::sapic::SapicLNFact) -> tamarin_theory::fact::LNFact {
    let terms = f.terms.iter().map(to_ln_term).collect();
    let mut nf = tamarin_theory::fact::Fact::new(f.tag.clone(), terms);
    nf = nf.with_annotations(f.annotations.clone());
    nf
}

/// `toLVar v = slvar v`.
pub fn to_lvar(v: &SapicLVar) -> LVar {
    v.var.clone()
}

/// `baseTransAction` (Basetranslation.hs:94-205) — linear subset.  Returns the
/// rule bodies and the updated `tildex`.  `needs_ass_immediate` is the
/// `needsInEvRes` flag (false for typing2, which has no lemma needing
/// `in_event`); when false, `Event` emits NO extra `EventEmpty` action.
pub fn base_trans_action(
    _async_channels: bool,
    needs_ass_immediate: bool,
    ac: &SapicAction<SapicLVar>,
    _an: &ProcessAnnotation<LVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<(Vec<RuleBody>, BTreeSet<LVar>), String> {
    // `def_state = State LState p tildex`
    let def_state = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p.clone(), tx.iter().cloned().collect())
    };
    // `def_state' tx = State LState (p++[1]) tx`
    let mut p1 = p.clone();
    p1.push(1);
    let def_state_next = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p1.clone(), tx.iter().cloned().collect())
    };

    match ac {
        // (Rep): replication (Basetranslation.hs:99-102).  Two rules:
        //   [([def_state], [], [State PSemiState (p++[1]) tildex], []),
        //    ([State PSemiState (p++[1]) tildex], [], [def_state' tildex], [])]
        // The first consumes the entering linear state and produces a
        // PERSISTENT semistate (so it can fire arbitrarily often); the second
        // turns each persistent-semistate instance back into a fresh linear
        // `def_state'` for the replicated body.  `tildex` is unchanged.
        SapicAction::Rep => {
            let semistate = TransFact::State(
                StateKind::PSemiState,
                p1.clone(),
                tildex.iter().cloned().collect(),
            );
            let body1: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![semistate.clone()],
                vec![],
            );
            let body2: RuleBody = (
                vec![semistate],
                vec![],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body1, body2], tildex.clone()))
        }
        // (New v): `tx' = toLVar v `insert` tildex`
        //   [([def_state, Fr (toLVar v)], [], [def_state' tx'], [])]
        SapicAction::New(v) => {
            let lv = to_lvar(v);
            let mut tx2 = tildex.clone();
            tx2.insert(lv.clone());
            let body: RuleBody = (
                vec![def_state(tildex), TransFact::Fr(lv)],
                vec![],
                vec![def_state_next(&tx2)],
                vec![],
            );
            Ok((vec![body], tx2))
        }
        // (Event f): `[([def_state], TamarinAct f : [EventEmpty | needsAss], [def_state' tildex], [])]`
        SapicAction::Event(f) => {
            let lnf = to_ln_fact(f);
            let mut acts = vec![TransAction::TamarinAct(lnf)];
            if needs_ass_immediate {
                acts.push(TransAction::EventEmpty);
            }
            let body: RuleBody = (
                vec![def_state(tildex)],
                acts,
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (ChOut Nothing t): `[([def_state], [], [def_state' tildex, Out t], [])]`
        SapicAction::ChOut { chan: None, msg } => {
            let t = to_ln_term(msg);
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state_next(tildex), TransFact::Out(t)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // ChOut with a channel, ChIn, Insert/Delete/Lock/Unlock, MSR, calls:
        // Phase 2+.
        other => Err(format!(
            "baseTransAction: action not yet ported (Phase 2+): {other:?}"
        )),
    }
}

/// The result of translating a combinator: `(rules, tildex_l, Option<tildex_r>)`
/// — HS `TranslationResultComb` (Basetranslation.hs:51).  `tildex_r` is `None`
/// only when the combinator has no right child to translate (e.g. `let` without
/// an else branch — deferred); for the in-scope combinators it is always
/// `Some(...)`.
pub type CombResult = (Vec<RuleBody>, BTreeSet<LVar>, Option<BTreeSet<LVar>>);

/// `baseTransComb` (Basetranslation.hs:226-306) — the in-scope subset:
/// `Parallel`, `NDC`, `CondEq`.  `Cond` (with a formula), `Lookup` and `Let`
/// are deferred (Phase 2+/3).
pub fn base_trans_comb(
    c: &tamarin_theory::sapic::ProcessCombinator<SapicLVar>,
    _an: &ProcessAnnotation<LVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<CombResult, String> {
    use tamarin_theory::sapic::ProcessCombinator as PC;

    // `def_state = State LState p tildex`
    let def_state = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p.clone(), tx.iter().cloned().collect())
    };
    // `def_state1 tx = State LState (p++[1]) tx`
    let mut p1 = p.clone();
    p1.push(1);
    let def_state1 = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p1.clone(), tx.iter().cloned().collect())
    };
    // `def_state2 tx = State LState (p++[2]) tx`
    let mut p2 = p.clone();
    p2.push(2);
    let def_state2 = |tx: &BTreeSet<LVar>| {
        TransFact::State(StateKind::LState, p2.clone(), tx.iter().cloned().collect())
    };

    match c {
        // Parallel (Basetranslation.hs:228-230):
        //   ([([def_state], [], [def_state1 tildex, def_state2 tildex], [])],
        //    tildex, Just tildex)
        PC::Parallel => {
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state1(tildex), def_state2(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone(), Some(tildex.clone())))
        }
        // NDC (Basetranslation.hs:231-233): no rules of its own; both children
        // share the parent's position (handled by `substStatePos` in `gen`).
        //   ([], tildex, Just tildex)
        PC::Ndc => Ok((vec![], tildex.clone(), Some(tildex.clone()))),
        // CondEq (Basetranslation.hs:243-251):
        //   let fa = toLNFact (protoFact Linear "Eq" [t1, t2]) in
        //   if vars_f ⊆ tildex then
        //     ([([def_state], [PredicateA fa], [def_state1 tildex], []),
        //       ([def_state], [NegPredicateA fa], [def_state2 tildex], [])],
        //      tildex, Just tildex)
        //   else throw (WFUnbound (vars_f \\ tildex))
        PC::CondEq(t1, t2) => {
            let fa = eq_fact(t1, t2);
            // `vars_f = fromList $ getFactVariables fa` — the variables in the
            // (untyped) Eq fact.
            let vars_f = fact_vars(&fa);
            if !vars_f.is_subset(tildex) {
                let unbound: Vec<LVar> = vars_f.difference(tildex).cloned().collect();
                return Err(format!(
                    "process not well-formed: unbound variables in conditional: {unbound:?}"
                ));
            }
            let body_eq: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::PredicateA(fa.clone())],
                vec![def_state1(tildex)],
                vec![],
            );
            let body_neq: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::NegPredicateA(fa)],
                vec![def_state2(tildex)],
                vec![],
            );
            Ok((
                vec![body_eq, body_neq],
                tildex.clone(),
                Some(tildex.clone()),
            ))
        }
        PC::Cond(_) => Err(
            "baseTransComb: conditional with a formula not yet ported (Phase 2+)".to_string(),
        ),
        PC::Lookup(_, _) => {
            Err("baseTransComb: lookup not yet ported (Phase 3 — state)".to_string())
        }
        PC::Let { .. } => {
            Err("baseTransComb: let-binding not yet ported (Phase 2+)".to_string())
        }
    }
}

/// `toLNFact (protoFact Linear "Eq" [t1, t2])` (Basetranslation.hs:244): build
/// the `Eq( t1, t2 )` linear fact over the type-erased terms.
fn eq_fact(t1: &SapicTerm, t2: &SapicTerm) -> tamarin_theory::fact::LNFact {
    use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
    let terms = vec![to_ln_term(t1), to_ln_term(t2)];
    Fact::new(FactTag::Proto(Multiplicity::Linear, "Eq".to_string(), 2), terms)
}

/// `fromList $ getFactVariables fa` — the set of variables occurring in a fact.
fn fact_vars(f: &tamarin_theory::fact::LNFact) -> BTreeSet<LVar> {
    use tamarin_term::vterm::{Lit, VTerm};
    fn collect(t: &LNTerm, out: &mut BTreeSet<LVar>) {
        match t {
            VTerm::Lit(Lit::Var(v)) => {
                out.insert(v.clone());
            }
            VTerm::Lit(_) => {}
            VTerm::App(_, args) => {
                for a in args.iter() {
                    collect(a, out);
                }
            }
        }
    }
    let mut out = BTreeSet::new();
    for t in &f.terms {
        collect(t, &mut out);
    }
    out
}

/// `baseInit` (Basetranslation.hs:312-318): the `Init` rule plus the empty
/// initial `tildex`.
///   `[AnnotatedRule (Just "Init") anP (Right InitPosition) [] [InitEmpty]
///       [State LState [] empty] [] 0]`
pub fn base_init(
    an_proc: &tamarin_theory::sapic::Process<ProcessAnnotation<LVar>, SapicLVar>,
) -> (Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, BTreeSet<LVar>) {
    let rule = AnnotatedRule {
        process_name: Some("Init".to_string()),
        process: an_proc.clone(),
        position: RulePosition::Special(SpecialPosition::InitPosition),
        prems: vec![],
        acts: vec![TransAction::InitEmpty],
        concs: vec![TransFact::State(StateKind::LState, vec![], vec![])],
        restr: vec![],
        index: 0,
    };
    (vec![rule], BTreeSet::new())
}

// =============================================================================
// baseRestr — the always-on `single_session` restriction (Basetranslation.hs)
// =============================================================================

/// The hardcoded text of `resSingleSession` (Basetranslation.hs:361-364).
///
/// HS parses this string with `parseRestriction` (`toEx`).  We instead build
/// the restriction directly as a parser-AST [`tamarin_parser::ast::Restriction`]
/// so it flows through the existing restriction renderer / solver, which is
/// what `translate` injects into the theory.  The rendered output is
/// byte-identical to what HS emits for `restriction single_session`.
pub fn single_session_restriction() -> tamarin_parser::ast::Restriction {
    use tamarin_parser::ast as p;
    // Formula: ∀ #i #j. ((Init( ) @ #i) ∧ (Init( ) @ #j)) ⇒ (#i = #j)
    //   = All #i #j. Init()@i & Init()@j ==> #i=#j
    let tvar = |name: &str| p::VarSpec {
        name: name.into(),
        idx: 0,
        sort: p::SortHint::Node,
        typ: None,
    };
    let init_at = |tv: &str| -> p::Formula {
        p::Formula::Atom(p::Atom::Action(
            p::Fact {
                persistent: false,
                name: "Init".into(),
                args: vec![],
                annotations: vec![],
            },
            p::Term::Var(tvar(tv)),
        ))
    };
    let body = p::Formula::Implies(
        Box::new(p::Formula::And(
            Box::new(init_at("i")),
            Box::new(init_at("j")),
        )),
        Box::new(p::Formula::Atom(p::Atom::Eq(
            p::Term::Var(tvar("i")),
            p::Term::Var(tvar("j")),
        ))),
    );
    let formula = p::Formula::Forall(vec![tvar("i"), tvar("j")], Box::new(body));
    p::Restriction {
        name: "single_session".to_string(),
        formula,
        attributes: vec![],
    }
}

/// The two conditional-equality restrictions `predicate_eq` / `predicate_not_eq`
/// (Basetranslation.hs:427-436), added by `baseRestr` when the process
/// `contains isEq` (a `CondEq` combinator).  As with `single_session`, we build
/// them as parser-AST [`tamarin_parser::ast::Restriction`] so they render
/// byte-identically to HS's hand-written strings:
///   `predicate_eq:      "All #i a b. Pred_Eq(a,b)@i ==> a = b"`
///   `predicate_not_eq:  "All #i a b. Pred_Not_Eq(a,b)@i ==> not(a = b)"`
pub fn predicate_restrictions() -> Vec<tamarin_parser::ast::Restriction> {
    use tamarin_parser::ast as p;
    // `#i` is a node (timepoint) variable; `a`, `b` are message variables.
    let tvar = |name: &str| p::VarSpec {
        name: name.into(),
        idx: 0,
        sort: p::SortHint::Node,
        typ: None,
    };
    let mvar = |name: &str| p::VarSpec {
        name: name.into(),
        idx: 0,
        sort: p::SortHint::Untagged,
        typ: None,
    };
    let pred_at = |pname: &str| -> p::Formula {
        p::Formula::Atom(p::Atom::Action(
            p::Fact {
                persistent: false,
                name: pname.into(),
                args: vec![p::Term::Var(mvar("a")), p::Term::Var(mvar("b"))],
                annotations: vec![],
            },
            p::Term::Var(tvar("i")),
        ))
    };
    let eq_atom = p::Formula::Atom(p::Atom::Eq(
        p::Term::Var(mvar("a")),
        p::Term::Var(mvar("b")),
    ));

    // predicate_eq: All #i a b. Pred_Eq(a,b)@i ==> a = b
    let eq_body = p::Formula::Implies(
        Box::new(pred_at("Pred_Eq")),
        Box::new(eq_atom.clone()),
    );
    let eq_formula = p::Formula::Forall(
        vec![tvar("i"), mvar("a"), mvar("b")],
        Box::new(eq_body),
    );
    let predicate_eq = p::Restriction {
        name: "predicate_eq".to_string(),
        formula: eq_formula,
        attributes: vec![],
    };

    // predicate_not_eq: All #i a b. Pred_Not_Eq(a,b)@i ==> not(a = b)
    let neq_body = p::Formula::Implies(
        Box::new(pred_at("Pred_Not_Eq")),
        Box::new(p::Formula::Not(Box::new(eq_atom))),
    );
    let neq_formula = p::Formula::Forall(
        vec![tvar("i"), mvar("a"), mvar("b")],
        Box::new(neq_body),
    );
    let predicate_not_eq = p::Restriction {
        name: "predicate_not_eq".to_string(),
        formula: neq_formula,
        attributes: vec![],
    };

    vec![predicate_eq, predicate_not_eq]
}


#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_theory::sapic::ProcessCombinator;
    use tamarin_term::lterm::LSort;

    fn lv(name: &str, idx: u64) -> LVar {
        LVar::new(name, LSort::Msg, idx)
    }
    fn svar(name: &str) -> SapicTerm {
        VTerm::Lit(Lit::Var(SapicLVar::untyped(lv(name, 0))))
    }

    #[test]
    fn rep_emits_two_rules_with_persistent_semistate() {
        // pos = [1], tildex = {}.  baseTransAction Rep:
        //   [([State LState [1] {}], [], [State PSemiState [1,1] {}], []),
        //    ([State PSemiState [1,1] {}], [], [State LState [1,1] {}], [])]
        let an = ProcessAnnotation::<LVar>::empty();
        let p = vec![1i64];
        let tx = BTreeSet::new();
        let (bodies, tx2) =
            base_trans_action(false, false, &SapicAction::Rep, &an, &p, &tx).unwrap();
        assert_eq!(bodies.len(), 2);
        assert_eq!(tx2, tx); // tildex unchanged
        // First rule conclusion is a PERSISTENT semistate at [1,1].
        let (_, _, concs0, _) = &bodies[0];
        match &concs0[0] {
            TransFact::State(kind, pos, _) => {
                assert!(kind.is_semi_state());
                assert_eq!(kind.multiplicity(), tamarin_theory::fact::Multiplicity::Persistent);
                assert_eq!(pos, &vec![1, 1]);
            }
            _ => panic!("expected semistate conclusion"),
        }
        // Second rule premise is that same persistent semistate.
        let (prems1, _, concs1, _) = &bodies[1];
        assert!(matches!(&prems1[0], TransFact::State(k, _, _) if k.is_semi_state()));
        // ...and its conclusion is the linear def_state' at [1,1].
        match &concs1[0] {
            TransFact::State(kind, pos, _) => {
                assert!(!kind.is_semi_state());
                assert_eq!(pos, &vec![1, 1]);
            }
            _ => panic!("expected linear def_state' conclusion"),
        }
    }

    #[test]
    fn parallel_splits_into_two_states() {
        let an = ProcessAnnotation::<LVar>::empty();
        let p: Vec<i64> = vec![];
        let tx = BTreeSet::new();
        let (bodies, txl, txr) =
            base_trans_comb(&ProcessCombinator::Parallel, &an, &p, &tx).unwrap();
        assert_eq!(bodies.len(), 1);
        assert_eq!(txl, tx);
        assert_eq!(txr, Some(tx));
        let (_, _, concs, _) = &bodies[0];
        // Two conclusions: State_1 and State_2.
        assert_eq!(concs.len(), 2);
        assert!(matches!(&concs[0], TransFact::State(_, p, _) if p == &vec![1]));
        assert!(matches!(&concs[1], TransFact::State(_, p, _) if p == &vec![2]));
    }

    #[test]
    fn ndc_emits_no_rule() {
        let an = ProcessAnnotation::<LVar>::empty();
        let p: Vec<i64> = vec![];
        let tx = BTreeSet::new();
        let (bodies, txl, txr) =
            base_trans_comb(&ProcessCombinator::Ndc, &an, &p, &tx).unwrap();
        assert!(bodies.is_empty());
        assert_eq!(txl, tx);
        assert_eq!(txr, Some(tx));
    }

    #[test]
    fn condeq_emits_pred_and_negpred_arms() {
        // tildex must contain a and b for the wellformedness check to pass.
        let an = ProcessAnnotation::<LVar>::empty();
        let p: Vec<i64> = vec![];
        let mut tx = BTreeSet::new();
        tx.insert(lv("a", 0));
        tx.insert(lv("b", 0));
        let c = ProcessCombinator::CondEq(svar("a"), svar("b"));
        let (bodies, _, _) = base_trans_comb(&c, &an, &p, &tx).unwrap();
        assert_eq!(bodies.len(), 2);
        // Arm 0: PredicateA, conclusion State_1; arm 1: NegPredicateA, State_2.
        let (_, acts0, concs0, _) = &bodies[0];
        assert!(matches!(&acts0[0], TransAction::PredicateA(_)));
        assert!(matches!(&concs0[0], TransFact::State(_, p, _) if p == &vec![1]));
        let (_, acts1, concs1, _) = &bodies[1];
        assert!(matches!(&acts1[0], TransAction::NegPredicateA(_)));
        assert!(matches!(&concs1[0], TransFact::State(_, p, _) if p == &vec![2]));
    }

    #[test]
    fn condeq_unbound_var_errors() {
        // tildex empty → a, b unbound → WFUnbound error.
        let an = ProcessAnnotation::<LVar>::empty();
        let p: Vec<i64> = vec![];
        let tx = BTreeSet::new();
        let c = ProcessCombinator::CondEq(svar("a"), svar("b"));
        assert!(base_trans_comb(&c, &an, &p, &tx).is_err());
    }
}
