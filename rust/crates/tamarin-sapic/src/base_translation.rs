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

