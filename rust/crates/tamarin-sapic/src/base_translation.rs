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
/// 4th element carries the embedded restriction formulas (non-empty only for
/// the `if <formula>` arms — `Cond`), as parser-AST formulas.
pub type RuleBody = (
    Vec<TransFact>,
    Vec<TransAction>,
    Vec<TransFact>,
    Vec<tamarin_parser::ast::Formula>,
);

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
    an: &ProcessAnnotation<LVar>,
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
        // === Pure cell translation (Basetranslation.hs:155-174) ===
        // Gated on `an.pure_state`, which is only ever set when the
        // state-channel optimisation is enabled (`--translation-state-optimisation`
        // / `_stateChannelOpt`).  These guards MUST be checked BEFORE the classical
        // `Insert`/`Lock`/`Unlock` cases (HS guard order).
        //
        // (Insert t1 t2) | pureState, Just (AnVar v) <- an.unlock
        //   let tx' = v `insert` tildex in
        //   [([def_state, CellLocked t1 (varTerm v)], [],
        //     [def_state' tx', PureCell t1 t2], [])]
        SapicAction::Insert(t1, t2) if an.pure_state && an.unlock.is_some() => {
            let v = an.unlock.as_ref().unwrap().0.clone();
            let lt1 = to_ln_term(t1);
            let lt2 = to_ln_term(t2);
            let mut tx2 = tildex.clone();
            tx2.insert(v.clone());
            let body: RuleBody = (
                vec![
                    def_state(tildex),
                    TransFact::CellLocked(lt1.clone(), VTerm::Lit(Lit::Var(v))),
                ],
                vec![],
                vec![def_state_next(&tx2), TransFact::PureCell(lt1, lt2)],
                vec![],
            );
            Ok((vec![body], tx2))
        }
        // (Insert t1 t2) | pureState  (no unlock annotation — lone insert)
        //   [([def_state], [], [def_state' tildex, PureCell t1 t2], [])]
        SapicAction::Insert(t1, t2) if an.pure_state => {
            let lt1 = to_ln_term(t1);
            let lt2 = to_ln_term(t2);
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state_next(tildex), TransFact::PureCell(lt1, lt2)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Lock _) | pureState -> silent passthrough.
        //   [([def_state], [], [def_state' tildex], [])]
        SapicAction::Lock(_) if an.pure_state => {
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Unlock _) | pureState -> silent passthrough.
        SapicAction::Unlock(_) if an.pure_state => {
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }

        // === Classical state translation (Basetranslation.hs:177-194) ===
        //
        // (Insert t1 t2): `[([def_state], [InsertA t1 t2], [def_state' tildex], [])]`
        SapicAction::Insert(t1, t2) => {
            let lt1 = to_ln_term(t1);
            let lt2 = to_ln_term(t2);
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::InsertA(lt1, lt2)],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Delete t): `[([def_state], [DeleteA t], [def_state' tildex], [])]`
        SapicAction::Delete(t) => {
            let lt = to_ln_term(t);
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::DeleteA(lt)],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // (Lock t) | Just (AnVar v) <- an.lock (Basetranslation.hs:185-189):
        //   let tx' = v `insert` tildex in
        //   [([def_state, Fr v], [LockNamed t v, LockUnnamed t v], [def_state' tx'], [])]
        // (Lock _) | Nothing <- an.lock -> "Unannotated lock" error
        //   (Basetranslation.hs:190).
        SapicAction::Lock(t) => {
            let Some(an_v) = &an.lock else {
                return Err("baseTransAction: Unannotated lock".to_string());
            };
            let v = an_v.0.clone();
            let lt = to_ln_term(t);
            let mut tx2 = tildex.clone();
            tx2.insert(v.clone());
            let body: RuleBody = (
                vec![def_state(tildex), TransFact::Fr(v.clone())],
                vec![
                    TransAction::LockNamed(lt.clone(), v.clone()),
                    TransAction::LockUnnamed(lt, v),
                ],
                vec![def_state_next(&tx2)],
                vec![],
            );
            Ok((vec![body], tx2))
        }
        // (Unlock t) | Just (AnVar v) <- an.unlock (Basetranslation.hs:191-193):
        //   [([def_state], [UnlockNamed t v, UnlockUnnamed t v], [def_state' tildex], [])]
        // (Unlock _) | Nothing <- an.lock -> "Unannotated unlock" error
        //   (Basetranslation.hs:194).
        SapicAction::Unlock(t) => {
            let Some(an_v) = &an.unlock else {
                return Err("baseTransAction: Unannotated unlock".to_string());
            };
            let v = an_v.0.clone();
            let lt = to_ln_term(t);
            let body: RuleBody = (
                vec![def_state(tildex)],
                vec![
                    TransAction::UnlockNamed(lt.clone(), v.clone()),
                    TransAction::UnlockUnnamed(lt, v),
                ],
                vec![def_state_next(tildex)],
                vec![],
            );
            Ok((vec![body], tildex.clone()))
        }
        // ChOut with a channel, ChIn, MSR, calls: Phase 5+.
        other => Err(format!(
            "baseTransAction: action not yet ported (Phase 5+): {other:?}"
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
    an: &ProcessAnnotation<LVar>,
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
        // Cond f (Basetranslation.hs:234-242):
        //   let freevars_f = fromList (freesList f)
        //   if freevars_f ⊆ tildex then
        //     ([([def_state], [], [def_state1 tildex], [f]),
        //       ([def_state], [], [def_state2 tildex], [Not f])],
        //      tildex, Just tildex)
        //   else throw (WFUnbound (freevars_f \\ tildex))
        // The formula is the parser-AST `Cond` payload; the embedded restriction
        // flows through `lift_rule_restrictions` (HS `liftedAddProtoRule`).
        PC::Cond(f) => {
            // `freesList f` as LVars (the formula's free message/timepoint vars),
            // mapped to `LVar`s to compare against `tildex :: Set LVar`.
            let freevars_f = formula_free_lvars(f);
            if !freevars_f.is_subset(tildex) {
                let unbound: Vec<LVar> = freevars_f.difference(tildex).cloned().collect();
                return Err(format!(
                    "process not well-formed: unbound variables in conditional: {unbound:?}"
                ));
            }
            // then-arm carries `[f]`; else-arm carries `[Not f]`.
            let not_f = tamarin_parser::ast::Formula::Not(Box::new(f.clone()));
            let body_then: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state1(tildex)],
                vec![f.clone()],
            );
            let body_else: RuleBody = (
                vec![def_state(tildex)],
                vec![],
                vec![def_state2(tildex)],
                vec![not_f],
            );
            Ok((vec![body_then, body_else], tildex.clone(), Some(tildex.clone())))
        }
        // Pure cell Lookup (Basetranslation.hs:280-289), gated on
        //   pureState && Just (AnVar vs) <- an.unlock:
        //   let tx' = vs `insert` (v `insert` tildex) in
        //   ([([def_state, PureCell t (varTerm v), Fr vs], [],
        //      [def_state1 tx', CellLocked t (varTerm vs)], [])],
        //    tx', Just tildex)
        // (The right `IsNotSet` arm is commented out in HS — pure lookups have a
        // single arm.)
        PC::Lookup(t, v) if an.pure_state && an.unlock.is_some() => {
            let vs = an.unlock.as_ref().unwrap().0.clone();
            let lt = to_ln_term(t);
            let lv = to_lvar(v);
            let mut tx_prime = tildex.clone();
            tx_prime.insert(lv.clone());
            tx_prime.insert(vs.clone());
            let body: RuleBody = (
                vec![
                    def_state(tildex),
                    TransFact::PureCell(lt.clone(), VTerm::Lit(Lit::Var(lv))),
                    TransFact::Fr(vs.clone()),
                ],
                vec![],
                vec![
                    def_state1(&tx_prime),
                    TransFact::CellLocked(lt, VTerm::Lit(Lit::Var(vs))),
                ],
                vec![],
            );
            Ok((vec![body], tx_prime, Some(tildex.clone())))
        }
        // Classical Lookup (Basetranslation.hs:293-299):
        //   let tx' = v `insert` tildex
        //   ([([def_state], [IsIn t v], [def_state1 tx'], []),
        //     ([def_state], [IsNotSet t], [def_state2 tildex], [])],
        //    tx', Just tildex)
        PC::Lookup(t, v) => {
            let lt = to_ln_term(t);
            let lv = to_lvar(v);
            let mut tx_prime = tildex.clone();
            tx_prime.insert(lv.clone());
            let body_in: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::IsIn(lt.clone(), lv)],
                vec![def_state1(&tx_prime)],
                vec![],
            );
            let body_notset: RuleBody = (
                vec![def_state(tildex)],
                vec![TransAction::IsNotSet(lt)],
                vec![def_state2(tildex)],
                vec![],
            );
            Ok((vec![body_in, body_notset], tx_prime, Some(tildex.clone())))
        }
        PC::Let { .. } => {
            Err("baseTransComb: let-binding not yet ported (Phase 4+)".to_string())
        }
    }
}

/// `fromList (freesList f)` for a parser-AST formula — the formula's FREE
/// variables (vars not bound by an enclosing quantifier), as `LVar`s for the
/// WFUnbound `⊆ tildex` check (HS Basetranslation.hs:236).  Quantifier-bound
/// vars are excluded; the special timepoint vars carry the `Node` sort.
fn formula_free_lvars(f: &tamarin_parser::ast::Formula) -> BTreeSet<LVar> {
    use tamarin_parser::ast as p;
    fn sort_of(s: &p::SortHint) -> tamarin_term::lterm::LSort {
        use tamarin_term::lterm::LSort;
        match s {
            p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) => LSort::Fresh,
            p::SortHint::Pub | p::SortHint::Suffix(p::SuffixSort::Pub) => LSort::Pub,
            p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node) => LSort::Node,
            p::SortHint::Nat | p::SortHint::Suffix(p::SuffixSort::Nat) => LSort::Nat,
            p::SortHint::Msg | p::SortHint::Suffix(p::SuffixSort::Msg) | p::SortHint::Untagged => {
                LSort::Msg
            }
        }
    }
    fn collect_term(t: &p::Term, bound: &[String], out: &mut BTreeSet<LVar>) {
        match t {
            p::Term::Var(v) => {
                if !bound.iter().any(|n| n == &v.name) {
                    out.insert(LVar::new(v.name.clone(), sort_of(&v.sort), v.idx));
                }
            }
            p::Term::App(_, args) | p::Term::Pair(args) => {
                for a in args {
                    collect_term(a, bound, out);
                }
            }
            p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
                collect_term(a, bound, out);
                collect_term(b, bound, out);
            }
            p::Term::PatMatch(inner) => collect_term(inner, bound, out),
            _ => {}
        }
    }
    fn collect_atom(a: &p::Atom, bound: &[String], out: &mut BTreeSet<LVar>) {
        use p::Atom::*;
        match a {
            Eq(l, r) | Less(l, r) | LessMset(l, r) | Subterm(l, r) => {
                collect_term(l, bound, out);
                collect_term(r, bound, out);
            }
            Action(fa, t) => {
                for arg in &fa.args {
                    collect_term(arg, bound, out);
                }
                collect_term(t, bound, out);
            }
            Last(t) => collect_term(t, bound, out),
            Pred(fa) => {
                for arg in &fa.args {
                    collect_term(arg, bound, out);
                }
            }
        }
    }
    fn collect(f: &p::Formula, bound: &mut Vec<String>, out: &mut BTreeSet<LVar>) {
        use p::Formula::*;
        match f {
            True | False => {}
            Atom(a) => collect_atom(a, bound, out),
            Not(g) => collect(g, bound, out),
            And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b) => {
                collect(a, bound, out);
                collect(b, bound, out);
            }
            Forall(vs, body) | Exists(vs, body) => {
                let saved = bound.len();
                for v in vs {
                    bound.push(v.name.clone());
                }
                collect(body, bound, out);
                bound.truncate(saved);
            }
        }
    }
    let mut out = BTreeSet::new();
    let mut bound = Vec::new();
    collect(f, &mut bound, &mut out);
    out
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

/// The `set_in` / `set_notin` restrictions (Basetranslation.hs:332-359), added
/// by `baseRestr` (449-457) when the process `contains isLookup`.  HS hardcodes
/// these as restriction strings and parses them with `toEx`/`parseRestriction`;
/// we do the same with the RS `parse_formula_str` (so the rendered output is
/// byte-identical to HS's hand-written strings, and AC/sort handling matches the
/// parser path).  `has_delete` selects the full variants (the process also
/// `contains isDelete`) over the NoDelete variants.
pub fn state_restrictions(has_delete: bool) -> Vec<tamarin_parser::ast::Restriction> {
    use tamarin_parser::ast as p;
    // `parseRestriction`'s formula body, verbatim from Basetranslation.hs.
    let (set_in_src, set_notin_src) = if has_delete {
        (
            // resSetIn (Basetranslation.hs:333-338)
            "All x y #t3 . IsIn(x,y)@t3 ==>\n\
             (Ex #t2 . Insert(x,y)@t2 & #t2<#t3\n\
             & ( All #t1 . Delete(x)@t1 ==> (#t1<#t2 |  #t3<#t1))\n\
             & ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1))\n\
             )",
            // resSetNotIn (Basetranslation.hs:341-345)
            "All x #t3 . IsNotSet(x)@t3 ==>\n\
             (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )\n\
             | ( Ex #t1 .   Delete(x)@t1 & #t1<#t3\n\
             &  (All #t2 y . Insert(x,y)@t2 & #t2<#t3 ==>  #t2<#t1))",
        )
    } else {
        (
            // resSetInNoDelete (Basetranslation.hs:349-353)
            "All x y #t3 . IsIn(x,y)@t3 ==>\n\
             (Ex #t2 . Insert(x,y)@t2 & #t2<#t3\n\
             & ( All #t1 yp . Insert(x,yp)@t1 ==> (#t1<#t2 | #t1=#t2 | #t3<#t1))\n\
             )",
            // resSetNotInNoDelete (Basetranslation.hs:356-358)
            "All x #t3 . IsNotSet(x)@t3 ==>\n\
             (All #t1 y . Insert(x,y)@t1 ==>  #t3<#t1 )",
        )
    };
    let parse = |name: &str, src: &str| -> p::Restriction {
        let formula = tamarin_parser::parser::parse_formula_str(src)
            .unwrap_or_else(|e| panic!("Error parsing hard-coded restriction {name}: {e:?}"));
        p::Restriction { name: name.to_string(), formula, attributes: vec![] }
    };
    vec![parse("set_in", set_in_src), parse("set_notin", set_notin_src)]
}


// =============================================================================
// resLocking / resLockingPure (Basetranslation.hs:366-425)
// =============================================================================

/// `resLockingPOS` (Basetranslation.hs:368-376): the per-lock locking
/// restriction.  `LockPOS`/`UnlockPOS` are placeholder fact names that
/// `resLocking` rewrites to `Lock_<idx>`/`Unlock_<idx>` for the given lock var.
const RES_LOCKING_POS: &str = "All p pp l x lp #t1 #t3. LockPOS(p, l, x)@t1 & Lock(pp, lp, x)@t3 ==>\n\
        (#t1<#t3 & (Ex #t2. UnlockPOS(p, l, x)@t2 & #t1 < #t2 & #t2 < #t3\n\
                   & (All #t0 pp. Unlock(pp, l, x)@t0 ==> #t0 = #t2)\n\
                   & (All pp lpp #t0. Lock(pp, lpp, x)@t0 ==> #t0 < #t1 | #t0 = #t1 | #t2 < #t0)\n\
                   & (All pp lpp #t0. Unlock(pp, lpp, x)@t0 ==> #t0 < #t1 | #t2 < #t0 | #t2 = #t0 )))\n\
      | #t3<#t1 | #t1=#t3";

/// `resLockingPOSNoUnlock` (Basetranslation.hs:379-383): the locking
/// restriction for a lock with no matching unlock.
const RES_LOCKING_POS_NO_UNLOCK: &str = "All p pp l x lp #t1 #t3. LockPOS(p, l, x)@t1 & Lock(pp, lp, x)@t3 ==>\n\
        #t3<#t1 | #t1=#t3";

/// `resLocking hasUnlock v` (Basetranslation.hs:406-425): produce the
/// `locking_<idx v>` restriction by parsing `resLockingPOS` (or the NoUnlock
/// variant) and rewriting the `LockPOS`/`UnlockPOS` action facts to
/// `Lock_<idx>`/`Unlock_<idx>` (HS `mapAtoms subst`, with
/// `hardcode s = s ++ "_" ++ show (lvarIdx v)`).
pub fn res_locking(has_unlock: bool, v: &LVar) -> tamarin_parser::ast::Restriction {
    use tamarin_parser::ast as p;
    let src = if has_unlock { RES_LOCKING_POS } else { RES_LOCKING_POS_NO_UNLOCK };
    let mut formula = tamarin_parser::parser::parse_formula_str(src)
        .unwrap_or_else(|e| panic!("Error parsing hard-coded restriction locking: {e:?}"));
    let idx = v.idx;
    rename_lock_pos_atoms(&mut formula, idx);
    p::Restriction {
        name: format!("locking_{idx}"),
        formula,
        attributes: vec![],
    }
}

/// HS `subst` inside `resLocking` (Basetranslation.hs:414-422): rewrite the
/// `LockPOS` 3-ary action fact name to `Lock_<idx>` and `UnlockPOS` to
/// `Unlock_<idx>`.  Non-POS `Lock`/`Unlock` facts are left untouched.
fn rename_lock_pos_atoms(f: &mut tamarin_parser::ast::Formula, idx: u64) {
    use tamarin_parser::ast as p;
    fn walk_atom(a: &mut p::Atom, idx: u64) {
        if let p::Atom::Action(fact, _) = a {
            if fact.name == "LockPOS" && fact.args.len() == 3 {
                fact.name = format!("Lock_{idx}");
            } else if fact.name == "UnlockPOS" && fact.args.len() == 3 {
                fact.name = format!("Unlock_{idx}");
            }
        }
    }
    fn walk(f: &mut p::Formula, idx: u64) {
        use p::Formula::*;
        match f {
            True | False => {}
            Atom(a) => walk_atom(a, idx),
            Not(g) => walk(g, idx),
            And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b) => {
                walk(a, idx);
                walk(b, idx);
            }
            Forall(_, body) | Exists(_, body) => walk(body, idx),
        }
    }
    walk(f, idx);
}

/// `resLockingPure` (Basetranslation.hs:388-402): the two `locking1`/`locking2`
/// restrictions used only in the pure-state case (state-channel optimisation).
pub fn res_locking_pure() -> Vec<tamarin_parser::ast::Restriction> {
    use tamarin_parser::ast as p;
    let parse = |name: &str, src: &str| -> p::Restriction {
        let formula = tamarin_parser::parser::parse_formula_str(src)
            .unwrap_or_else(|e| panic!("Error parsing hard-coded restriction {name}: {e:?}"));
        p::Restriction { name: name.to_string(), formula, attributes: vec![] }
    };
    let locking1 = "All p l x #t1 pp lp #t2 #t3 . Lock(p,l,x)@t1 &  Lock(pp,lp,x)@t2\n\
                     & Unlock(p,l,x)@t3 & not(#t1=#t2)\n\
                   ==> (t2 < t1) | (t3 < t2)";
    let locking2 = "All p l x #t1 pp lp #t2 #t3 . Lock(p,l,x)@t1 &  Unlock(pp,lp,x)@t2\n\
           & Unlock(p,l,x)@t3 & not(#t2=#t3)\n\
           ==> (t3 < t2) | (t2 < t1)";
    vec![parse("locking1", locking1), parse("locking2", locking2)]
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
