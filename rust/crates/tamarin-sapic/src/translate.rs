//! Port of the top-level SAPIC `translate` orchestration
//! (`lib/sapic/src/Sapic.hs:45-101`) and `gen` (Sapic.hs:112-153), restricted
//! to the CORE LINEAR pipeline (no progress / reliable / report / states /
//! locks / compression passes).
//!
//! For a single top-level process, `translate`:
//!   1. annotates it (`toAnProcess` + `propagateNames`),
//!   2. computes the initial `Init` rule via `baseInit`,
//!   3. walks the process with `gen` (base translation per node),
//!   4. converts every `AnnotatedRule` to a `ProtoRuleE` via `toRule`,
//!   5. emits the always-on `single_session` restriction (`baseRestr`).
//!
//! The caller (run.rs) injects the rules + restriction into the theory, sets
//! `is_sapic`, and adds `heuristic: p` if the user didn't set one.

use std::collections::BTreeSet;

use tamarin_term::lterm::LVar;

use tamarin_theory::rule::ProtoRuleE;
use tamarin_theory::sapic::{
    GoodAnnotation, PlainProcess, Process, SapicLVar, ProcessPosition,
};

use tamarin_theory::sapic::ProcessCombinator;

use crate::annotation::{to_annotated, ProcessAnnotation};
use crate::base_translation::{
    base_init, base_trans_action, base_trans_comb, base_trans_null, predicate_restrictions,
    single_session_restriction, state_restrictions, RuleBody,
};
use crate::facts::{to_rule, AnnotatedRule, RulePosition, StateKind, TransFact};

/// `propagateNames` (Facts.hs:301-313): push each node's process-names down to
/// its children so every node carries the names of all its ancestors.
pub fn propagate_names<A: GoodAnnotation + Clone>(p: Process<A, SapicLVar>) -> Process<A, SapicLVar> {
    fn go<A: GoodAnnotation + Clone>(
        prefix: Vec<String>,
        p: Process<A, SapicLVar>,
    ) -> Process<A, SapicLVar> {
        match p {
            Process::Null(ann) => {
                let mut names = prefix;
                names.extend(ann.parsed().process_names.clone());
                Process::Null(set_names(ann, names))
            }
            Process::Action(a, ann, body) => {
                let mut names = prefix;
                names.extend(ann.parsed().process_names.clone());
                let ann2 = set_names(ann, names.clone());
                Process::Action(a, ann2, Box::new(go(names, *body)))
            }
            Process::Comb(c, ann, l, r) => {
                let mut names = prefix;
                names.extend(ann.parsed().process_names.clone());
                let ann2 = set_names(ann, names.clone());
                Process::Comb(
                    c,
                    ann2,
                    Box::new(go(names.clone(), *l)),
                    Box::new(go(names, *r)),
                )
            }
        }
    }
    go(Vec::new(), p)
}

fn set_names<A: GoodAnnotation>(ann: A, names: Vec<String>) -> A {
    let mut parsed = ann.parsed().clone();
    parsed.process_names = names;
    ann.set_parsed(parsed)
}

/// `processAt` over the annotated process (theory-side helper is generic).
fn process_at<'a>(
    p: &'a Process<ProcessAnnotation<LVar>, SapicLVar>,
    pos: &[i64],
) -> Option<&'a Process<ProcessAnnotation<LVar>, SapicLVar>> {
    if pos.is_empty() {
        return Some(p);
    }
    match (p, pos[0]) {
        (Process::Null(_), _) => None,
        (Process::Action(_, _, body), 1) => process_at(body, &pos[1..]),
        (Process::Comb(_, _, l, _), 1) => process_at(l, &pos[1..]),
        (Process::Comb(_, _, _, r), 2) => process_at(r, &pos[1..]),
        _ => None,
    }
}

/// `mapToAnnotatedRule` (Sapic.hs:145-147): tag each rule body with its index.
fn map_to_annotated_rule(
    proc: &Process<ProcessAnnotation<LVar>, SapicLVar>,
    p: &ProcessPosition,
    bodies: Vec<RuleBody>,
) -> Vec<AnnotatedRule<ProcessAnnotation<LVar>>> {
    bodies
        .into_iter()
        .enumerate()
        .map(|(i, (prems, acts, concs, restr))| AnnotatedRule {
            process_name: None,
            process: proc.clone(),
            position: RulePosition::Pos(p.clone()),
            prems,
            acts,
            concs,
            restr,
            index: i,
        })
        .collect()
}

/// `gen` (Sapic.hs:112-153).  Handles `Null`, `Action` (incl. the `Rep`
/// replication action), and the `Comb` combinators in scope — `Parallel`,
/// `NDC` (with the `substStatePos` shared-position rewrite), and `CondEq`.
/// `Cond`-with-a-formula / `Lookup` / `Let` are rejected in `base_trans_comb`
/// (Phase 2+/3).
fn gen(
    needs_in_ev_res: bool,
    an_proc: &Process<ProcessAnnotation<LVar>, SapicLVar>,
    p: &ProcessPosition,
    tildex: &BTreeSet<LVar>,
) -> Result<Vec<AnnotatedRule<ProcessAnnotation<LVar>>>, String> {
    let proc = process_at(an_proc, p)
        .ok_or_else(|| format!("gen: invalid position {p:?}"))?;
    match proc {
        Process::Null(ann) => {
            let bodies = base_trans_null(p, tildex);
            let _ = ann;
            Ok(map_to_annotated_rule(proc, p, bodies))
        }
        Process::Action(ac, ann, _) => {
            let (bodies, tildex2) =
                base_trans_action(false, needs_in_ev_res, ac, ann, p, tildex)?;
            let mut here = map_to_annotated_rule(proc, p, bodies);
            let mut child_pos = p.clone();
            child_pos.push(1);
            let rest = gen(needs_in_ev_res, an_proc, &child_pos, &tildex2)?;
            here.extend(rest);
            Ok(here)
        }
        // NDC special case (Sapic.hs:123-127): the NDC node itself emits NO
        // rule; its two children SHARE the parent's state position.  We
        // translate each child at `p++[1]` / `p++[2]` (so rule names carry the
        // correct position suffix), then rewrite the State premise of EVERY
        // generated rule from the child position back to the parent `p`
        // (`substStatePos`).
        Process::Comb(ProcessCombinator::Ndc, _, _, _) => {
            let mut pl = p.clone();
            pl.push(1);
            let mut pr = p.clone();
            pr.push(2);
            let l = gen(needs_in_ev_res, an_proc, &pl, tildex)?;
            let r = gen(needs_in_ev_res, an_proc, &pr, tildex)?;
            let mut out = subst_state_pos_rules(l, &pl, p);
            out.extend(subst_state_pos_rules(r, &pr, p));
            Ok(out)
        }
        // General combinator (Sapic.hs:128-134): emit this node's own rules,
        // then recurse into the left child with `tildex'1` and (if present) the
        // right child with `tildex'2`.
        Process::Comb(c, ann, _, _) => {
            let (bodies, tildex_l, tildex_r) = base_trans_comb(c, ann, p, tildex)?;
            let mut here = map_to_annotated_rule(proc, p, bodies);
            let mut pl = p.clone();
            pl.push(1);
            let msrs_l = gen(needs_in_ev_res, an_proc, &pl, &tildex_l)?;
            here.extend(msrs_l);
            if let Some(tx_r) = tildex_r {
                let mut pr = p.clone();
                pr.push(2);
                let msrs_r = gen(needs_in_ev_res, an_proc, &pr, &tx_r)?;
                here.extend(msrs_r);
            }
            Ok(here)
        }
    }
}

/// `substStatePos p_old p_new` over a list of generated rules (Sapic.hs:124,
/// 140-144): rewrite the position of every NON-semistate `State` PREMISE fact
/// from `p_old` to `p_new` (leaving the actual position `p_old==p++[i]` only in
/// the rule NAME, which was already fixed during `gen`).
fn subst_state_pos_rules(
    rules: Vec<AnnotatedRule<ProcessAnnotation<LVar>>>,
    p_old: &[i64],
    p_new: &[i64],
) -> Vec<AnnotatedRule<ProcessAnnotation<LVar>>> {
    rules
        .into_iter()
        .map(|mut r| {
            r.prems = r
                .prems
                .into_iter()
                .map(|f| subst_state_pos_fact(f, p_old, p_new))
                .collect();
            r
        })
        .collect()
}

/// `substStatePos` on a single fact (Sapic.hs:142-144):
///   State s p' vs | p' == p_old, not (isSemiState s) = State LState p_new vs
///   otherwise = fact
fn subst_state_pos_fact(f: TransFact, p_old: &[i64], p_new: &[i64]) -> TransFact {
    match f {
        TransFact::State(kind, pos, vs) if pos == p_old && !kind.is_semi_state() => {
            TransFact::State(StateKind::LState, p_new.to_vec(), vs)
        }
        other => other,
    }
}

/// `getLockPositions = pfoldMap getLock` (Basetranslation.hs:473,478): the lock
/// variables of every `Lock` action with `pureState=False` and a `lock`
/// annotation, in `pfoldMap` order, NOT deduplicated.
fn get_lock_positions(
    p: &Process<ProcessAnnotation<LVar>, SapicLVar>,
) -> Vec<LVar> {
    use tamarin_theory::sapic::SapicAction;
    let mut get_lock = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> Vec<LVar> {
        if let Process::Action(SapicAction::Lock(_), an, _) = proc {
            if !an.pure_state {
                if let Some(v) = &an.lock {
                    return vec![v.0.clone()];
                }
            }
        }
        vec![]
    };
    tamarin_theory::sapic::pfold_map(p, &mut get_lock)
}

/// `nub $ getUnlockPositions` (Basetranslation.hs:463): the lock variables of
/// every `Unlock` action with `pureState=False` and an `unlock` annotation, in
/// `pfoldMap` order, first-occurrence deduplicated (HS `List.nub`).
fn get_unlock_positions(
    p: &Process<ProcessAnnotation<LVar>, SapicLVar>,
) -> Vec<LVar> {
    use tamarin_theory::sapic::SapicAction;
    let mut get_unlock = |proc: &Process<ProcessAnnotation<LVar>, SapicLVar>| -> Vec<LVar> {
        if let Process::Action(SapicAction::Unlock(_), an, _) = proc {
            if !an.pure_state {
                if let Some(v) = &an.unlock {
                    return vec![v.0.clone()];
                }
            }
        }
        vec![]
    };
    let raw = tamarin_theory::sapic::pfold_map(p, &mut get_unlock);
    // `List.nub` — keep first occurrence, preserve order.
    let mut seen: Vec<LVar> = Vec::new();
    for v in raw {
        if !seen.contains(&v) {
            seen.push(v);
        }
    }
    seen
}

/// The result of translating a single top-level process.
pub struct Translation {
    /// The generated rules, each paired with its embedded `_restrict` formulas
    /// (parser-AST; non-empty only for `if <formula>` arms).  HS attaches these
    /// as the rule's `_preRestriction`; the RS port keeps them alongside the
    /// elaborated rule so `apply_sapic` can run the `_restrict` expansion
    /// (`lift_rule_restrictions`, HS `liftedAddProtoRule`) over both theories.
    pub rules: Vec<(ProtoRuleE, Vec<tamarin_parser::ast::Formula>)>,
    pub restrictions: Vec<tamarin_parser::ast::Restriction>,
}

/// `translate` (Sapic.hs:45-101) — linear subset.  `needs_in_ev_res` is HS
/// `needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)`; typing2 has no
/// such lemma, so the caller passes `false`.
pub fn translate(
    plain: &PlainProcess,
    needs_in_ev_res: bool,
) -> Result<Translation, String> {
    // annotate: toAnProcess + propagateNames + annotateLocks (Sapic.hs:54-61).
    //   The secret-channel / pure-state / report / let-destructor passes are
    //   either no-ops for the in-scope subset (secret-channels) or gated off by
    //   default (pure-state needs `--translation-state-optimisation`); locks is
    //   the last annotation step and the one Phase 4 requires.
    let an_proc_pre: Process<ProcessAnnotation<LVar>, SapicLVar> =
        propagate_names(to_annotated::<LVar>(plain.clone()));
    let an_proc = crate::locks::annotate_locks(an_proc_pre)?;

    // initial rules + initial tildex
    let (init_rules, init_tx) = base_init(&an_proc);

    // protocol rules
    let proto_rules = gen(needs_in_ev_res, &an_proc, &Vec::new(), &init_tx)?;

    // toRule over (initRules ++ protoRules), pairing each elaborated rule with
    // its embedded restriction formulas (the `AnnotatedRule.restr` field).
    let mut all = init_rules;
    all.extend(proto_rules);
    let rules: Vec<(ProtoRuleE, Vec<tamarin_parser::ast::Formula>)> =
        all.iter().map(|r| (to_rule(r), r.restr.clone())).collect();

    // restrictions (baseRestr, Basetranslation.hs:449-468), in HS order:
    //   [setIn, setNotIn]   if the process `contains isLookup`
    //                       (NoDelete variants unless it also `contains isDelete`)
    //   [resEq, resNotEq]   if the process `contains isEq`  (a CondEq node)
    //   [resSingleSession]  always (hasAccountabilityLemmaWithControl = True)
    // (locking restrictions are Phase 4.)
    let mut restrictions = Vec::new();
    if tamarin_theory::sapic::process_contains(&an_proc, tamarin_theory::sapic::is_lookup) {
        let has_delete =
            tamarin_theory::sapic::process_contains(&an_proc, tamarin_theory::sapic::is_delete);
        restrictions.extend(state_restrictions(has_delete));
    }
    if tamarin_theory::sapic::process_contains(&an_proc, tamarin_theory::sapic::is_eq) {
        restrictions.extend(predicate_restrictions());
    }
    restrictions.push(single_session_restriction());

    // Locking restrictions (baseRestr, Basetranslation.hs:463-468), AFTER the
    // hardcoded restrictions, in HS order:
    //   lockingWithUnlock = map (resLocking True)  (nub  getUnlockPositions)
    //   lockingOnlyLock   = map (resLocking False) (getLockPositions \\ getUnlockPositions)
    let unlock_positions = get_unlock_positions(&an_proc); // nub'd
    let lock_positions = get_lock_positions(&an_proc); // NOT nub'd (HS `getLockPositions`)
    for v in &unlock_positions {
        restrictions.push(crate::base_translation::res_locking(true, v));
    }
    // `getLockPositions anP \\ getUnlockPositions anP` — list-difference: keep
    // each lock var (in order, with duplicates) NOT present in the unlock set.
    for v in &lock_positions {
        if !unlock_positions.contains(v) {
            restrictions.push(crate::base_translation::res_locking(false, v));
        }
    }

    Ok(Translation { rules, restrictions })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::convert::convert_process;
    use crate::typing::type_and_rename_process;
    use tamarin_parser::ast as p;

    fn typing2_process() -> p::Process {
        let xspec = p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: Some("lol".into()),
        };
        let xref = p::Term::Var(p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: None,
        });
        let ffx = p::Term::App(
            "f".into(),
            vec![p::Term::App("f".into(), vec![xref.clone()])],
        );
        p::Process::Action {
            action: p::SapicAction::New(xspec),
            body: Box::new(p::Process::Action {
                action: p::SapicAction::Event(p::Fact {
                    persistent: false,
                    name: "Test".into(),
                    args: vec![xref],
                    annotations: vec![],
                }),
                body: Box::new(p::Process::Action {
                    action: p::SapicAction::ChOut { chan: None, msg: ffx },
                    body: Box::new(p::Process::Null),
                }),
            }),
        }
    }

    #[test]
    fn translate_typing2_produces_five_rules() {
        let plain = convert_process(&typing2_process()).unwrap();
        // No function-typing needed for the rule-count check; type over an
        // empty signature (defaults all funs).
        let sig = tamarin_term::maude_sig::MaudeSig::default();
        let typed = type_and_rename_process(&sig, &plain).unwrap();
        let tr = translate(&typed, false).unwrap();
        // Init + new + event + out + null = 5 rules.
        assert_eq!(tr.rules.len(), 5);
        assert_eq!(tr.restrictions.len(), 1);
        // First rule is "Init".
        assert_eq!(tr.rules[0].0.info.name, tamarin_theory::rule::ProtoRuleName::Stand("Init".into()));
    }
}
