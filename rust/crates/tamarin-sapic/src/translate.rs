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

use crate::annotation::{to_annotated, ProcessAnnotation};
use crate::base_translation::{
    base_init, base_trans_action, base_trans_null, single_session_restriction, RuleBody,
};
use crate::facts::{to_rule, AnnotatedRule, RulePosition};

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

/// `gen` (Sapic.hs:112-153) — linear subset (Null / Action).  Combinators and
/// replication are rejected here (Phase 2+).
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
        Process::Comb(..) => Err(
            "gen: process combinators not yet ported (Phase 2+)".to_string(),
        ),
    }
}

/// The result of translating a single top-level process.
pub struct Translation {
    pub rules: Vec<ProtoRuleE>,
    pub restrictions: Vec<tamarin_parser::ast::Restriction>,
}

/// `translate` (Sapic.hs:45-101) — linear subset.  `needs_in_ev_res` is HS
/// `needsInEvRes = any lemmaNeedsInEvRes (theoryLemmas th)`; typing2 has no
/// such lemma, so the caller passes `false`.
pub fn translate(
    plain: &PlainProcess,
    needs_in_ev_res: bool,
) -> Result<Translation, String> {
    // annotate: toAnProcess + propagateNames.  (We skip the secret-channel /
    // lock / let-destructor / state passes — none apply to the linear subset.)
    let an_proc: Process<ProcessAnnotation<LVar>, SapicLVar> =
        propagate_names(to_annotated::<LVar>(plain.clone()));

    // initial rules + initial tildex
    let (init_rules, init_tx) = base_init(&an_proc);

    // protocol rules
    let proto_rules = gen(needs_in_ev_res, &an_proc, &Vec::new(), &init_tx)?;

    // toRule over (initRules ++ protoRules)
    let mut all = init_rules;
    all.extend(proto_rules);
    let rules: Vec<ProtoRuleE> = all.iter().map(to_rule).collect();

    // restrictions: the always-on single_session (baseRestr with
    // hasAccountabilityLemmaWithControl = True at the call site).
    let restrictions = vec![single_session_restriction()];

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
        assert_eq!(tr.rules[0].info.name, tamarin_theory::rule::ProtoRuleName::Stand("Init".into()));
    }
}
