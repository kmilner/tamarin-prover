//! Pretty-printer for the constraint `System`.
//!
//! Port of `prettyNonGraphSystem` from
//! `lib/theory/src/Theory/Constraint/System.hs:1673`.  Produces the
//! same section layout the Haskell interactive UI shows in its
//! "Constraint system" pane:
//!
//!   last:     ...
//!   formulas: ...
//!   subterms: ...
//!   equations: ...
//!   lemmas: ...
//!   allowed cases: ...
//!   solved formulas: ...
//!   unsolved constraints: ...
//!   solved constraints: ...
//!
//! For the lemma view `pretty_system` also emits the graph-bearing
//! sections (`nodes`, `edges`, `less`); unlike Haskell's `prettySystem`
//! no `actions` section is produced.

use tamarin_term::pretty::{pp_lvar, pretty_lnterm};

use crate::constraint::constraints::{Edge, Goal, LessAtom, NodeId};
use crate::constraint::system::{SourceKind, System};
use crate::fact::{fact_tag_name, LNFact};
use crate::guarded::Guarded;
use crate::pretty_formula::pretty_guarded;
use crate::rule::{
    ConcIdx, IntrRuleACInfo, PremIdx, ProtoRuleACInstInfo, ProtoRuleName,
    Rule, RuleACInst, RuleInfo,
};

/// Emit just the non-graph-part of the system, matching Haskell's
/// `prettyNonGraphSystem`.  See file-level docs for the section list.
pub fn pretty_non_graph_system(sys: &System) -> String {
    let mut out = String::new();
    section(&mut out, "last", &pretty_last(sys));
    section(&mut out, "formulas", &pretty_formula_list(&sys.formulas));
    section(&mut out, "subterms", &pretty_subterm_store(sys));
    section(&mut out, "equations", &pretty_eq_store(sys));
    section(&mut out, "lemmas", &pretty_formula_list(&sys.lemmas));
    section(&mut out, "allowed cases", &pretty_source_kind(sys.source_kind));
    section(&mut out, "solved formulas", &pretty_formula_list(&sys.solved_formulas));
    section(&mut out, "unsolved constraints", &pretty_goals(sys, false));
    section(&mut out, "solved constraints", &pretty_goals(sys, true));
    out
}

/// Full system rendering — emits the graph-bearing sections
/// (`nodes`/`edges`/`less`) plus everything in
/// `pretty_non_graph_system`.  Mirrors Haskell's `prettySystem`
/// (System.hs) except that the `actions` section
/// (`fsepList ppActionAtom $ unsolvedActionAtoms se`) is omitted.
#[allow(dead_code)]
pub fn pretty_system(sys: &System) -> String {
    let mut out = String::new();
    section(&mut out, "nodes", &pretty_nodes(sys));
    section(&mut out, "edges", &pretty_edges(&sys.edges));
    section(&mut out, "less", &pretty_lesses(&sys.less_atoms));
    out.push_str(&pretty_non_graph_system(sys));
    out
}

// ---------------------------------------------------------------------
// Section header helper
// ---------------------------------------------------------------------

fn section(out: &mut String, header: &str, body: &str) {
    out.push_str(header);
    out.push(':');
    if body.contains('\n') {
        out.push('\n');
        for line in body.lines() {
            out.push_str("  ");
            out.push_str(line);
            out.push('\n');
        }
    } else if body.is_empty() {
        out.push('\n');
    } else {
        out.push(' ');
        out.push_str(body);
        out.push('\n');
    }
}

// ---------------------------------------------------------------------
// last_atom
// ---------------------------------------------------------------------

fn pretty_last(sys: &System) -> String {
    match &sys.last_atom {
        None => "none".to_string(),
        Some(nid) => pretty_node_id(nid),
    }
}

// ---------------------------------------------------------------------
// formulas / lemmas / solved_formulas
// ---------------------------------------------------------------------

fn pretty_formula_list(items: &[Guarded]) -> String {
    if items.is_empty() { return String::new(); }
    let mut s = String::new();
    for (i, g) in items.iter().enumerate() {
        if i > 0 { s.push('\n'); }
        s.push_str(&pretty_guarded(g));
    }
    s
}

// ---------------------------------------------------------------------
// subterm / equation stores
// ---------------------------------------------------------------------

fn pretty_subterm_store(sys: &System) -> String {
    let st = &sys.subterm_store;
    let mut lines: Vec<String> = Vec::new();
    for c in &st.subterms {
        lines.push(format!("{} \u{228F} {}", pretty_lnterm(&c.small), pretty_lnterm(&c.big)));
    }
    for c in &st.solved_subterms {
        lines.push(format!("(solved) {} \u{228F} {}", pretty_lnterm(&c.small), pretty_lnterm(&c.big)));
    }
    if st.contradictory && lines.is_empty() {
        lines.push("\u{22A5}".into());
    }
    lines.join("\n")
}

fn pretty_eq_store(sys: &System) -> String {
    let eq = &sys.eq_store;
    let mut out = String::new();
    if !eq.subst.is_empty() {
        out.push_str("free: ");
        let parts: Vec<String> = eq.subst.to_list().into_iter()
            .map(|(v, t)| format!("{}={}", lvar_to_string(&v), pretty_lnterm(&t)))
            .collect();
        out.push_str(&parts.join(", "));
    }
    for d in &eq.conj {
        if !out.is_empty() { out.push('\n'); }
        out.push_str(&format!("split[{}]: ", d.split_id.0));
        if d.substs.is_empty() {
            out.push('\u{22A5}'); // ⊥
        } else {
            let parts: Vec<String> = d.substs.iter().map(|s| {
                let bindings: Vec<String> = s.to_list().into_iter()
                    .map(|(v, t)| format!("{}={}", lvar_to_string(&v), pretty_lnterm(&t)))
                    .collect();
                if bindings.is_empty() {
                    "{}".to_string()
                } else {
                    bindings.join(", ")
                }
            }).collect();
            out.push_str(&parts.join("  \u{2225} ")); // ‖
        }
    }
    out
}

// ---------------------------------------------------------------------
// goals
// ---------------------------------------------------------------------

fn pretty_goals(sys: &System, want_solved: bool) -> String {
    let mut lines: Vec<String> = Vec::new();
    let mut nr = 0;
    for (g, st) in sys.goals.iter() {
        if st.solved != want_solved { continue; }
        nr += 1;
        let lb = if st.looping { " (loop breaker)".to_string() } else { String::new() };
        lines.push(format!("{}  // nr: {}{}", pretty_goal(g), nr, lb));
    }
    lines.join("\n")
}

fn pretty_goal(g: &Goal) -> String {
    match g {
        Goal::Action(nid, fa) =>
            format!("{} @ {}", pretty_fact(fa), pretty_node_id(nid)),
        Goal::Chain(src, tgt) =>
            format!("{} ~~> {}", pretty_node_conc(src), pretty_node_prem(tgt)),
        Goal::Premise(np, fa) => {
            let (nid, PremIdx(i)) = np;
            format!("{} \u{25B6}{} {}", pretty_fact(fa), subscript(*i), pretty_node_id(nid))
        }
        Goal::Split(id) => format!("splitEqs({})", id.0),
        Goal::Disj(d) => {
            if d.0.is_empty() {
                "Disj(\u{22A5})".to_string()
            } else {
                let parts: Vec<String> = d.0.iter()
                    .map(|c| format!("({})", pretty_guarded(c))).collect();
                parts.join("  \u{2225} ") // ‖
            }
        }
        Goal::Subterm((l, r)) =>
            format!("{} \u{228F} {}", pretty_lnterm(l), pretty_lnterm(r)), // ⊏
    }
}

fn subscript(n: usize) -> String {
    n.to_string().chars().map(|c| match c {
        '0' => '\u{2080}', '1' => '\u{2081}', '2' => '\u{2082}',
        '3' => '\u{2083}', '4' => '\u{2084}', '5' => '\u{2085}',
        '6' => '\u{2086}', '7' => '\u{2087}', '8' => '\u{2088}',
        '9' => '\u{2089}', _ => c,
    }).collect()
}

// ---------------------------------------------------------------------
// source kind
// ---------------------------------------------------------------------

fn pretty_source_kind(sk: Option<SourceKind>) -> String {
    match sk {
        None => "all".to_string(),
        Some(SourceKind::RawSources) => "RawSources".to_string(),
        Some(SourceKind::RefinedSources) => "RefinedSources".to_string(),
    }
}

// ---------------------------------------------------------------------
// nodes / edges / less
// ---------------------------------------------------------------------

fn pretty_nodes(sys: &System) -> String {
    let mut sorted = (*sys.nodes).clone();
    sorted.sort_by(|(a, _), (b, _)| a.cmp(b));
    let lines: Vec<String> = sorted.iter()
        .map(|(nid, ru)| format!("{}: {}", pretty_node_id(nid), pretty_rule_inst(ru)))
        .collect();
    lines.join("\n")
}

fn pretty_edges(es: &[Edge]) -> String {
    let mut sorted = es.to_vec();
    sorted.sort();
    let parts: Vec<String> = sorted.iter()
        .map(|e| format!("{} >--> {}",
            pretty_node_conc(&e.src),
            pretty_node_prem(&e.tgt)))
        .collect();
    parts.join(", ")
}

fn pretty_lesses(ls: &[LessAtom]) -> String {
    let mut sorted = ls.to_vec();
    sorted.sort();
    let parts: Vec<String> = sorted.iter().map(|l| {
        format!("{} < {}: induced by {:?}",
            pretty_node_id(&l.smaller), pretty_node_id(&l.larger), l.reason)
    }).collect();
    parts.join(", ")
}

// ---------------------------------------------------------------------
// LNFact / RuleACInst rendering
// ---------------------------------------------------------------------

fn pretty_fact(fa: &LNFact) -> String {
    use crate::fact::Multiplicity;
    let prefix = match &fa.tag {
        crate::fact::FactTag::Proto(Multiplicity::Persistent, _, _) => "!",
        _ => "",
    };
    let name = fact_tag_name(&fa.tag);
    let args: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
    format!("{}{}({})", prefix, name, args.join(", "))
}

fn pretty_rule_inst(ru: &RuleACInst) -> String {
    let name = rule_inst_name(ru);
    let prems: Vec<String> = ru.premises.iter().map(pretty_fact).collect();
    let acts: Vec<String> = ru.actions.iter().map(pretty_fact).collect();
    let concs: Vec<String> = ru.conclusions.iter().map(pretty_fact).collect();
    if acts.is_empty() {
        format!("[{}] --> [{}]  // {}",
            prems.join(", "), concs.join(", "), name)
    } else {
        format!("[{}] --[ {} ]-> [{}]  // {}",
            prems.join(", "), acts.join(", "), concs.join(", "), name)
    }
}

fn rule_inst_name(ru: &Rule<RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo>>) -> String {
    match &ru.info {
        RuleInfo::Proto(p) => match &p.name {
            ProtoRuleName::Stand(s) => s.clone(),
            ProtoRuleName::Fresh => "Fresh".to_string(),
        },
        RuleInfo::Intr(info) => intr_rule_name(info),
    }
}

fn intr_rule_name(info: &IntrRuleACInfo) -> String {
    match info {
        IntrRuleACInfo::ConstrRule(bs) =>
            format!("c_{}", String::from_utf8_lossy(bs)),
        IntrRuleACInfo::DestrRule(bs, _, _, _) =>
            format!("d_{}", String::from_utf8_lossy(bs)),
        IntrRuleACInfo::Coerce => "coerce".to_string(),
        IntrRuleACInfo::IRecv => "irecv".to_string(),
        IntrRuleACInfo::ISend => "isend".to_string(),
        // Built-in constructor rules render without the `c_` prefix —
        // Haskell `prettyIntrRuleACInfo` (Rule.hs:1229) emits "pub",
        // "nat", "fresh"; the `c` prefix is for named user constructors.
        IntrRuleACInfo::PubConstr => "pub".to_string(),
        IntrRuleACInfo::NatConstr => "nat".to_string(),
        IntrRuleACInfo::FreshConstr => "fresh".to_string(),
        IntrRuleACInfo::IEquality => "iequality".to_string(),
    }
}

fn pretty_node_id(nid: &NodeId) -> String {
    let mut s = String::new();
    pp_lvar(nid, &mut s);
    s
}

fn lvar_to_string(v: &tamarin_term::lterm::LVar) -> String {
    let mut s = String::new();
    pp_lvar(v, &mut s);
    s
}

fn pretty_node_conc(c: &(NodeId, ConcIdx)) -> String {
    format!("({}, {})", pretty_node_id(&c.0), c.1 .0)
}

fn pretty_node_prem(p: &(NodeId, PremIdx)) -> String {
    format!("({}, {})", pretty_node_id(&p.0), p.1 .0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::system::System;

    #[test]
    fn empty_system_renders_each_section() {
        let s = System::default();
        let out = pretty_non_graph_system(&s);
        for h in &[
            "last:", "formulas:", "subterms:", "equations:", "lemmas:",
            "allowed cases:", "solved formulas:", "unsolved constraints:",
            "solved constraints:",
        ] {
            assert!(out.contains(h), "missing header {} in:\n{}", h, out);
        }
        assert!(out.contains("none"));
    }
}
