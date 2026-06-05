//! Dynamic message-derivation check.
//!
//! Mirrors HS's `Theory.Tools.MessageDerivationChecks.checkVariableDeducability`
//! (lib/theory/src/Theory/Tools/MessageDerivationChecks.hs:35-50).  For each
//! protocol rule, asks the prover: "given that the intruder has access to all
//! of this rule's premise terms, can it derive each of the rule's free
//! variables?"  When a variable IS bound by some premise fact but cannot
//! actually be derived by the intruder (because the fact's containing rule
//! is unreachable / requires private knowledge), HS flags it as an
//! "unintended pattern match".
//!
//! How HS does it (verbatim — see `MessageDerivationChecks.hs:35-50,181-188`):
//!
//!   For each rule R indexed by idx:
//!     1. Drop ALL rules/lemmas/restrictions from the theory.
//!     2. `makeFunsPublic`: rewrite every private NoEq fun-sym to public,
//!        because the synthetic rule emits Out facts and the intruder must
//!        be able to apply destructors.
//!     3. Add a single generated rule:
//!          rule Generated_<idx>:
//!            [ Fr(~v1), Fr(~v2), ... ]                  // each free var of R
//!            --[ Generated_<idx>(v1, v2, ...) ]->        // sole action
//!            [ Out(t1), Out(t2), ... ]                   // R's premise terms
//!     4. Add one exists-trace lemma per free var v:
//!          lemma deriv_v: exists-trace
//!            "Ex v1 v2 ... #i. Generated_<idx>(v1, v2, ...) @ #i & K(v) @ #i"
//!     5. Run the prover on each lemma with `--derivcheck-timeout`.
//!     6. Lemmas whose proof did NOT find a trace identify non-derivable
//!        variables — report them.
//!
//! Note: prove_lemma is called per-variable, so a rule with N free vars
//! incurs N proof attempts.  Each is bounded by the user's timeout (default
//! 5s, mirrored on the HS side).  The check is gated by
//! `args.derivcheck_timeout`; passing `0` disables it entirely (HS:
//! `Main.TheoryLoader.hs:218`).

use std::time::{Duration, Instant};
use tamarin_parser::ast as p;
use tamarin_parser::wf::WfError;
use tamarin_term::maude_proc::MaudeHandle;

/// Run HS's per-variable derivability check on every rule.
///
/// `timeout_secs == 0` disables the check (returns `vec![]`).  Otherwise
/// each per-variable prove call is bounded by `timeout_secs` of wall-clock
/// time (mirrors HS's `--derivcheck-timeout`).
pub fn check_message_derivation(
    parsed: &p::Theory,
    maude: &MaudeHandle,
    timeout_secs: u32,
) -> Vec<WfError> {
    if timeout_secs == 0 { return Vec::new(); }
    let timeout = Duration::from_secs(timeout_secs as u64);
    let dbg = std::env::var_os("TAM_DBG_DERIV_CHECK").is_some();

    let mut per_rule: Vec<(String, Vec<String>)> = Vec::new();
    for (idx, rule) in protocol_rules(parsed).enumerate() {
        if rule.attributes.iter().any(|a| matches!(a, p::RuleAttr::NoDerivCheck)) {
            continue;
        }
        let free_vars = collect_rule_free_vars(rule);
        if free_vars.is_empty() { continue; }

        // Build the probe theory ONCE per rule (it contains all the
        // per-variable lemmas).  The synthesised theory is small —
        // one rule, N lemmas, the original signature.
        let probe = synthesise_probe_theory(parsed, rule, idx, &free_vars);
        if dbg {
            eprintln!("[deriv] rule={} free_vars={:?}", rule.name,
                free_vars.iter().map(|v| &v.name).collect::<Vec<_>>());
            eprintln!("[deriv] probe theory items:");
            for it in &probe.items {
                match it {
                    p::TheoryItem::Rule(r) => eprintln!("  rule {}: prem={} act={} conc={}",
                        r.name, r.premises.len(), r.actions.len(), r.conclusions.len()),
                    p::TheoryItem::Lemma(l) => eprintln!("  lemma {} ({:?})",
                        l.name, l.trace_quantifier),
                    _ => {}
                }
            }
        }

        // Try each variable's lemma.  HS's "TraceFound" status maps
        // to RS's `NodeStatus::Solved` for exists-trace lemmas.
        let mut undecidable = Vec::new();
        for v in &free_vars {
            let lemma_name = format!("deriv_check_{}_{}", idx, v.name);
            if !try_prove_within(&probe, &lemma_name, maude.clone(), timeout) {
                undecidable.push(v.name.clone());
            }
        }
        if !undecidable.is_empty() {
            per_rule.push((rule.name.clone(), undecidable));
        }
    }
    format_deriv_report(&per_rule)
}

/// Iterate over Rule items in declaration order.  Skips IntrRule
/// declarations (intruder rules), Restrictions, Lemmas.
fn protocol_rules(thy: &p::Theory) -> impl Iterator<Item = &p::Rule> {
    thy.items.iter().filter_map(|it| match it {
        p::TheoryItem::Rule(r) => Some(r),
        _ => None,
    })
}

/// All variables that appear anywhere in a rule's premise / action /
/// conclusion terms, in first-occurrence order, deduped, EXCLUDING:
///   - `Pub`-sort vars (`$x`) — HS's `deleteGlobals` drops these:
///     they are adversary-known by definition.
///   - `Node`-sort vars (`#i`) — timepoints, not message vars.
///   - Suffix-sorted vars whose underlying sort is Pub or Node, for the
///     same reason.
fn collect_rule_free_vars(r: &p::Rule) -> Vec<p::VarSpec> {
    let mut out: Vec<p::VarSpec> = Vec::new();
    let mut seen: std::collections::BTreeSet<(String, u64)> = std::collections::BTreeSet::new();
    let mut push = |v: &p::VarSpec, out: &mut Vec<p::VarSpec>, seen: &mut std::collections::BTreeSet<_>| {
        if matches!(v.sort, p::SortHint::Pub | p::SortHint::Node) {
            return;
        }
        if matches!(v.sort, p::SortHint::Suffix(p::SuffixSort::Pub)
            | p::SortHint::Suffix(p::SuffixSort::Node))
        {
            return;
        }
        let key = (v.name.clone(), v.idx);
        if seen.insert(key) {
            out.push(v.clone());
        }
    };
    let visit_term = |t: &p::Term, out: &mut Vec<p::VarSpec>, seen: &mut _| {
        let mut vs = Vec::new();
        collect_term_vars(t, &mut vs);
        for v in vs { push(&v, out, seen); }
    };
    for f in &r.premises { for a in &f.args { visit_term(a, &mut out, &mut seen); } }
    for f in &r.actions { for a in &f.args { visit_term(a, &mut out, &mut seen); } }
    for f in &r.conclusions { for a in &f.args { visit_term(a, &mut out, &mut seen); } }
    out
}

/// Apply a (name,idx) → VarSpec rename map to all variables in a term.
fn rename_term_vars(
    t: &p::Term,
    map: &std::collections::HashMap<(String, u64), p::VarSpec>,
) -> p::Term {
    match t {
        p::Term::Var(v) => {
            if let Some(new) = map.get(&(v.name.clone(), v.idx)) {
                p::Term::Var(new.clone())
            } else {
                t.clone()
            }
        }
        p::Term::App(name, args) => p::Term::App(
            name.clone(),
            args.iter().map(|a| rename_term_vars(a, map)).collect(),
        ),
        p::Term::Pair(args) => p::Term::Pair(
            args.iter().map(|a| rename_term_vars(a, map)).collect(),
        ),
        p::Term::BinOp(op, l, r) => p::Term::BinOp(
            *op,
            Box::new(rename_term_vars(l, map)),
            Box::new(rename_term_vars(r, map)),
        ),
        p::Term::AlgApp(name, l, r) => p::Term::AlgApp(
            name.clone(),
            Box::new(rename_term_vars(l, map)),
            Box::new(rename_term_vars(r, map)),
        ),
        _ => t.clone(),
    }
}

fn collect_term_vars(t: &p::Term, out: &mut Vec<p::VarSpec>) {
    match t {
        p::Term::Var(v) => out.push(v.clone()),
        p::Term::App(_, args) | p::Term::Pair(args) => {
            for a in args { collect_term_vars(a, out); }
        }
        p::Term::BinOp(_, l, rt) => { collect_term_vars(l, out); collect_term_vars(rt, out); }
        p::Term::AlgApp(_, l, rt) => { collect_term_vars(l, out); collect_term_vars(rt, out); }
        _ => {}
    }
}

/// Build the per-rule probe theory:
///
///   theory Probe_<idx>
///     <copy of original signature: builtins, functions, equations, macros>
///
///     rule Probe_<idx>:
///       [ Fr(~v) for each free Fresh-sort var ]
///       --[ Generated_<idx>(v1, v2, ...) ]->
///       [ Out(t) for each premise term in R ]
///
///     lemma deriv_check_<idx>_<v>: exists-trace
///       "Ex v1 v2 ... #i. Generated_<idx>(...) @ #i & K(v) @ #i"
///     ...one per free var...
fn synthesise_probe_theory(
    src: &p::Theory,
    rule: &p::Rule,
    idx: usize,
    free_vars: &[p::VarSpec],
) -> p::Theory {
    let mut probe = p::Theory {
        is_diff: false,
        name: format!("Probe_{}", idx),
        configuration: None,
        items: Vec::new(),
    };
    // Carry over the signature items.  Drops rules/lemmas/restrictions.
    for it in &src.items {
        match it {
            p::TheoryItem::Builtins(_)
            | p::TheoryItem::Functions(_)
            | p::TheoryItem::Equations { .. }
            | p::TheoryItem::Macros(_) => {
                probe.items.push(it.clone());
            }
            _ => {}
        }
    }
    // Rename ALL free vars to Fresh sort throughout the rule (mirrors
    // HS's `freesToFresh` + the implicit retyping the synthetic rule
    // needs to be wf — Fr( ) only accepts Fresh- or Msg-sorted args).
    // We use Fresh so the resulting var IS a fresh-sourced nonce the
    // intruder learns from Out, not a Msg-sort var.  The rename is
    // applied consistently to (a) the new Fr( ) premises, (b) the
    // action's args, (c) the Out( ) conclusions, AND (d) the lemma's
    // existential quantifier and KU goal.
    let rename: std::collections::HashMap<(String, u64), p::VarSpec> = free_vars.iter()
        .map(|v| {
            let mut vf = v.clone();
            vf.sort = p::SortHint::Fresh;
            ((v.name.clone(), v.idx), vf)
        })
        .collect();
    let renamed_free_vars: Vec<p::VarSpec> = free_vars.iter()
        .map(|v| rename[&(v.name.clone(), v.idx)].clone())
        .collect();
    let fresh_premises: Vec<p::Fact> = renamed_free_vars.iter()
        .map(|v| p::Fact {
            persistent: false,
            name: "Fr".into(),
            args: vec![p::Term::Var(v.clone())],
            annotations: Vec::new(),
        })
        .collect();
    let action = p::Fact {
        persistent: false,
        name: format!("Generated_{}", idx),
        args: renamed_free_vars.iter().map(|v| p::Term::Var(v.clone())).collect(),
        annotations: Vec::new(),
    };
    let out_concs: Vec<p::Fact> = rule.premises.iter()
        .flat_map(|f| f.args.iter().cloned())
        .map(|t| p::Fact {
            persistent: false,
            name: "Out".into(),
            args: vec![rename_term_vars(&t, &rename)],
            annotations: Vec::new(),
        })
        .collect();
    let probe_rule = p::Rule {
        name: format!("Probe_{}", idx),
        modulo: None,
        attributes: Vec::new(),
        let_block: Vec::new(),
        premises: fresh_premises,
        actions: vec![action.clone()],
        conclusions: out_concs,
        embedded_restrictions: Vec::new(),
        variants: Vec::new(),
        left_right: None,
    };
    probe.items.push(p::TheoryItem::Rule(probe_rule));

    // Build one lemma per free var.  HS's `landFormula` gives each
    // conjoined fact its OWN timepoint (MessageDerivationChecks.hs:202-203):
    //   `Generated_<idx>(...) @ #t0  ∧  KU(v) @ #t1`
    // Two DIFFERENT timepoints — asking "is there ever a time the
    // intruder knows v AND a (possibly different) time Generated fires?"
    // not "are these simultaneous".  The intruder-knowledge predicate
    // is `KU` (HS's `lntermToKUFact = kuFact`), not `K`.
    let action_atom = |action: p::Fact, t: p::Term| -> p::Formula {
        p::Formula::Atom(p::Atom::Action(action, t))
    };
    for v in free_vars {
        let lemma_name = format!("deriv_check_{}_{}", idx, v.name);
        let v_renamed = rename[&(v.name.clone(), v.idx)].clone();
        let t0 = p::VarSpec { name: "t0".into(), idx: 0, sort: p::SortHint::Node, typ: None };
        let t1 = p::VarSpec { name: "t1".into(), idx: 0, sort: p::SortHint::Node, typ: None };
        let gen_at = action_atom(action.clone(), p::Term::Var(t0.clone()));
        let ku_fact = p::Fact {
            persistent: false,
            name: "KU".into(),
            args: vec![p::Term::Var(v_renamed)],
            annotations: Vec::new(),
        };
        let ku_at = action_atom(ku_fact, p::Term::Var(t1.clone()));
        let conj = p::Formula::And(Box::new(gen_at), Box::new(ku_at));
        // Ex t0 t1 vars... . <conj>
        let mut all_quant = renamed_free_vars.clone();
        all_quant.push(t0);
        all_quant.push(t1);
        let body = p::Formula::Exists(all_quant, Box::new(conj));
        probe.items.push(p::TheoryItem::Lemma(p::Lemma {
            name: lemma_name,
            modulo: None,
            attributes: Vec::new(),
            trace_quantifier: p::TraceQuantifier::ExistsTrace,
            formula: body,
            proof: None,
        }));
    }

    probe
}

/// Run `prove_lemma` with a wall-clock cap of `timeout`.  Returns
/// `true` iff the prover found a trace (Solved for exists-trace).
fn try_prove_within(
    parsed: &p::Theory,
    lemma_name: &str,
    maude: MaudeHandle,
    timeout: Duration,
) -> bool {
    let prev_deadline = std::env::var("TAM_PROVE_DEADLINE_MS").ok();
    // Convert duration to ms.  +1 to guard against rounding-to-0 for
    // sub-second durations (HS clamps to whole seconds; we accept any
    // sub-second too, but a 0-ms deadline would immediately Sorry).
    let ms = (timeout.as_millis() as u64).max(1);
    std::env::set_var("TAM_PROVE_DEADLINE_MS", ms.to_string());
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        crate::prove::prove_lemma(parsed, lemma_name, maude, 1000)
    }));
    // Restore prior deadline so the deriv check doesn't leak into the
    // main prove loop.
    match prev_deadline {
        Some(v) => std::env::set_var("TAM_PROVE_DEADLINE_MS", v),
        None => std::env::remove_var("TAM_PROVE_DEADLINE_MS"),
    }
    match result {
        Ok(Ok(node)) => {
            if std::env::var_os("TAM_DBG_DERIV_CHECK").is_some() {
                eprintln!("[deriv] prove {} -> status={:?} children={}",
                    lemma_name, node.status, node.children.len());
            }
            matches!(node.status, crate::constraint::solver::search::NodeStatus::Solved)
        }
        Ok(Err(e)) => {
            if std::env::var_os("TAM_DBG_DERIV_CHECK").is_some() {
                eprintln!("[deriv] prove {} -> ProveError {:?}", lemma_name, e);
            }
            false
        }
        Err(_) => false,
    }
}

fn format_deriv_report(per_rule: &[(String, Vec<String>)]) -> Vec<WfError> {
    if per_rule.is_empty() { return Vec::new(); }
    let mut msg = String::from(
        "The variables of the following rule(s) are not derivable \
         from their premises, you may be performing unintended pattern \
         matching.\n\n");
    let blocks: Vec<String> = per_rule.iter()
        .map(|(rule_name, vars)| {
            format!("Rule {}: \nFailed to derive Variable(s): {}",
                rule_name, vars.join(", "))
        })
        .collect();
    msg.push_str(&blocks.join("\n\n"));
    vec![WfError::new("Message Derivation Checks", msg)]
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parse_theory;

    fn maude() -> Option<MaudeHandle> {
        let p = "/home/linuxbrew/.linuxbrew/bin/maude";
        if !std::path::Path::new(p).exists() { return None; }
        MaudeHandle::start(p, tamarin_term::maude_sig::pair_maude_sig()).ok()
    }

    #[test]
    fn deriv_check_passes_on_derivable_var() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [In(x)] --[Use(x)]-> [Out(x)]
              lemma trivial: "T"
            end
        "#;
        let thy = parse_theory(src, &[]).expect("parse");
        let report = check_message_derivation(&thy, &m, 5);
        // `x` appears in `In(x)` which is intruder-known → derivable.
        assert!(report.is_empty(), "expected no warnings, got {:?}", report);
    }

    #[test]
    fn deriv_check_flags_unbound_var() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [] --[Use(unbound)]-> [Out(unbound)]
              lemma trivial: "T"
            end
        "#;
        let thy = parse_theory(src, &[]).expect("parse");
        let report = check_message_derivation(&thy, &m, 5);
        // Free `unbound` has no premise → not derivable.
        assert_eq!(report.len(), 1);
        assert!(report[0].message.contains("unbound"),
            "expected 'unbound' in report, got {:?}", report);
    }

    #[test]
    fn deriv_check_disabled_by_zero_timeout() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [] --[Use(unbound)]-> [Out(unbound)]
              lemma trivial: "T"
            end
        "#;
        let thy = parse_theory(src, &[]).expect("parse");
        let report = check_message_derivation(&thy, &m, 0);
        assert!(report.is_empty(), "timeout=0 should disable the check");
    }
}
