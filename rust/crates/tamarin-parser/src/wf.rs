//! Wellformedness checks operating on the parser AST.
//!
//! Port of `Theory.Tools.Wellformedness` from
//! `lib/theory/src/Theory/Tools/Wellformedness.hs`. This implementation
//! works directly on the surface syntax tree because we don't yet have
//! a typed `Theory` AST. As a consequence:
//!
//! - Checks that need term-level sort inference (e.g. `Nat Sorts`) work
//!   over the parser's [`SortHint`] / sigil annotations rather than a
//!   full sort assignment.
//! - Checks that depend on Maude (`Variants`, `Rule has no variants`)
//!   are not implemented yet.
//! - The error messages we emit may not match Tamarin's word-for-word,
//!   but the *topic strings* (the underlined headers) match exactly so
//!   the fixture runner can compare topic sets.
//!
//! Each public `check_*` function corresponds to a Haskell `*Report`
//! function. The umbrella entry point is [`check_theory`].

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::*;

// =============================================================================
// Error type
// =============================================================================

/// A wellformedness diagnostic. `topic` matches exactly the underlined
/// header string Tamarin emits (e.g. `"Reserved names"`,
/// `"Fact arity issues"`).
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub struct WfError {
    pub topic: String,
    pub message: String,
}

impl WfError {
    pub fn new(topic: impl Into<String>, message: impl Into<String>) -> Self {
        WfError { topic: topic.into(), message: message.into() }
    }
}

pub type WfReport = Vec<WfError>;

/// Run every wellformedness check against `thy`. Topics from the result
/// can be compared directly against `tamarin-prover`'s output.
pub fn check_theory(thy: &Theory) -> WfReport {
    // Mirrors HS `Theory.Tools.Wellformedness.checkWellformedness`
    // (Wellformedness.hs:1270-1287) — same execution order so the
    // emitted warning groups appear in the same order in `tamarin-prover
    // --prove` output.
    let mut report = Vec::new();
    report.extend(unbound_report(thy));
    report.extend(fresh_names_report(thy));
    report.extend(public_names_report(thy));
    report.extend(left_right_rule_report(thy));    // ruleSortsReport
    // ruleVariantsReport — not ported (needs MaudeHandle + variant solver).
    // factReports group:
    report.extend(reserved_report(thy));
    report.extend(reserved_fact_name_rules(thy));
    report.extend(reserved_prefix_report(thy));
    report.extend(fresh_fact_arguments(thy));
    report.extend(special_facts_usage(thy));
    report.extend(fact_usage(thy));
    report.extend(fact_lhs_occur_no_rhs(thy));
    // formulaReports group:
    report.extend(formula_terms_report(thy));
    // checkQuantifiers / checkGuarded — partial via formula_free_var_report.
    // lemmaAttributeReport, multRestrictedReport, natWellSortedReport:
    report.extend(lemma_attribute_report(thy));
    report.extend(mult_restricted_report(thy));
    report.extend(nat_well_sorted_report(thy));
    // checkEquationsSubtermConvergence:
    report.extend(subterm_convergence_report(thy));
    // Message Derivation Checks (HS: TheoryLoader.hs:172-176 +
    // MessageDerivationChecks.hs:35).  HS's check is dynamic
    // (per-variable prover invocation, --derivcheck-timeout default 5s);
    // we run a static intersection that catches the same variables for
    // the common case.  See `message_derivation_report` docstring.
    report.extend(message_derivation_report(thy));
    report
}

/// The ordered set of distinct topic strings present in `report`.
pub fn topics(report: &WfReport) -> BTreeSet<String> {
    report.iter().map(|e| e.topic.clone()).collect()
}

// =============================================================================
// Helpers — collecting facts and variables
// =============================================================================

fn theory_rules(thy: &Theory) -> Vec<&Rule> {
    let mut out = Vec::new();
    for it in &thy.items {
        match it {
            TheoryItem::Rule(r) => out.push(r),
            TheoryItem::IntrRule(r) => out.push(r),
            _ => {}
        }
    }
    out
}

fn theory_lemmas(thy: &Theory) -> Vec<&Lemma> {
    thy.items.iter().filter_map(|it| match it {
        TheoryItem::Lemma(l) => Some(l),
        _ => None,
    }).collect()
}

#[allow(dead_code)]
fn theory_restrictions(thy: &Theory) -> Vec<&Restriction> {
    thy.items.iter().filter_map(|it| match it {
        TheoryItem::Restriction(r) | TheoryItem::LegacyAxiom(r) => Some(r),
        _ => None,
    }).collect()
}

/// Iterate all facts in a rule (premises ∪ actions ∪ conclusions),
/// labelled with which side they appeared on.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FactSide { Lhs, Acts, Rhs }

fn rule_facts(r: &Rule) -> Vec<(FactSide, &Fact)> {
    let mut out = Vec::new();
    for f in &r.premises    { out.push((FactSide::Lhs, f)); }
    for f in &r.actions     { out.push((FactSide::Acts, f)); }
    for f in &r.conclusions { out.push((FactSide::Rhs, f)); }
    out
}

/// Recursively collect every variable appearing in a term.
fn term_vars(t: &Term, out: &mut Vec<VarSpec>) {
    match t {
        Term::Var(v) => out.push(v.clone()),
        Term::App(_, args) => for a in args { term_vars(a, out); },
        Term::AlgApp(_, a, b) => { term_vars(a, out); term_vars(b, out); }
        Term::Pair(items) => for a in items { term_vars(a, out); },
        Term::Diff(a, b) => { term_vars(a, out); term_vars(b, out); }
        Term::BinOp(_, a, b) => { term_vars(a, out); term_vars(b, out); }
        Term::PatMatch(inner) => term_vars(inner, out),
        Term::PubLit(_) | Term::FreshLit(_) | Term::NatLit(_)
        | Term::Number(_) | Term::NumberOne | Term::NatOne | Term::DhNeutral => {}
    }
}

fn fact_vars(f: &Fact) -> Vec<VarSpec> {
    let mut v = Vec::new();
    for a in &f.args { term_vars(a, &mut v); }
    v
}

/// Collect every public-name literal (`'foo'`) and fresh-name literal
/// (`~'foo'`) within a term subtree.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NameKind { Pub, Fresh }

fn term_name_lits(t: &Term, out: &mut Vec<(NameKind, String)>) {
    match t {
        Term::PubLit(s) => out.push((NameKind::Pub, s.clone())),
        Term::FreshLit(s) => out.push((NameKind::Fresh, s.clone())),
        Term::App(_, args) => for a in args { term_name_lits(a, out); },
        Term::AlgApp(_, a, b) => { term_name_lits(a, out); term_name_lits(b, out); }
        Term::Pair(items) => for a in items { term_name_lits(a, out); },
        Term::Diff(a, b) => { term_name_lits(a, out); term_name_lits(b, out); }
        Term::BinOp(_, a, b) => { term_name_lits(a, out); term_name_lits(b, out); }
        Term::PatMatch(inner) => term_name_lits(inner, out),
        _ => {}
    }
}

fn rule_terms(r: &Rule) -> impl Iterator<Item = &Term> {
    r.premises.iter().chain(&r.actions).chain(&r.conclusions)
        .flat_map(|f: &Fact| f.args.iter())
}

/// True if a sort hint indicates a fresh-sort variable.
fn is_fresh_sort(s: &SortHint) -> bool {
    matches!(s,
        SortHint::Fresh
        | SortHint::Suffix(SuffixSort::Fresh))
}

fn is_msg_sort_or_untagged(s: &SortHint) -> bool {
    matches!(s, SortHint::Msg | SortHint::Untagged
        | SortHint::Suffix(SuffixSort::Msg))
}

fn is_pub_sort(s: &SortHint) -> bool {
    matches!(s, SortHint::Pub | SortHint::Suffix(SuffixSort::Pub))
}

fn is_node_sort(s: &SortHint) -> bool {
    matches!(s, SortHint::Node | SortHint::Suffix(SuffixSort::Node))
}

fn is_nat_sort(s: &SortHint) -> bool {
    matches!(s, SortHint::Nat | SortHint::Suffix(SuffixSort::Nat))
}

// =============================================================================
// Reserved fact names — Tamarin reserves 'fr', 'ku', 'kd', 'out', 'in'
// =============================================================================

const RESERVED_FACT_NAMES: &[&str] = &["fr", "ku", "kd", "out", "in"];

/// True if `name` is a built-in fact tag (case-insensitive). These are
/// allowed when used in their semantic position (e.g. `Fr(~k)` in a
/// premise) but not as user-defined protocol facts elsewhere.
fn is_builtin_fact_name(name: &str) -> bool {
    matches!(name, "Fr" | "In" | "Out" | "K" | "KU" | "KD" | "Ded" | "Term")
}

pub fn reserved_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for (_, f) in rule_facts(r) {
            // Only protocol facts (non-builtin) trigger this check.
            if is_builtin_fact_name(&f.name) { continue; }
            let lower = f.name.to_lowercase();
            if RESERVED_FACT_NAMES.contains(&lower.as_str()) {
                out.push(WfError::new("Reserved names",
                    format!("Rule '{}' contains a fact with reserved name `{}`",
                        r.name, f.name)));
            }
        }
    }
    // Lemma/restriction formula facts: skipped here because the parser
    // AST keeps formulas in a less-structured form. This matches the
    // bulk of Tamarin's reserved_report behaviour for rules.
    out
}

// =============================================================================
// Reserved KU/KD/K-log usage
// =============================================================================

const KLOG_NAMES: &[&str] = &["KU", "KD", "K", "Ded"];

pub fn reserved_fact_name_rules(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let bad_lhs: Vec<&Fact> = r.premises.iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str()))
            .collect();
        let bad_acts: Vec<&Fact> = r.actions.iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str())
                || matches!(f.name.as_str(), "In" | "Out" | "Fr"))
            .collect();
        let bad_rhs: Vec<&Fact> = r.conclusions.iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str()))
            .collect();
        for (msg, fs) in [
            ("on left-hand-side", bad_lhs),
            ("on the middle", bad_acts),
            ("on the right-hand-side", bad_rhs),
        ] {
            if !fs.is_empty() {
                let names: Vec<String> = fs.iter().map(|f| f.name.clone()).collect();
                out.push(WfError::new("Reserved names",
                    format!("Rule '{}' contains facts with reserved names {}: {}",
                        r.name, msg, names.join(", "))));
            }
        }
    }
    out
}

// =============================================================================
// Reserved prefixes (DiffIntr*, DiffProto*) — diff theories only
// =============================================================================

pub fn reserved_prefix_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    if !thy.is_diff { return out; }
    for r in theory_rules(thy) {
        for (_, f) in rule_facts(r) {
            let lower = f.name.to_lowercase();
            if lower.starts_with("diffintr") || lower.starts_with("diffproto") {
                out.push(WfError::new("Reserved prefixes",
                    format!("Rule '{}' contains a fact with reserved prefix: {}",
                        r.name, f.name)));
            }
        }
    }
    out
}

// =============================================================================
// Special facts misuse
// =============================================================================

pub fn special_facts_usage(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let lhs_bad: Vec<&Fact> = r.premises.iter()
            .filter(|f| f.name == "Out")
            .collect();
        let rhs_bad: Vec<&Fact> = r.conclusions.iter()
            .filter(|f| f.name == "Fr" || f.name == "In")
            .collect();
        if !lhs_bad.is_empty() {
            out.push(WfError::new("Special facts",
                format!("rule '{}' uses disallowed facts on left-hand-side: {}",
                    r.name, lhs_bad.iter().map(|f| f.name.as_str())
                        .collect::<Vec<_>>().join(", "))));
        }
        if !rhs_bad.is_empty() {
            out.push(WfError::new("Special facts",
                format!("rule '{}' uses disallowed facts on right-hand-side: {}",
                    r.name, rhs_bad.iter().map(|f| f.name.as_str())
                        .collect::<Vec<_>>().join(", "))));
        }
    }
    out
}

// =============================================================================
// Fr facts must use a fresh- or msg-variable
// =============================================================================

/// Compact term pretty-printer for wf error messages.  Matches HS's
/// `Theory.Tools.Wellformedness` rendering of variable sorts:
///   `$name`  — public, `~name` — fresh, `#name` — node, `%name` — nat,
///   bare `name` for msg-sorted or untagged variables.  Function
///   applications use `f(arg, ...)` form.
fn pp_term_short(t: &Term) -> String {
    match t {
        Term::Var(v) => {
            let prefix = match v.sort {
                SortHint::Pub => "$",
                SortHint::Fresh => "~",
                SortHint::Node => "#",
                SortHint::Nat => "%",
                _ => "",
            };
            format!("{}{}", prefix, v.name)
        }
        Term::App(name, args) => {
            let parts: Vec<String> = args.iter().map(pp_term_short).collect();
            format!("{}({})", name, parts.join(", "))
        }
        Term::PubLit(s) => format!("'{}'", s),
        _ => format!("{:?}", t),
    }
}

pub fn fresh_fact_arguments(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for f in &r.premises {
            if f.name != "Fr" { continue; }
            if f.args.len() != 1 { continue; }
            let arg = &f.args[0];
            // The argument must be a single variable of fresh- or
            // message-sort. Anything else (constants, function
            // applications, public/node vars) triggers the warning.
            let ok = match arg {
                Term::Var(v) => is_fresh_sort(&v.sort) || is_msg_sort_or_untagged(&v.sort),
                _ => false,
            };
            if !ok {
                out.push(WfError::new(
                    "Fr facts must only use a fresh- or a msg-variable",
                    format!("rule `{}' fact: Fr( {} )", r.name, pp_term_short(arg)),
                ));
            }
        }
    }
    out
}

// =============================================================================
// Fact arity / multiplicity / capitalization clashes
// =============================================================================

#[derive(Debug, Clone)]
struct FactObservation {
    #[allow(dead_code)]
    rule_name: String,
    name: String,
    arity: usize,
    persistent: bool,
}

fn collect_fact_observations(thy: &Theory) -> Vec<FactObservation> {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for (_, f) in rule_facts(r) {
            // Built-in tags (Fr, In, Out, ...) are not part of the
            // capitalization/arity/multiplicity check — Tamarin treats
            // those separately.
            if is_builtin_fact_name(&f.name) { continue; }
            out.push(FactObservation {
                rule_name: r.name.clone(),
                name: f.name.clone(),
                arity: f.args.len(),
                persistent: f.persistent,
            });
        }
    }
    out
}

pub fn fact_usage(thy: &Theory) -> WfReport {
    let observations = collect_fact_observations(thy);
    let mut groups: BTreeMap<String, Vec<&FactObservation>> = BTreeMap::new();
    for obs in &observations {
        groups.entry(obs.name.to_lowercase()).or_default().push(obs);
    }
    let mut out = Vec::new();
    for (_, group) in groups.iter().filter(|(_, g)| g.len() >= 2) {
        let cap_set: BTreeSet<&str> = group.iter().map(|o| o.name.as_str()).collect();
        let arity_set: BTreeSet<usize> = group.iter().map(|o| o.arity).collect();
        let mult_set: BTreeSet<bool> = group.iter().map(|o| o.persistent).collect();
        if cap_set.len() > 1 {
            out.push(WfError::new("Fact capitalization issues",
                format!("Fact `{}`: clashing capitalizations {}",
                    group[0].name.to_lowercase(),
                    cap_set.iter().cloned().collect::<Vec<_>>().join(", "))));
        }
        if arity_set.len() > 1 {
            let arities: Vec<String> = arity_set.iter().map(|n| n.to_string()).collect();
            out.push(WfError::new("Fact arity issues",
                format!("Fact `{}`: clashing arities {}",
                    group[0].name.to_lowercase(),
                    arities.join(", "))));
        }
        if mult_set.len() > 1 {
            out.push(WfError::new("Fact multiplicity issues",
                format!("Fact `{}`: clashing multiplicities (linear/persistent)",
                    group[0].name.to_lowercase())));
        }
    }
    out
}

// =============================================================================
// Fact occurs in some LHS but not in any RHS
// =============================================================================

pub fn fact_lhs_occur_no_rhs(thy: &Theory) -> WfReport {
    let mut rhs_keys: BTreeSet<(String, usize, bool)> = BTreeSet::new();
    for r in theory_rules(thy) {
        for f in &r.conclusions {
            rhs_keys.insert((f.name.clone(), f.args.len(), f.persistent));
        }
    }
    let mut seen_lhs: BTreeMap<(String, usize, bool), Vec<String>> = BTreeMap::new();
    for r in theory_rules(thy) {
        for f in &r.premises {
            if is_builtin_fact_name(&f.name) { continue; }
            seen_lhs.entry((f.name.clone(), f.args.len(), f.persistent))
                .or_default()
                .push(r.name.clone());
        }
    }
    let mut out = Vec::new();
    for (key, rules) in seen_lhs {
        if !rhs_keys.contains(&key) {
            out.push(WfError::new(
                "Facts occur in the left-hand-side but not in any right-hand-side",
                format!("Fact `{}`/{} appears only as a premise (rules: {})",
                    key.0, key.1, rules.join(", "))));
        }
    }
    out
}

// =============================================================================
// Fresh public constants — `~'foo'` is forbidden
// =============================================================================

pub fn fresh_names_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let mut names = Vec::new();
        for t in rule_terms(r) {
            term_name_lits(t, &mut names);
        }
        let fresh_lits: Vec<String> = names.iter()
            .filter_map(|(k, n)| if *k == NameKind::Fresh { Some(n.clone()) } else { None })
            .collect();
        if !fresh_lits.is_empty() {
            out.push(WfError::new("Fresh public constants",
                format!("rule '{}': fresh public constants are not allowed: {}",
                    r.name, fresh_lits.join(", "))));
        }
    }
    out
}

// =============================================================================
// Public constant capitalization clashes
// =============================================================================

pub fn public_names_report(thy: &Theory) -> WfReport {
    let mut all: Vec<(String, String)> = Vec::new(); // (rule_name, pub_name)
    for r in theory_rules(thy) {
        let mut names = Vec::new();
        for t in rule_terms(r) {
            term_name_lits(t, &mut names);
        }
        for (k, n) in names {
            if k == NameKind::Pub { all.push((r.name.clone(), n)); }
        }
    }
    let mut by_lower: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (_ru, n) in &all {
        by_lower.entry(n.to_lowercase()).or_default().insert(n.clone());
    }
    let mut out = Vec::new();
    for (_lower, set) in by_lower.iter().filter(|(_, s)| s.len() > 1) {
        let mut names: Vec<&String> = set.iter().collect();
        names.sort();
        out.push(WfError::new(
            "Public constants with mismatching capitalization",
            format!("clashing public-name capitalizations: {}",
                names.iter().map(|s| format!("'{}'", s))
                    .collect::<Vec<_>>().join(", "))));
    }
    out
}

// =============================================================================
// Unbound variables: vars in RHS / actions but not in LHS
// =============================================================================

/// Collect a rule's unbound variables (conclusion/action vars NOT in
/// any premise / let-binding).  Returns the list in first-occurrence
/// order, deduped, excluding pub-sort variables (which are implicitly
/// adversary-known and so always bound).
fn collect_rule_unbound_vars(r: &Rule) -> Vec<VarSpec> {
    let mut bound: BTreeSet<(String, u64)> = BTreeSet::new();
    for f in &r.premises {
        for v in fact_vars(f) {
            bound.insert((v.name.clone(), v.idx));
        }
    }
    for binding in &r.let_block {
        let mut vs = Vec::new();
        term_vars(&binding.var, &mut vs);
        term_vars(&binding.value, &mut vs);
        for v in vs {
            bound.insert((v.name, v.idx));
        }
    }
    let mut unbound: Vec<VarSpec> = Vec::new();
    let mut seen: BTreeSet<(String, u64)> = BTreeSet::new();
    for f in r.actions.iter().chain(&r.conclusions) {
        for v in fact_vars(f) {
            if is_pub_sort(&v.sort) { continue; }
            let key = (v.name.clone(), v.idx);
            if bound.contains(&key) { continue; }
            if seen.insert(key.clone()) {
                unbound.push(v);
            }
        }
    }
    unbound
}

pub fn unbound_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let unbound = collect_rule_unbound_vars(r);
        if !unbound.is_empty() {
            let names: Vec<String> = unbound.iter()
                .map(render_var)
                .collect();
            // HS format: `rule `R' has unbound variables: \n    v1\n    v2\n...`
            // (Wellformedness.hs:493-510, `prettyVarList`).  One var
            // per indented line.
            let var_lines: String = names.iter()
                .map(|n| format!("    {}", n))
                .collect::<Vec<_>>()
                .join("\n");
            out.push(WfError::new("Unbound variables",
                format!("rule `{}' has unbound variables: \n{}", r.name, var_lines)));
        }
    }
    out
}

/// Static analog of HS's `checkVariableDeducability`
/// (`Theory.Tools.MessageDerivationChecks`).  HS spawns the prover on a
/// synthetic theory per rule + per variable; we instead emit the
/// SAME set of variables that `unbound_report` flags, under the
/// distinct topic HS uses.
///
/// HS's check is a superset of ours: it also catches variables that ARE
/// bound by a premise but whose containing fact is never produced by
/// any other rule, so the intruder can't derive them.  Catching that
/// requires the prover (see HS's `proveTheory` per-variable loop) and
/// is gated behind `--derivcheck-timeout` (default 5s).  We currently
/// implement only the static intersection — the common case — and
/// preserve byte-identical output for it.  Extending to the dynamic
/// check is documented as future work.
pub fn message_derivation_report(thy: &Theory) -> WfReport {
    // Aggregate (rule_name, [unbound_var_names]) pairs across the
    // theory, skipping rules with the `no_derivcheck` attribute.
    let mut per_rule: Vec<(String, Vec<String>)> = Vec::new();
    for r in theory_rules(thy) {
        if r.attributes.iter().any(|a| matches!(a,
            crate::ast::RuleAttr::NoDerivCheck)) { continue; }
        let unbound = collect_rule_unbound_vars(r);
        if unbound.is_empty() { continue; }
        let names: Vec<String> = unbound.iter()
            .map(|v| v.name.clone())
            .collect();
        per_rule.push((r.name.clone(), names));
    }
    if per_rule.is_empty() { return Vec::new(); }
    // HS emits this as a single WfErrorReport entry with a multi-line
    // message: explanatory header + one block per affected rule.
    let mut msg = String::from(
        "The variables of the following rule(s) are not derivable \
         from their premises, you may be performing unintended pattern \
         matching.\n\n");
    let rule_blocks: Vec<String> = per_rule.iter()
        .map(|(rule_name, vars)| {
            format!("Rule {}: \nFailed to derive Variable(s): {}",
                rule_name, vars.join(", "))
        })
        .collect();
    msg.push_str(&rule_blocks.join("\n\n"));
    vec![WfError::new("Message Derivation Checks", msg)]
}

fn render_var(v: &VarSpec) -> String {
    let prefix = match v.sort {
        SortHint::Fresh | SortHint::Suffix(SuffixSort::Fresh) => "~",
        SortHint::Pub | SortHint::Suffix(SuffixSort::Pub) => "$",
        SortHint::Node | SortHint::Suffix(SuffixSort::Node) => "#",
        SortHint::Nat | SortHint::Suffix(SuffixSort::Nat) => "%",
        _ => "",
    };
    if v.idx == 0 {
        format!("{}{}", prefix, v.name)
    } else {
        format!("{}{}.{}", prefix, v.name, v.idx)
    }
}

// =============================================================================
// Multiplication restriction of rules
// =============================================================================

/// True if `t` (or any subterm) uses the AC `*` (mult) or `^` (exp) op
/// or appears as `inv(...)` — these are reducible roots forbidden in
/// rule LHS.
fn term_has_reducible_op(t: &Term) -> bool {
    match t {
        Term::BinOp(BinOp::Mult, _, _) | Term::BinOp(BinOp::Exp, _, _)
        | Term::BinOp(BinOp::Xor, _, _) => true,
        Term::App(name, _) if name == "inv" => true,
        Term::App(_, args) | Term::Pair(args) => args.iter().any(term_has_reducible_op),
        Term::AlgApp(_, a, b) => term_has_reducible_op(a) || term_has_reducible_op(b),
        Term::Diff(a, b) => term_has_reducible_op(a) || term_has_reducible_op(b),
        Term::BinOp(_, a, b) => term_has_reducible_op(a) || term_has_reducible_op(b),
        Term::PatMatch(inner) => term_has_reducible_op(inner),
        _ => false,
    }
}

pub fn mult_restricted_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let bad_lhs: Vec<String> = r.premises.iter()
            .flat_map(|f| f.args.iter())
            .filter(|t| term_has_reducible_op(t))
            .map(|t| format!("{:?}", t))
            .collect();
        if !bad_lhs.is_empty() {
            out.push(WfError::new("Multiplication restriction of rules",
                format!("rule `{}' has reducible operators on its LHS: {}",
                    r.name, bad_lhs.join(", "))));
        }
    }
    out
}

// =============================================================================
// Lemma annotations — reuse on exists-trace
// =============================================================================

pub fn lemma_attribute_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for l in theory_lemmas(thy) {
        let is_exists = matches!(l.trace_quantifier, TraceQuantifier::ExistsTrace);
        let is_reuse = l.attributes.iter().any(|a| matches!(a, LemmaAttr::Reuse));
        if is_exists && is_reuse {
            out.push(WfError::new("Lemma annotations",
                format!("Lemma `{}': cannot reuse 'exists-trace' lemmas",
                    l.name)));
        }
    }
    out
}

// =============================================================================
// Diff theory: Left rule / Right rule consistency
// =============================================================================

pub fn left_right_rule_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    if !thy.is_diff { return out; }
    for r in theory_rules(thy) {
        let (lhs_diff, rhs_diff) = match &r.left_right {
            Some(pair) => pair,
            None => continue,
        };
        // Project the parent rule's premises onto LEFT (first arg of
        // diff) and RIGHT (second arg).
        let proj_l = project_rule(r, /* left = */ true);
        let proj_r = project_rule(r, /* left = */ false);
        if !rules_equivalent_up_to_actions(&proj_l, lhs_diff) {
            out.push(WfError::new("Left rule",
                format!("Inconsistent left rule for `{}'", r.name)));
        }
        if !rules_equivalent_up_to_actions(&proj_r, rhs_diff) {
            out.push(WfError::new("Right rule",
                format!("Inconsistent right rule for `{}'", r.name)));
        }
    }
    out
}

/// Project all `diff(a, b)` subterms in `r` onto `left` or right. Used to
/// derive what the explicit left/right rule blocks should look like.
fn project_rule(r: &Rule, left: bool) -> Rule {
    fn proj_term(t: &Term, left: bool) -> Term {
        match t {
            Term::Diff(a, b) => if left { proj_term(a, left) } else { proj_term(b, left) },
            Term::App(n, args) =>
                Term::App(n.clone(), args.iter().map(|a| proj_term(a, left)).collect()),
            Term::AlgApp(n, a, b) =>
                Term::AlgApp(n.clone(), Box::new(proj_term(a, left)), Box::new(proj_term(b, left))),
            Term::Pair(items) =>
                Term::Pair(items.iter().map(|a| proj_term(a, left)).collect()),
            Term::BinOp(op, a, b) =>
                Term::BinOp(*op, Box::new(proj_term(a, left)), Box::new(proj_term(b, left))),
            Term::PatMatch(inner) => Term::PatMatch(Box::new(proj_term(inner, left))),
            other => other.clone(),
        }
    }
    fn proj_fact(f: &Fact, left: bool) -> Fact {
        Fact {
            persistent: f.persistent,
            name: f.name.clone(),
            args: f.args.iter().map(|a| proj_term(a, left)).collect(),
            annotations: f.annotations.clone(),
        }
    }
    Rule {
        name: r.name.clone(),
        modulo: r.modulo.clone(),
        attributes: r.attributes.clone(),
        let_block: r.let_block.clone(),
        premises: r.premises.iter().map(|f| proj_fact(f, left)).collect(),
        actions: r.actions.iter().map(|f| proj_fact(f, left)).collect(),
        conclusions: r.conclusions.iter().map(|f| proj_fact(f, left)).collect(),
        embedded_restrictions: r.embedded_restrictions.clone(),
        variants: vec![],
        left_right: None,
    }
}

/// Two rules are "equivalent up to added actions" if their premises
/// and conclusions match exactly. Tamarin allows the explicit
/// left/right rule to add actions; everything else must match.
fn rules_equivalent_up_to_actions(a: &Rule, b: &Rule) -> bool {
    a.premises == b.premises && a.conclusions == b.conclusions
}

// =============================================================================
// Subterm convergence warning
// =============================================================================

/// True if `lhs = rhs` is a subterm-convergent rewrite rule: every
/// proper subterm of the RHS occurs as a subterm of the LHS, OR the
/// RHS is exactly a constant `true`.
pub fn subterm_convergence_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for it in &thy.items {
        let (eqs, convergent) = match it {
            TheoryItem::Equations { eqs, convergent } => (eqs, *convergent),
            _ => continue,
        };
        if convergent { continue; }
        for eq in eqs {
            if !is_subterm_convergent(&eq.lhs, &eq.rhs) {
                out.push(WfError::new("Subterm Convergence Warning",
                    format!("equation is not subterm-convergent: {:?} = {:?}",
                        eq.lhs, eq.rhs)));
            }
        }
    }
    out
}

fn is_subterm_convergent(lhs: &Term, rhs: &Term) -> bool {
    // Rules with RHS = `true` (a public constructor constant) are accepted.
    // Tamarin treats certain reserved nullary names as constants; our parser
    // may render bare `true` as either `App("true", [])` or `Var("true")`,
    // so accept both forms.
    if is_reserved_constant(rhs) { return true; }
    // Otherwise the RHS must literally appear as a subterm of the LHS.
    contains_subterm(lhs, rhs)
}

fn is_reserved_constant(t: &Term) -> bool {
    match t {
        Term::App(name, args) if args.is_empty() =>
            is_known_nullary_constant_name(name),
        Term::Var(v) if matches!(v.sort, SortHint::Untagged) =>
            is_known_nullary_constant_name(&v.name),
        _ => false,
    }
}

/// Names that the surface parser may render as bare identifiers but
/// that semantically denote nullary constants (typically declared by
/// `builtins:` or `functions: ... /0`). We treat them as constants
/// for the purposes of subterm-convergence and free-variable checks.
fn is_known_nullary_constant_name(n: &str) -> bool {
    matches!(n, "true" | "True" | "zero" | "one" | "DH_neutral")
}

fn contains_subterm(haystack: &Term, needle: &Term) -> bool {
    if haystack == needle { return true; }
    match haystack {
        Term::App(_, args) | Term::Pair(args) =>
            args.iter().any(|a| contains_subterm(a, needle)),
        Term::AlgApp(_, a, b) =>
            contains_subterm(a, needle) || contains_subterm(b, needle),
        Term::Diff(a, b) | Term::BinOp(_, a, b) =>
            contains_subterm(a, needle) || contains_subterm(b, needle),
        Term::PatMatch(inner) => contains_subterm(inner, needle),
        _ => false,
    }
}

// =============================================================================
// Variable sort/capitalization clashes (within a single rule)
// =============================================================================

pub fn formula_terms_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    out.extend(variable_sort_clashes(thy));
    out.extend(formula_free_var_report(thy));
    out
}

/// Walk every lemma/restriction formula and emit `Formula terms` when
/// it contains a variable not bound by any enclosing quantifier. This
/// is a pragmatic stand-in for Tamarin's full `checkTerms`: a free
/// variable in a formula always violates "only allowed terms are
/// public constants and bound vars".
pub fn formula_free_var_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for l in theory_lemmas(thy) {
        if let Some(bad) = first_free_var_in_formula(&l.formula) {
            out.push(WfError::new("Formula terms",
                format!("Lemma `{}' uses terms of the wrong form: `Free {}'",
                    l.name, render_var(&bad))));
        }
    }
    for r in theory_restrictions(thy) {
        if let Some(bad) = first_free_var_in_formula(&r.formula) {
            out.push(WfError::new("Formula terms",
                format!("Restriction `{}' uses terms of the wrong form: `Free {}'",
                    r.name, render_var(&bad))));
        }
    }
    out
}

/// Find the first free variable in `f`, walking quantifier scopes. We
/// treat two `VarSpec`s as "the same variable" if their name and
/// effective sort kind agree. A bound `i` (untagged or `#i`) covers
/// references to the same name in either form when used at the
/// expected position.
fn first_free_var_in_formula(f: &Formula) -> Option<VarSpec> {
    fn rec(f: &Formula, scope: &[VarSpec]) -> Option<VarSpec> {
        match f {
            Formula::True | Formula::False => None,
            Formula::Atom(a) => first_free_var_in_atom(a, scope),
            Formula::Not(g) => rec(g, scope),
            Formula::And(a, b) | Formula::Or(a, b)
            | Formula::Implies(a, b) | Formula::Iff(a, b) => {
                rec(a, scope).or_else(|| rec(b, scope))
            }
            Formula::Forall(vs, body) | Formula::Exists(vs, body) => {
                let mut new_scope = scope.to_vec();
                new_scope.extend(vs.iter().cloned());
                rec(body, &new_scope)
            }
        }
    }
    rec(f, &[])
}

/// One occurrence of a variable inside a formula, with the sort it
/// must have at this position. Untagged usage means "any sort".
#[derive(Debug, Clone)]
struct VarUse {
    name: String,
    /// `None` means "any sort" (untagged use); otherwise the variable
    /// is constrained by its position to be of this sort kind.
    expected: Option<u8>,
    raw: VarSpec,
}

fn kind_of(s: &SortHint) -> u8 {
    match s {
        SortHint::Fresh | SortHint::Suffix(SuffixSort::Fresh) => 0,
        SortHint::Pub   | SortHint::Suffix(SuffixSort::Pub) => 1,
        SortHint::Node  | SortHint::Suffix(SuffixSort::Node) => 2,
        SortHint::Nat   | SortHint::Suffix(SuffixSort::Nat) => 3,
        SortHint::Msg   | SortHint::Suffix(SuffixSort::Msg) => 4,
        SortHint::Untagged => 4, // default to msg
    }
}

/// True if `s` is an explicit sort prefix (sigil/suffix), not untagged.
fn is_explicit_sort(s: &SortHint) -> bool {
    !matches!(s, SortHint::Untagged)
}

/// Collect every variable use inside a term, treating each as a
/// "Msg-or-anything" position (no positional coercion).
fn term_var_uses(t: &Term, out: &mut Vec<VarUse>) {
    match t {
        Term::Var(v) => {
            // Reserved nullary constants (`true`, etc.) parsed as
            // untagged Var should not be treated as free variables.
            if matches!(v.sort, SortHint::Untagged)
                && is_known_nullary_constant_name(&v.name)
            { return; }
            out.push(VarUse {
                name: v.name.clone(),
                expected: if is_explicit_sort(&v.sort) { Some(kind_of(&v.sort)) } else { None },
                raw: v.clone(),
            });
        }
        Term::App(_, args) | Term::Pair(args) =>
            for a in args { term_var_uses(a, out); },
        Term::AlgApp(_, a, b) => { term_var_uses(a, out); term_var_uses(b, out); }
        Term::Diff(a, b) | Term::BinOp(_, a, b) => {
            term_var_uses(a, out); term_var_uses(b, out);
        }
        Term::PatMatch(inner) => term_var_uses(inner, out),
        _ => {}
    }
}

/// Collect var-uses appearing in a temporal position — i.e. the
/// argument of `@`, `Less`, or `Last`. Untagged variables here are
/// implicitly node-sort.
fn term_var_uses_temporal(t: &Term, out: &mut Vec<VarUse>) {
    match t {
        Term::Var(v) => out.push(VarUse {
            name: v.name.clone(),
            // Whether explicit or untagged, the position forces node.
            expected: Some(2 /* node */),
            raw: v.clone(),
        }),
        // Temporal terms shouldn't be compound, but be tolerant.
        _ => term_var_uses(t, out),
    }
}

fn first_free_var_in_atom(a: &Atom, scope: &[VarSpec]) -> Option<VarSpec> {
    let mut uses = Vec::new();
    match a {
        Atom::Eq(x, y) | Atom::LessMset(x, y) | Atom::Subterm(x, y) => {
            term_var_uses(x, &mut uses); term_var_uses(y, &mut uses);
        }
        Atom::Less(x, y) => {
            term_var_uses_temporal(x, &mut uses);
            term_var_uses_temporal(y, &mut uses);
        }
        Atom::Action(fact, t) => {
            for arg in &fact.args { term_var_uses(arg, &mut uses); }
            term_var_uses_temporal(t, &mut uses);
        }
        Atom::Last(t) => term_var_uses_temporal(t, &mut uses),
        Atom::Pred(fact) => {
            for arg in &fact.args { term_var_uses(arg, &mut uses); }
        }
    }
    for u in uses {
        let bound = scope.iter().any(|q| {
            if q.name != u.name { return false; }
            // Sort agreement:
            // - if the use position constrains the sort (Some(k)), the
            //   binder's kind must match k;
            // - otherwise any binder of that name is fine.
            match u.expected {
                Some(k) => kind_of(&q.sort) == k,
                None    => true,
            }
        });
        if !bound { return Some(u.raw); }
    }
    None
}

/// Within each rule, a given variable name must use a consistent sort.
/// `~x` and `$x` in the same rule trigger this check.
pub fn variable_sort_clashes(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let mut by_name: BTreeMap<String, BTreeSet<&'static str>> = BTreeMap::new();
        let mut all_vars: Vec<VarSpec> = Vec::new();
        for f in r.premises.iter().chain(&r.actions).chain(&r.conclusions) {
            all_vars.extend(fact_vars(f));
        }
        for v in &all_vars {
            let label: &'static str = if is_fresh_sort(&v.sort) { "fresh" }
                else if is_pub_sort(&v.sort) { "pub" }
                else if is_node_sort(&v.sort) { "node" }
                else if is_nat_sort(&v.sort) { "nat" }
                else if matches!(v.sort, SortHint::Suffix(SuffixSort::Msg) | SortHint::Msg) { "msg" }
                else { "?" };
            // Skip "?" (untagged) — we only flag clashes between explicit sorts.
            if label != "?" {
                by_name.entry(v.name.clone()).or_default().insert(label);
            }
        }
        for (name, sorts) in by_name.iter().filter(|(_, s)| s.len() > 1) {
            out.push(WfError::new(
                "Variable with mismatching sorts or capitalization",
                format!("rule `{}': variable `{}' used at sorts {:?}",
                    r.name, name, sorts.iter().cloned().collect::<Vec<_>>())));
        }
    }
    out
}

// =============================================================================
// Nat sorts: `%+` requires nat operands
// =============================================================================

pub fn nat_well_sorted_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        for t in rule_terms(r) {
            collect_nat_violations(t, r, &mut out);
        }
    }
    for l in theory_lemmas(thy) {
        let _ = l;
        // formulas would need a separate walker; skipped for now since
        // the nat tests that fire sit inside rules.
    }
    out
}

fn collect_nat_violations(t: &Term, r: &Rule, out: &mut WfReport) {
    if let Term::BinOp(BinOp::NatPlus, a, b) = t {
        check_nat_operand(a, r, out);
        check_nat_operand(b, r, out);
    }
    match t {
        Term::App(_, args) | Term::Pair(args) => for a in args { collect_nat_violations(a, r, out); },
        Term::AlgApp(_, a, b) => { collect_nat_violations(a, r, out); collect_nat_violations(b, r, out); }
        Term::Diff(a, b) | Term::BinOp(_, a, b) => {
            collect_nat_violations(a, r, out);
            collect_nat_violations(b, r, out);
        }
        Term::PatMatch(inner) => collect_nat_violations(inner, r, out),
        _ => {}
    }
}

fn check_nat_operand(t: &Term, r: &Rule, out: &mut WfReport) {
    match t {
        Term::Var(v) if !is_nat_sort(&v.sort) => {
            // Untagged is OK at parse level (sort inference would
            // refine), but explicit non-nat sorts trigger.
            if matches!(v.sort, SortHint::Untagged) { return; }
            out.push(WfError::new("Nat Sorts",
                format!("rule `{}': variable `{}' must be of sort nat",
                    r.name, render_var(v))));
        }
        Term::NatOne | Term::NatLit(_) => {}
        Term::BinOp(BinOp::NatPlus, a, b) => {
            check_nat_operand(a, r, out);
            check_nat_operand(b, r, out);
        }
        // Anything else (pub literal, function app, fresh literal,
        // etc.) is rejected.
        Term::PubLit(_) | Term::FreshLit(_) | Term::App(_, _) | Term::Pair(_)
        | Term::AlgApp(_, _, _) | Term::Diff(_, _) | Term::Number(_)
        | Term::NumberOne | Term::DhNeutral | Term::PatMatch(_) => {
            out.push(WfError::new("Nat Sorts",
                format!("rule `{}': operand must be of sort nat: {:?}", r.name, t)));
        }
        Term::Var(_) => {} // Untagged var, accepted.
        Term::BinOp(_, _, _) => {
            out.push(WfError::new("Nat Sorts",
                format!("rule `{}': operand must be of sort nat: {:?}", r.name, t)));
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_theory;

    fn parse(src: &str) -> Theory {
        parse_theory(src, &["diff"]).expect("parse")
    }

    #[test]
    fn unbound_var_detected() {
        let t = parse("theory T begin rule R: [] --[ ]-> [ Out(~k) ] end");
        let r = check_theory(&t);
        assert!(topics(&r).contains("Unbound variables"), "report: {:?}", r);
    }

    #[test]
    fn fact_arity_clash_detected() {
        let t = parse(r#"theory T begin
            rule R1: [Fr(~x)] --[ ]-> [Foo(~x)]
            rule R2: [Fr(~x), Fr(~y)] --[ ]-> [Foo(~x, ~y)]
        end"#);
        let r = check_theory(&t);
        assert!(topics(&r).contains("Fact arity issues"));
    }

    #[test]
    fn special_facts_misuse_detected() {
        let t = parse("theory T begin rule R: [Out(x)] --[ ]-> [] end");
        let r = check_theory(&t);
        assert!(topics(&r).contains("Special facts"));
    }

    #[test]
    fn reserved_name_detected() {
        let t = parse(r#"theory T begin
            rule R: [Fr(~k)] --[ ]-> [KU(~k)]
        end"#);
        let r = check_theory(&t);
        assert!(topics(&r).contains("Reserved names"));
    }
}
