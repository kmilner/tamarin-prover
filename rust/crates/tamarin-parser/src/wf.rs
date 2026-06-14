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
    /// Short title used for grouping/ordering — matches HS's
    /// `underlineTopic` argument exactly (e.g. `"Reserved names"`).
    pub topic: String,
    /// Fully-formatted HS-style block for this entry.  When multiple
    /// `WfError`s share a topic the `format_wf_block` formatter
    /// concatenates the messages, separated by blank lines, beneath
    /// the topic header (which is part of `message`).
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
    // (Wellformedness.hs:1270-1287).  The order here is close but NOT
    // identical: HS's `ruleSortsReport` (the "Variable with mismatching
    // sorts" / sort-clash check) runs before factReports, whereas we run
    // it later inside `formula_terms_report`; and `left_right_rule_report`
    // (the diff-only Left/Right check) is interleaved here rather than
    // appearing where HS places `leftRightRuleReportDiff`.
    let mut report = Vec::new();
    report.extend(unbound_report(thy));
    report.extend(fresh_names_report(thy));
    report.extend(public_names_report(thy));
    report.extend(left_right_rule_report(thy));    // leftRightRuleReportDiff (diff only)
    // HS `ruleSortsReport` (sortsClashCheck) is ported as
    // `variable_sort_clashes`, run later via `formula_terms_report`.
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
// Check that CLI --prove/--lemma arguments name actual lemmas in the theory
// =============================================================================

/// Port of HS `checkIfLemmasInTheory` (Wellformedness.hs:1156-1171).
///
/// HS threads `_lemmasToProve` through the theory's `Options` record.
/// In the Rust port the CLI args are not embedded in the parser AST,
/// so we take them as a separate parameter.
///
/// Semantics (mirror of `findNotProvedLemmas` / `lemmaChecker`):
///   - An empty `lemma_names` slice (no `--prove` / `--lemma` flag)
///     means "prove all" → skip the check.
///   - A list that is exactly `[""]` (bare `--prove` with no value)
///     also means "all" → skip.
///   - Otherwise: for each name in `lemma_names`, it "corresponds" if
///     • there is a theory lemma whose name equals it exactly, OR
///     • the name ends with `*` and its prefix is a prefix of at least
///     one theory-lemma name.
///     Names that don't correspond are collected; if any exist the WF
///     check fires.
pub fn check_if_lemmas_in_theory(lemma_names: &[String], thy: &Theory) -> WfReport {
    // HS: `| lemmaArgsNames == [[]] = []`  (Wellformedness.hs:1158)
    // HS stores lemmaArgsNames as [String]; [[]] is [""] (a list
    // containing exactly one empty string), which means bare `--prove`
    // with no argument value.  Skip the check ONLY in that case.
    //
    // When lemma_names is EMPTY (no --prove at all) → also skip.
    // When lemma_names has MIXED entries (e.g. `--prove --lemma=BadX`
    // → ["", "BadX"]) the HS condition fails so the check DOES run —
    // the empty string is reported as "not found" too (faithfulness
    // requires we keep empty strings in the probe list).
    if lemma_names.is_empty() {
        return Vec::new();
    }
    // Exactly one entry and it is empty → bare `--prove` → skip.
    if lemma_names == [""] {
        return Vec::new();
    }
    // Collect non-empty names for the "matches any lemma" test;
    // empty strings are kept in the fold below since HS does NOT
    // filter them (they trivially fail argFilter).
    let all_names: Vec<&str> = lemma_names.iter().map(|s| s.as_str()).collect();

    let theory_lemma_names: Vec<&str> = theory_lemmas(thy)
        .into_iter()
        .map(|l| l.name.as_str())
        .collect();

    // HS `findNotProvedLemmas` (Wellformedness.hs:1141) is a `foldl`
    // that PREPENDS mismatches.  HS's Arguments list is built with
    // `addArg` which prepends each CLI flag, so the stored arg list is
    // in REVERSE CLI order.  `findArg` returns them in that reversed
    // order; `foldl`-prepend of a reversed list re-reverses → the final
    // `notProvedLemmas` is in ORIGINAL CLI order.
    //
    // RS's `lemma_names` is already in CLI order (no prepend in
    // `parse_args`), so a simple forward-iterate-and-push yields the
    // same result as the double-reversed HS fold.
    let mut not_proved: Vec<&str> = Vec::new();
    for name in all_names.iter() {
        if !arg_matches_any_lemma(name, &theory_lemma_names) {
            not_proved.push(name);
        }
    }

    if not_proved.is_empty() {
        return Vec::new();
    }

    // HS topic: `underlineTopic "Check presence of the --prove/--lemma
    // arguments in theory"` (Wellformedness.hs:1169).
    let topic_str = "Check presence of the --prove/--lemma arguments in theory";
    // HS body: `vcat [text $ "--> '" ++ intercalate "', '" notProvedLemmas
    //   ++ "'" ++ " from arguments do(es) not correspond ..."]`
    // Rendered via `prettyWfErrorReport` → `nest 2`:
    //   "<topic>\n<===>\n\n  --> '<names>' from arguments ...\n"
    let names_str = not_proved.join("', '");
    let body_line = format!(
        "--> '{}' from arguments do(es) not correspond to a specified lemma in the theory ",
        names_str,
    );

    // Build the message in the same shape that format_wf_block expects:
    // the topic header (underlineTopic output) followed by a blank line,
    // followed by the 2-space-indented body line.
    // HS prettyWfErrorReport: `text topic $-$ (nest 2 . vcat ... $ map snd errs)`
    // `text topic` renders the underlineTopic string (title\n====\n),
    // `$-$` appends one more newline, so we get title\n====\n\n<body>.
    let mut msg = String::new();
    msg.push_str(&underline_topic(topic_str));
    msg.push('\n');                   // blank line between header and body
    msg.push_str("  ");              // nest 2
    msg.push_str(&body_line);
    msg.push('\n');

    vec![WfError::new(topic_str, msg)]
}

/// True if `arg` "corresponds" to at least one lemma name in
/// `theory_lemmas`.  Mirrors HS `lemmaChecker`:
///   - suffix `*` → prefix match on the lemma name (no `*` in result)
///   - otherwise  → exact equality
fn arg_matches_any_lemma(arg: &str, theory_lemmas: &[&str]) -> bool {
    if let Some(prefix) = arg.strip_suffix('*') {
        theory_lemmas.iter().any(|n| n.starts_with(prefix))
    } else {
        theory_lemmas.contains(&arg)
    }
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

/// Build an HS `underlineTopic` block: `"<title>\n<====>\n"` where the
/// underline matches the title length exactly (counting any trailing
/// space).  Mirrors `underlineTopic` in `Theory.Tools.Wellformedness`.
pub fn underline_topic(title: &str) -> String {
    let len = title.chars().count();
    let mut s = String::with_capacity(title.len() + len + 2);
    s.push_str(title);
    s.push('\n');
    for _ in 0..len { s.push('='); }
    s.push('\n');
    s
}

/// Pretty-print a parser-AST fact in HS's `prettyLNFact` style:
/// `!Name( arg, arg, ... )` for persistent, `Name( arg, arg, ... )`
/// for linear.  Internal spaces match `nestShort'`.
fn pp_wf_fact(fa: &Fact) -> String {
    let mut s = String::new();
    if fa.persistent { s.push('!'); }
    s.push_str(&fa.name);
    s.push_str("( ");
    for (i, a) in fa.args.iter().enumerate() {
        if i > 0 { s.push_str(", "); }
        pp_wf_term(a, &mut s);
    }
    s.push_str(" )");
    s
}

fn pp_wf_term(t: &Term, out: &mut String) {
    use Term::*;
    match t {
        Var(v) => {
            out.push_str(sort_prefix(&v.sort));
            out.push_str(&v.name);
            if v.idx > 0 { out.push('.'); out.push_str(&v.idx.to_string()); }
        }
        PubLit(s) => { out.push('\''); out.push_str(s); out.push('\''); }
        FreshLit(s) => { out.push_str("~'"); out.push_str(s); out.push('\''); }
        NatLit(s) => { out.push_str("%'"); out.push_str(s); out.push('\''); }
        Number(n) => out.push_str(&n.to_string()),
        NumberOne => out.push('1'),
        NatOne => out.push_str("%1"),
        DhNeutral => out.push_str("1:msg"),
        Pair(items) => {
            out.push('<');
            for (i, it) in items.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                pp_wf_term(it, out);
            }
            out.push('>');
        }
        App(name, args) => {
            out.push_str(name);
            if !args.is_empty() {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { out.push_str(", "); }
                    pp_wf_term(a, out);
                }
                out.push(')');
            }
        }
        AlgApp(name, l, r) => {
            // HS canonicalises `aenc{m}pk` as `aenc(m, pk)`.
            out.push_str(name);
            out.push('(');
            pp_wf_term(l, out);
            out.push_str(", ");
            pp_wf_term(r, out);
            out.push(')');
        }
        Diff(l, r) => {
            out.push_str("diff(");
            pp_wf_term(l, out);
            out.push_str(", ");
            pp_wf_term(r, out);
            out.push(')');
        }
        BinOp(op, l, r) => {
            use crate::ast::BinOp as B;
            let sym = match op {
                B::Exp => "^",
                B::Mult => "*",
                B::Union => "++",
                B::Xor => "\u{2295}",
                B::NatPlus => "%+",
            };
            // HS builds AC operators (Mult/Union/Xor/NatPlus) via `fAppAC`,
            // which flattens the chain, sorts the operands (Ord LTerm), and
            // renders them parenthesised by `prettyTerm` (e.g. `(%x%+%1%+%1)`).
            // Exp is NOT AC: rendered binary, no surrounding parens.
            if matches!(op, B::Mult | B::Union | B::Xor | B::NatPlus) {
                let mut flat: Vec<&Term> = Vec::new();
                flatten_ac(*op, t, &mut flat);
                flat.sort_by(|a, b| cmp_wf_term(a, b));
                out.push('(');
                for (i, a) in flat.iter().enumerate() {
                    if i > 0 { out.push_str(sym); }
                    pp_wf_term(a, out);
                }
                out.push(')');
            } else {
                pp_wf_term(l, out);
                out.push_str(sym);
                pp_wf_term(r, out);
            }
        }
        PatMatch(inner) => { out.push('='); pp_wf_term(inner, out); }
    }
}

/// Substitute every `let`-binding of a rule into its facts, mirroring HS,
/// whose rule parser inlines the `let` block before building the
/// `ProtoRuleE` (so wellformedness checks see fully-substituted facts).
///
/// HS `letBlock` (Parser/Let.hs:34) is `foldr1 compose` over singleton
/// substitutions — equivalent to applying each binding sequentially in
/// REVERSE binding order ("bottom-up").  Backward references expand;
/// FORWARD references survive as free variables.  Matches
/// `elaborate::apply_let_block`.
fn rule_facts_with_lets(r: &Rule) -> (Vec<Fact>, Vec<Fact>, Vec<Fact>) {
    let mut prems = r.premises.clone();
    let mut acts = r.actions.clone();
    let mut concs = r.conclusions.clone();
    for b in r.let_block.iter().rev() {
        for f in prems.iter_mut() { subst_let_fact(f, &b.var, &b.value); }
        for f in acts.iter_mut()  { subst_let_fact(f, &b.var, &b.value); }
        for f in concs.iter_mut() { subst_let_fact(f, &b.var, &b.value); }
    }
    (prems, acts, concs)
}

fn subst_let_fact(f: &mut Fact, key: &Term, val: &Term) {
    for a in f.args.iter_mut() {
        *a = subst_let_term(a, key, val);
    }
}

fn subst_let_term(t: &Term, key: &Term, val: &Term) -> Term {
    if t == key { return val.clone(); }
    use Term::*;
    match t {
        App(name, args) =>
            App(name.clone(), args.iter().map(|a| subst_let_term(a, key, val)).collect()),
        AlgApp(name, a, b) =>
            AlgApp(name.clone(),
                Box::new(subst_let_term(a, key, val)),
                Box::new(subst_let_term(b, key, val))),
        Pair(args) =>
            Pair(args.iter().map(|a| subst_let_term(a, key, val)).collect()),
        Diff(a, b) =>
            Diff(Box::new(subst_let_term(a, key, val)),
                 Box::new(subst_let_term(b, key, val))),
        BinOp(op, a, b) =>
            BinOp(*op, Box::new(subst_let_term(a, key, val)),
                       Box::new(subst_let_term(b, key, val))),
        PatMatch(a) => PatMatch(Box::new(subst_let_term(a, key, val))),
        Var(_) | PubLit(_) | FreshLit(_) | NatLit(_) | Number(_)
        | NumberOne | NatOne | DhNeutral => t.clone(),
    }
}

/// Flatten an AC `BinOp` chain (same operator) into its operand list,
/// mirroring HS `fAppAC`'s flatten-then-sort (Term/Term/Raw.hs:118-128).
fn flatten_ac<'a>(op: crate::ast::BinOp, t: &'a Term, out: &mut Vec<&'a Term>) {
    match t {
        Term::BinOp(inner, l, r) if *inner == op => {
            flatten_ac(op, l, out);
            flatten_ac(op, r, out);
        }
        _ => out.push(t),
    }
}

/// HS `Ord LTerm` for the subset of parser terms we render here.
///
/// HS-faithful class order (Term/Term/Raw.hs:72-74, VTerm.hs:56-57):
/// `LIT _ < FAPP _ _`, and within `LIT`, `Con < Var`, with constant Names
/// ordered by NameTag (Fresh < Pub < Nat, LTerm.hs:215).  The nullary
/// builtins `1`/`%1`/`DH-neutral` are `fAppNoEq … []` so they live in the
/// FAPP class.  Within a class we fall back to a structural tie-break that
/// is enough for the AC operand lists that arise here.
fn cmp_wf_term(a: &Term, b: &Term) -> std::cmp::Ordering {
    fn class(t: &Term) -> (u8, u8) {
        use Term::*;
        match t {
            // LIT (Con name): constants, by NameTag Fresh<Pub<Nat.
            FreshLit(_) => (0, 0),
            PubLit(_) => (0, 1),
            NatLit(_) => (0, 2),
            Number(_) => (0, 3),
            // LIT (Var v): variables sort after all constants.
            Var(_) => (0, 4),
            // FAPP: nullary builtins are NoEq applications, not literals.
            NumberOne => (1, 0),
            NatOne => (1, 1),
            DhNeutral => (1, 2),
            App(..) => (1, 3),
            AlgApp(..) => (1, 4),
            Pair(_) => (1, 5),
            Diff(..) => (1, 6),
            BinOp(..) => (1, 7),
            PatMatch(_) => (1, 8),
        }
    }
    let (ca, sa) = class(a);
    let (cb, sb) = class(b);
    if ca != cb { return ca.cmp(&cb); }
    if sa != sb { return sa.cmp(&sb); }
    use Term::*;
    match (a, b) {
        (Var(v1), Var(v2)) => {
            // HS Ord LVar = (idx, sort, name) (LTerm.hs:521-523).
            v1.idx.cmp(&v2.idx)
                .then_with(|| sort_tag(&v1.sort).cmp(&sort_tag(&v2.sort)))
                .then_with(|| v1.name.cmp(&v2.name))
        }
        (PubLit(s1), PubLit(s2)) => s1.cmp(s2),
        (FreshLit(s1), FreshLit(s2)) => s1.cmp(s2),
        (NatLit(s1), NatLit(s2)) => s1.cmp(s2),
        (Number(n1), Number(n2)) => n1.cmp(n2),
        _ => std::cmp::Ordering::Equal,
    }
}

/// HS LSort declaration order (Term/LTerm.hs:161-166):
/// Pub < Fresh < Msg < Node < Nat.
fn sort_tag(s: &SortHint) -> u8 {
    use SortHint::*;
    use SuffixSort as SS;
    match s {
        Pub | Suffix(SS::Pub) => 0,
        Fresh | Suffix(SS::Fresh) => 1,
        Msg | Suffix(SS::Msg) | Untagged => 2,
        Node | Suffix(SS::Node) => 3,
        Nat | Suffix(SS::Nat) => 4,
    }
}

fn sort_prefix(s: &SortHint) -> &'static str {
    use SortHint::*;
    use SuffixSort as SS;
    match s {
        Pub | Suffix(SS::Pub) => "$",
        Fresh | Suffix(SS::Fresh) => "~",
        Node | Suffix(SS::Node) => "#",
        Nat | Suffix(SS::Nat) => "%",
        Msg | Suffix(SS::Msg) | Untagged => "",
    }
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
        // HS checks the let-substituted `ProtoRuleE`, so the emitted facts
        // carry their fully-inlined terms (Term/Term/Raw.hs fAppAC order).
        let (prems, acts, concs) = rule_facts_with_lets(r);
        let bad_lhs: Vec<&Fact> = prems.iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str()))
            .collect();
        let bad_acts: Vec<&Fact> = acts.iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str())
                || matches!(f.name.as_str(), "In" | "Out" | "Fr"))
            .collect();
        let bad_rhs: Vec<&Fact> = concs.iter()
            .filter(|f| KLOG_NAMES.contains(&f.name.as_str()))
            .collect();
        for (msg, fs) in [
            ("on left-hand-side", bad_lhs),
            ("on the middle", bad_acts),
            ("on the right-hand-side", bad_rhs),
        ] {
            if !fs.is_empty() {
                // HS `reservedFactNameRules'` (Wellformedness.hs:530-550):
                //   (underlineTopic "Reserved names",
                //      text ("Rule " ++ quote (showRuleCaseName ru))
                //      <-> text ("contains facts with reserved names"++msg) $-$
                //      nest 2 (fsep $ punctuate comma $ map prettyLNFact fas))
                // grouped/nested by `prettyWfErrorReport` (text topic $-$
                // nest 2 body): the rule line gets 2-space indent, the fact
                // line 4-space (2 from ppTopic + 2 from the inner nest 2).
                let facts: Vec<String> =
                    fs.iter().map(|f| pp_wf_fact(f)).collect();
                let mut s = String::new();
                s.push_str(&underline_topic("Reserved names"));
                s.push('\n');
                s.push_str(&format!(
                    "  Rule `{}' contains facts with reserved names {}:\n",
                    r.name, msg,
                ));
                s.push_str("    ");
                s.push_str(&facts.join(", "));
                s.push('\n');
                out.push(WfError::new("Reserved names", s));
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
    /// The actual fact, retained so we can render it in WF messages.
    fact: Fact,
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
                fact: f.clone(),
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

    // HS emits one block per issue type when ANY clash group exhibits
    // it.  Collect first, then emit.
    let mut cap_groups: Vec<&Vec<&FactObservation>> = Vec::new();
    let mut arity_groups: Vec<&Vec<&FactObservation>> = Vec::new();
    let mut mult_groups: Vec<&Vec<&FactObservation>> = Vec::new();
    for (_, group) in groups.iter().filter(|(_, g)| g.len() >= 2) {
        let cap_set: BTreeSet<&str> = group.iter().map(|o| o.name.as_str()).collect();
        let arity_set: BTreeSet<usize> = group.iter().map(|o| o.arity).collect();
        let mult_set: BTreeSet<bool> = group.iter().map(|o| o.persistent).collect();
        if cap_set.len() > 1 { cap_groups.push(group); }
        if arity_set.len() > 1 { arity_groups.push(group); }
        if mult_set.len() > 1 { mult_groups.push(group); }
    }

    if !cap_groups.is_empty() {
        let msg = "Fact names are case-sensitive, different capitalizations are \
                  considered as different facts, i.e., Fact() is different from FAct(). \n\
                  Check the capitalization of your fact names.";
        out.push(format_fact_clash_block(
            "Fact capitalization issues",
            msg,
            &cap_groups,
            |o| format!("capitalization {:?}", o.name),
        ));
    }
    if !arity_groups.is_empty() {
        let msg = "Same fact is used with different arities, \
                  i.e., Fact('A','B') is different from Fact('A'). \n\
                  Check the arguments of your facts.";
        out.push(format_fact_clash_block(
            "Fact arity issues",
            msg,
            &arity_groups,
            |o| format!("arity {}", o.arity),
        ));
    }
    if !mult_groups.is_empty() {
        let msg = "Same fact is used with different multiplicities, \
                  i.e., !Fact() (Persistent fact) exists along with Fact() (Linear) in your rules. \n\
                  Check the multiplicity (persistence) of your facts.";
        out.push(format_fact_clash_block(
            "Fact multiplicity issues",
            msg,
            &mult_groups,
            |o| format!("multiplicity (persistence) {}",
                if o.persistent { "Persistent" } else { "Linear" }),
        ));
    }
    out
}

/// Emit one HS-style WfError block: title + underline + intro msg +
/// per-clash numbered detail.  Layout matches the byte output of HS's
/// `formatMultipIssue` / `formatArityIssue` / `formatCapIssue`
/// (Wellformedness.hs:660-674).
fn format_fact_clash_block<F>(
    title: &str,
    intro: &str,
    groups: &[&Vec<&FactObservation>],
    detail: F,
) -> WfError
where F: Fn(&FactObservation) -> String,
{
    let mut s = String::new();
    s.push_str(&underline_topic(title));
    s.push('\n');
    s.push_str(intro);
    s.push('\n');
    s.push_str("  \n");  // trailing 2-space line from HS `text ""`
    for group in groups {
        s.push('\n');
        let name = group[0].name.to_lowercase();
        s.push_str(&format!("  Fact `{}':\n", name));
        s.push('\n');
        for (i, obs) in group.iter().enumerate() {
            if i > 0 {
                s.push_str("    \n");  // 4-space trailing line
            }
            s.push_str(&format!(
                "    {}. Rule `{}', {}\n",
                i + 1,
                obs.rule_name,
                detail(obs),
            ));
            s.push_str(&format!("         {}\n", pp_wf_fact(&obs.fact)));
        }
        s.push_str("  \n");  // 2-space trailing line after the group
    }
    WfError::new(title, s)
}

// =============================================================================
// Fact occurs in some LHS but not in any RHS
// =============================================================================

pub fn fact_lhs_occur_no_rhs(thy: &Theory) -> WfReport {
    // Mirrors HS `factLhsOccurNoRhs` (Wellformedness.hs:233-249): for
    // every premise fact that no rule produces, find a "similar" RHS
    // (same name, may differ in arity/multiplicity) on some rule and
    // emit a numbered suggestion list.
    //
    // Title carries a single trailing space, matching HS's source-literal
    // `"Facts occur in the left-hand-side but not in any right-hand-side "`.
    let title = "Facts occur in the left-hand-side but not in any right-hand-side ";

    let mut rhs_by_name: BTreeMap<String, Vec<(String, Fact)>> = BTreeMap::new();
    for r in theory_rules(thy) {
        for f in &r.conclusions {
            rhs_by_name.entry(f.name.clone())
                .or_default()
                .push((r.name.clone(), f.clone()));
        }
    }

    // Detect orphan premises (LHS facts with no exactly-matching RHS).
    let mut orphan_pairs: Vec<(String, Fact, Option<(String, Fact)>)> = Vec::new();
    for r in theory_rules(thy) {
        for f in &r.premises {
            if is_builtin_fact_name(&f.name) { continue; }
            let exact_match = rhs_by_name.get(&f.name)
                .map(|v| v.iter().any(|(_, rf)|
                    rf.args.len() == f.args.len() && rf.persistent == f.persistent))
                .unwrap_or(false);
            if exact_match { continue; }
            // Suggest a same-name RHS that differs in arity/multiplicity.
            let suggestion = rhs_by_name.get(&f.name)
                .and_then(|v| v.first())
                .map(|(rn, rf)| (rn.clone(), rf.clone()));
            orphan_pairs.push((r.name.clone(), f.clone(), suggestion));
        }
    }

    if orphan_pairs.is_empty() { return Vec::new(); }

    let mut s = String::new();
    s.push_str(&underline_topic(title));
    s.push('\n');
    // HS `numbered'` = `numbered (text "")`: items are interspersed with
    // `text ""` separators and joined by `$-$`.  `text ""` at indent 2
    // (from the `nest 2` in the caller) renders as `"  "` (2 spaces).
    // Result: item1\n  \nitem2\n  \nitem3\n (blank 2-space lines between items).
    let last_idx = orphan_pairs.len() - 1;
    for (i, (rule_name, fa, suggestion)) in orphan_pairs.iter().enumerate() {
        let primary = format!(
            "in rule \"{}\":  factName `{}' arity: {} multiplicity: {}",
            rule_name,
            fa.name,
            fa.args.len(),
            if fa.persistent { "Persistent" } else { "Linear" },
        );
        let line = match suggestion {
            Some((sug_rule, sug_fa)) => format!(
                "  {}. {}. Perhaps you want to use the fact in rule \"{}\":  factName `{}' arity: {} multiplicity: {}",
                i + 1, primary, sug_rule, sug_fa.name, sug_fa.args.len(),
                if sug_fa.persistent { "Persistent" } else { "Linear" },
            ),
            None => format!("  {}. {}", i + 1, primary),
        };
        s.push_str(&line);
        s.push('\n');
        // HS `numbered (text "")` inserts `text ""` between items.
        // At 2-space indent this renders as "  \n".
        if i < last_idx {
            s.push_str("  \n");
        }
    }

    vec![WfError::new(title, s)]
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

/// Collect every name declared by `functions: <name>/0 ...` blocks at
/// any depth in the theory.  HS-faithful: the parser registers these
/// in its `funSig` so `nullaryApp` resolves bare `<name>` tokens to
/// `FApp (NoEq <sym>) []` rather than `Var <name>`
/// (`lib/theory/src/Theory/Text/Parser/Term.hs::nullaryApp`).  In the
/// Rust port that resolution happens during elaboration, but WF runs
/// on the un-elaborated parser AST — so any walker that classifies
/// `Var name` as "really a variable" needs this set to deny-list the
/// 0-arity user funs.  Built-in nullaries (`signing`'s `true`, DH's
/// `1`, etc.) are NOT included here; they live in the builtin sig
/// which is registered at elaborate-time.  Today we only need to
/// shadow user-declared 0-arity funs (wireguard.spthy's `true/0`).
fn collect_nullary_fun_names(thy: &Theory) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = BTreeSet::new();
    for it in &thy.items {
        if let TheoryItem::Functions(decls) = it {
            for d in decls {
                if d.arg_types.is_empty() {
                    out.insert(d.name.clone());
                }
            }
        }
    }
    out
}

/// Collect a rule's unbound variables (conclusion/action vars NOT in
/// any premise / let-binding).  Returns the list in first-occurrence
/// order, deduped, excluding pub-sort variables (which are implicitly
/// adversary-known and so always bound) and excluding names declared
/// as 0-arity functions (those are nullary function calls, not
/// variables — HS resolves them via `nullaryApp` at parse-time).
fn collect_rule_unbound_vars(r: &Rule, nullary_funs: &BTreeSet<String>) -> Vec<VarSpec> {
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
            if nullary_funs.contains(&v.name) { continue; }
            // Builtin nullary constants (e.g. XOR's `zero`, DH's
            // `DH_neutral`) parse as bare identifiers in the surface
            // syntax but semantically denote 0-arity functions.  HS's
            // parser binds them via `nullaryApp` so they never appear
            // as variables in the rule AST; RS's parser still surfaces
            // them as `Term::Var` and relies on this check to skip
            // them when classifying "unbound".  Without this skip,
            // rules like CRxor's `responder` (`Neq(na, zero)`) get
            // bogus "has unbound variables: zero" warnings.
            if is_known_nullary_constant_name(&v.name) { continue; }
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
    // HS `unboundReport` (Wellformedness.hs:514-519) produces one `WfError`
    // PER offending rule, all sharing the topic "Unbound variables".  The
    // WARNING count printed in the summary is `length rep` (Batch.hs:245),
    // i.e. the number of these un-grouped entries — so we must emit one
    // entry per rule, NOT a single aggregated block.
    //
    // The renderer `prettyWfErrorReport` (Wellformedness.hs:118-125) then
    // `groupOn`s by topic and lays each group out as
    //   `text topic $-$ (nest 2 . vcat . intersperse (text "") $ map snd errs)`.
    // i.e. the underlineTopic header is emitted ONCE for the group, the
    // per-rule bodies are indented by 2 spaces and separated by a 2-space
    // blank line.  Each body is `text info $-$ nest 2 (prettyVarList vars)`
    // (Wellformedness.hs:497-498), so the `rule ... has unbound variables:`
    // line gets 2 spaces and the variable list 2+2 = 4 spaces.  RS's
    // `format_wf_block` applies that group-level header + 2-space layout
    // (see below); each entry here carries ONLY its body (`snd err`).
    let nullary_funs = collect_nullary_fun_names(thy);
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        let unbound = collect_rule_unbound_vars(r, &nullary_funs);
        if !unbound.is_empty() {
            // HS `prettyVarList = fsep . punctuate comma . map prettyLVar`
            // (TheoryObject.hs:815-816): comma-separated, word-wrapped.  The
            // sibling `reservedFactNameRules` block renders its list the
            // same way; we comma-join at the 4-space inner `nest 2` indent
            // (variable lists are short, so the fsep wrap never triggers in
            // practice — identical bytes to HS for the common case).
            let names: Vec<String> = unbound.iter()
                .map(render_var)
                .collect();
            // Body only: `  rule `{name}' has unbound variables: ` (2-space
            // ppTopic nest, trailing space from HS's `info`) then the
            // variable list at 4 spaces.  format_wf_block adds the header.
            out.push(WfError::new("Unbound variables", format!(
                "  rule `{}' has unbound variables: \n    {}",
                r.name, names.join(", "))));
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
    let nullary_funs = collect_nullary_fun_names(thy);
    let mut per_rule: Vec<(String, Vec<String>)> = Vec::new();
    for r in theory_rules(thy) {
        if r.attributes.iter().any(|a| matches!(a,
            crate::ast::RuleAttr::NoDerivCheck)) { continue; }
        let unbound = collect_rule_unbound_vars(r, &nullary_funs);
        if unbound.is_empty() { continue; }
        // HS shows the LVar (sort prefix included): MessageDerivationChecks.hs:138
        let names: Vec<String> = unbound.iter()
            .map(render_var)
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

/// HS `multRestrictedReport'` (Wellformedness.hs:1047-1099). HS only
/// flags a rule when:
///   (a) it has any multiplication term `*` in its RHS conclusions, OR
///   (b) abstracting reducible-headed terms in the rule introduces new
///       unbound (non-public) vars in the RHS that weren't present
///       pre-abstraction.
///
/// HS does NOT warn on every rule whose LHS contains any reducible op
/// (xor / exp / inv) — those are explicitly permitted as long as (a)
/// and (b) hold.
///
/// Implementation note: a previous draft of this check fired on every
/// rule with ANY reducible LHS op and rendered the offending term with
/// Rust's `{:?}` Debug formatter, generating false-positive WF warnings
/// (e.g. on every CRxor/CH07/LAK06 rule). The fix keeps the check
/// FAITHFUL to HS's narrower trigger: skip when no `*` is in RHS and no
/// unbound is introduced. The full abstraction-based (b) check is not
/// yet implemented; for now we conservatively skip when RHS has no `*`
/// (which matches HS on all XOR/DH theories in the corpus).
pub fn mult_restricted_report(thy: &Theory) -> WfReport {
    let mut out = Vec::new();
    for r in theory_rules(thy) {
        // (a) HS `multTerms` over RHS conclusions: gather any `AC Mult`
        //     sub-terms. Skip if RHS has no multiplication.
        let rhs_has_mult = r.conclusions.iter()
            .flat_map(|f| f.args.iter())
            .any(term_has_mult_subterm);
        if !rhs_has_mult { continue; }
        // (b) is approximated by `rhs_has_mult`; the abstraction-based
        // unbound-var check is not yet ported. When the unbound case
        // comes up in the corpus we'll thread the rule-abstraction
        // path through here.
        out.push(WfError::new("Multiplication restriction of rules",
            format!("rule `{}' has multiplication in its RHS",
                r.name)));
    }
    out
}

/// True if `t` has any `AC Mult` (`*`) sub-term (mirrors HS `multTerms
/// t = case viewTerm t of FApp (AC Mult) _ -> [t]; FApp _ ts ->
/// concatMap multTerms ts; _ -> []`).
fn term_has_mult_subterm(t: &Term) -> bool {
    match t {
        Term::BinOp(BinOp::Mult, _, _) => true,
        Term::App(_, args) | Term::Pair(args) => args.iter().any(term_has_mult_subterm),
        Term::AlgApp(_, a, b) => term_has_mult_subterm(a) || term_has_mult_subterm(b),
        Term::Diff(a, b) => term_has_mult_subterm(a) || term_has_mult_subterm(b),
        Term::BinOp(_, a, b) => term_has_mult_subterm(a) || term_has_mult_subterm(b),
        Term::PatMatch(inner) => term_has_mult_subterm(inner),
        _ => false,
    }
}

// =============================================================================
// Lemma annotations — reuse on exists-trace
// =============================================================================

pub fn lemma_attribute_report(thy: &Theory) -> WfReport {
    // HS `lemmaAttributeReport` (Wellformedness.hs:924-932): each
    // exists-trace lemma tagged `reuse` yields a body line
    //   `Lemma `<name>': cannot reuse 'exists-trace' lemmas`
    // all under the single topic `Lemma annotations`.  HS's
    // `prettyWfErrorReport` (Wellformedness.hs:118-125) renders a topic
    // group as `underlineTopic topic $-$ nest 2 (vcat (intersperse "" bodies))`
    // — i.e. ONE underlined header, then the bodies `nest 2`'d and
    // blank-line-separated.  Emit a single `WfError` carrying that whole
    // block so the header appears exactly once even with several lemmas.
    let topic = "Lemma annotations";
    let bodies: Vec<String> = theory_lemmas(thy)
        .into_iter()
        .filter(|l| matches!(l.trace_quantifier, TraceQuantifier::ExistsTrace)
            && l.attributes.iter().any(|a| matches!(a, LemmaAttr::Reuse)))
        .map(|l| format!("  Lemma `{}': cannot reuse 'exists-trace' lemmas", l.name))
        .collect();
    if bodies.is_empty() {
        return Vec::new();
    }
    // `underline_topic` already ends with a newline after the `===` rule;
    // the extra `\n` is HS's `$-$` blank line before the (nest-2) bodies.
    // Bodies are joined by a blank line that is ITSELF `nest 2`'d — HS
    // `nest 2 (vcat (intersperse (text "") bodies))` indents the empty
    // separator line to two spaces, so the join separator is `\n  \n`,
    // not `\n\n`.  (NB: the corpus has at most one reuse-exists lemma per
    // file, so this multi-body path is exercised only synthetically; the
    // per-lemma error COUNT in the `N wellformedness check failed` summary
    // still collapses to one here — matching that would require the wider
    // `format_wf_block` refactor that renders topic headers from raw
    // body-only entries.)
    let mut msg = underline_topic(topic);
    msg.push('\n');
    msg.push_str(&bodies.join("\n  \n"));
    vec![WfError::new(topic, msg)]
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
///
/// HS site: `Wellformedness.hs:1222-1232` — `checkEquationsSubtermConvergence`.
/// Emits ONE WfError with the full formatted block:
///   `underlineTopic "Subterm Convergence Warning" $-$ introText $-$
///    vcat (map prettyCtxtStRule nonSubtermEquations) $-$ manualRef`
/// where `prettyCtxtStRule` uses `sep [nest 2 lhsDoc, "=" <-> rhsDoc]`.
pub fn subterm_convergence_report(thy: &Theory) -> WfReport {
    // Collect all non-subterm-convergent equations across all `equations` items.
    let mut non_conv: Vec<(&Term, &Term)> = Vec::new();
    for it in &thy.items {
        let (eqs, convergent) = match it {
            TheoryItem::Equations { eqs, convergent } => (eqs, *convergent),
            _ => continue,
        };
        if convergent { continue; }
        for eq in eqs {
            if !is_subterm_convergent(&eq.lhs, &eq.rhs) {
                non_conv.push((&eq.lhs, &eq.rhs));
            }
        }
    }
    if non_conv.is_empty() { return Vec::new(); }

    // HS `prettyCtxtStRule r = sep [nest 2 (prettyLNTerm lhs), "=" <-> prettyLNTerm rhs]`
    // For equations that fit on one line, `sep` renders inline:
    // `  {lhs} = {rhs}` (two spaces from the outer nest-2 context inside `vcat`).
    // HS's outer `$-$` / `vcat` adds no extra indent — each rule renders
    // with its own `nest 2` inside the sep.  Result: `    {lhs} = {rhs}`
    // (4 spaces: 2 from `nest 2` on prettyLNTerm, but actually the outer
    // context in `doc` has no extra nest, so `nest 2 (prettyLNTerm lhs)`
    // → 2 spaces before lhs).  Observed HS output: 4 leading spaces.
    // Reconstruction: `sep [nest 2 lhs, "=" <-> rhs]` inline →
    // `  {lhs} = {rhs}` (2 spaces).  Then the wrapping `doc` context adds
    // another 2 via `nest 2 $ vcat ...`?  Let's pin to the observed 4.
    let mut eq_lines = String::new();
    for (lhs, rhs) in &non_conv {
        let lhs_s = pp_term_for_wf(lhs);
        let rhs_s = pp_term_for_wf(rhs);
        // `sep [nest 2 lhsDoc, "=" <-> rhsDoc]` inline → `  lhs = rhs`
        // HS output observed: `    unblind(...) = sign(...)` (4-space indent).
        // The top-level `$-$ vcat (map pretty ...) $-$` gives no extra indent,
        // but prettyWfErrorReport wraps the body in `nest 2`:
        // `(nest 2 . vcat . map snd) errs` (Wellformedness.hs:122).
        // So the per-rule `nest 2 lhs` + outer `nest 2` = 4 spaces total.
        eq_lines.push_str("    ");
        eq_lines.push_str(&lhs_s);
        eq_lines.push_str(" = ");
        eq_lines.push_str(&rhs_s);
        eq_lines.push('\n');
    }

    // Assemble the full message block (topic header + intro + equations + footer).
    // HS: `underlineTopic "Subterm Convergence Warning"` produces
    //   `"Subterm Convergence Warning\n===========================\n"`.
    // Then `$-$` (blank-line separator) adds a blank line before the intro.
    // Then `vcat` adds the equations, then `$-$` + manual reference text.
    let mut msg = String::new();
    msg.push_str(&underline_topic("Subterm Convergence Warning"));
    msg.push('\n'); // blank line before intro (HS `$-$`)
    // The intro text — HS: `text "User-defined equations must be convergent..."`.
    // Wrapped at 2-space indent (outer nest-2 in prettyWfErrorReport).
    msg.push_str("  User-defined equations must be convergent and have the finite variant property. The following equations are not subterm convergent. If you are sure that the set of equations is nevertheless convergent and has the finite variant property, you can ignore this warning and continue \n");
    msg.push('\n'); // blank line after intro (HS `$-$` before vcat)
    msg.push_str(&eq_lines);
    // HS: `$-$ text " \n For more information..."` — note the leading space.
    msg.push_str("   \n For more information, please refer to the manual : https://tamarin-prover.com/manual/master/book/010_modeling-issues.html ");

    vec![WfError::new("Subterm Convergence Warning", msg)]
}

/// Minimal pretty-printer for parser-AST `Term` for the WF subterm-convergence
/// warning.  Mirrors HS `prettyLNTerm` output for the restricted case of
/// equations: function applications, variables, public/fresh literals.
/// (No HughesPJ wrapping needed — equations are expected to fit on one line.)
fn pp_term_for_wf(t: &Term) -> String {
    match t {
        Term::Var(v) => v.name.clone(),
        Term::PubLit(s) => format!("'{}'", s),
        Term::FreshLit(s) => format!("~'{}'", s),
        Term::NatLit(s) => format!("%'{}'", s),
        Term::Number(n) => n.to_string(),
        Term::NumberOne => "one".to_string(),
        Term::NatOne => "%1".to_string(),
        Term::DhNeutral => "1:msg".to_string(),
        Term::App(name, args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let args_s: Vec<String> = args.iter().map(pp_term_for_wf).collect();
                format!("{}({})", name, args_s.join(", "))
            }
        }
        Term::AlgApp(name, a, b) => {
            format!("{}({}, {})", name, pp_term_for_wf(a), pp_term_for_wf(b))
        }
        Term::Pair(items) => {
            let parts: Vec<String> = items.iter().map(pp_term_for_wf).collect();
            format!("<{}>", parts.join(", "))
        }
        Term::Diff(a, b) => {
            format!("diff({}, {})", pp_term_for_wf(a), pp_term_for_wf(b))
        }
        Term::BinOp(op, a, b) => {
            use crate::ast::BinOp;
            let sym = match op {
                BinOp::Exp => "^",
                BinOp::Mult => "*",
                BinOp::Union => "++",
                BinOp::Xor => "\u{2295}",
                BinOp::NatPlus => "%+",
            };
            format!("({}{}{})", pp_term_for_wf(a), sym, pp_term_for_wf(b))
        }
        Term::PatMatch(inner) => pp_term_for_wf(inner),
    }
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
    // NOTE: the actual HS `checkTerms` ("Formula terms" topic) is ported
    // faithfully in `tamarin_theory::check_terms::check_terms_wf`, which
    // needs the elaborated `MaudeSig` (for reducible/irreducible funsym
    // classification) and so runs post-elaboration in `run.rs`.  Here we
    // only keep the parser-level "Variable with mismatching sorts or
    // capitalization" sub-check (a different topic, no signature needed).
    variable_sort_clashes(thy)
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
