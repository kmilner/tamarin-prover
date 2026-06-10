//! Port of `Theory.Constraint.System.Graph.Abbreviation`.
//!
//! Generates a per-graph map from "complex" `LNTerm`s to short
//! variable-style aliases (`SE1`, `PA2`, ...) so the rendered DOT
//! and JSON keep long compound terms compact.  A separate legend
//! table can be emitted alongside the graph to list `t_1 = ...`
//! expansions.
//!
//! See `lib/theory/src/Theory/Constraint/System/Graph/Abbreviation.hs`.

use std::collections::BTreeMap;

use tamarin_term::function_symbols::{CSym, FunSym};
use tamarin_term::lterm::{LNTerm, LSort, LVar};
use tamarin_term::pretty::pretty_lnterm;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

use tamarin_theory::fact::LNFact;
use tamarin_theory::rule::RuleACInst;

use super::repr::{GraphRepr, NodeType};

// ---------------------------------------------------------------------
// Options
// ---------------------------------------------------------------------

/// Mirror of `AbbreviationOptions` (Abbreviation.hs:56-62).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AbbreviationOptions {
    /// Soft cap on the number of abbreviations to generate, unless
    /// a term scores above `always_abbrev_weight`.
    pub abbrevs_soft_limit: usize,
    pub always_abbrev_weight: i64,
    pub first_index: u32,
    pub prefix_length: usize,
}

impl Default for AbbreviationOptions {
    fn default() -> Self {
        AbbreviationOptions {
            abbrevs_soft_limit: 10,
            always_abbrev_weight: 30,
            first_index: 1,
            prefix_length: 2,
        }
    }
}

// ---------------------------------------------------------------------
// Abbreviation map
// ---------------------------------------------------------------------

/// Map from original term -> (abbrev name, expansion with subterms
/// substituted by their own abbreviations).
pub type Abbreviations = BTreeMap<LNTerm, (LNTerm, LNTerm)>;

/// Lookup the abbreviation for a single term.  Mirror of `lookupAbbreviation`.
pub fn lookup_abbreviation<'a>(
    abbrevs: &'a Abbreviations,
    t: &LNTerm,
) -> Option<&'a LNTerm> {
    abbrevs.get(t).map(|(a, _)| a)
}

// ---------------------------------------------------------------------
// Substitution helpers
// ---------------------------------------------------------------------

/// Apply abbreviation substitution top-down: at each term, first
/// replace the whole thing if it's in the map, else recurse into args.
///
/// Mirror of `applyAbbreviationsTerm`.
pub fn apply_abbreviations_term(
    lookup: &dyn Fn(&LNTerm) -> Option<LNTerm>,
    t: &LNTerm,
) -> LNTerm {
    if let Some(abbrev) = lookup(t) {
        return abbrev;
    }
    match t {
        Term::Lit(_) => t.clone(),
        Term::App(s, args) => {
            let new_args: Vec<LNTerm> = args.iter()
                .map(|a| apply_abbreviations_term(lookup, a))
                .collect();
            Term::App(s.clone(), new_args.into())
        }
    }
}

/// Apply abbreviation substitution to all terms of a fact.
/// Mirror of `applyAbbreviationsFact`.
pub fn apply_abbreviations_fact(
    lookup: &dyn Fn(&LNTerm) -> Option<LNTerm>,
    fa: &LNFact,
) -> LNFact {
    let mut new_fa = fa.clone();
    new_fa.terms = fa.terms.iter()
        .map(|t| apply_abbreviations_term(lookup, t))
        .collect();
    new_fa
}

// ---------------------------------------------------------------------
// Term-prefix extraction
// ---------------------------------------------------------------------

/// `getTermPrefix` (Abbreviation.hs:106-115).
fn get_term_prefix(opts: &AbbreviationOptions, t: &LNTerm) -> String {
    let raw = match t {
        Term::Lit(Lit::Var(v)) => v.name.clone(),
        Term::Lit(Lit::Con(n)) => n.id.0.clone(),
        Term::App(FunSym::NoEq(sym), _) => {
            String::from_utf8_lossy(&sym.name).into_owned()
        }
        Term::App(FunSym::C(CSym::EMap), _) => "EMP".to_string(),
        Term::App(FunSym::List, _) => "LST".to_string(),
        Term::App(FunSym::Ac(op), _) => format!("{:?}", op),
    };
    let mut out: String = raw.chars().filter(|c| c.is_ascii_alphabetic()).collect();
    out.truncate(opts.prefix_length);
    out.to_ascii_uppercase()
}

// ---------------------------------------------------------------------
// Abbreviation generation
// ---------------------------------------------------------------------

type PrefixMap = BTreeMap<String, u32>;

/// Generate one fresh abbreviation name for a candidate term.
/// Mirror of `abbreviateTerm` (Abbreviation.hs:122-149).
///
/// Returns the new prefix-index map and the abbreviation as an `LNTerm`
/// (a Msg-sort variable).
fn abbreviate_term(
    opts: &AbbreviationOptions,
    all_names: &[String],
    mut prefix_map: PrefixMap,
    t: &LNTerm,
) -> (PrefixMap, LNTerm) {
    let prefix = get_term_prefix(opts, t);
    let mut idx = prefix_map.get(&prefix).copied().unwrap_or(opts.first_index);
    loop {
        let candidate = format!("{}{}", prefix, idx);
        // Case-insensitive comparison against the global name set, since
        // the Haskell side does `T.toUpper` on `allNames`.
        if !all_names.iter().any(|n| n.eq_ignore_ascii_case(&candidate)) {
            prefix_map.insert(prefix, idx + 1);
            let v = LVar::new(candidate, LSort::Msg, 0);
            return (prefix_map, Term::Lit(Lit::Var(v)));
        }
        idx += 1;
    }
}

/// Walk a `GraphRepr` collecting all rendered string fragments and pick
/// out alphanumeric runs (case-insensitive).  Mirror of `allNames`.
fn collect_all_names(repr: &GraphRepr) -> Vec<String> {
    let mut buf = String::new();
    for n in &repr.nodes { dump_node(&mut buf, n); }
    for c in &repr.clusters {
        buf.push_str(&c.name); buf.push('\n');
        for n in &c.nodes { dump_node(&mut buf, n); }
    }
    let mut out: Vec<String> = Vec::new();
    let mut cur = String::new();
    for ch in buf.chars() {
        if ch.is_ascii_alphanumeric() {
            cur.push(ch.to_ascii_uppercase());
        } else if !cur.is_empty() {
            out.push(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() { out.push(cur); }
    out.sort();
    out.dedup();
    out
}

fn dump_node(buf: &mut String, n: &super::repr::GNode) {
    use std::fmt::Write as _;
    let _ = write!(buf, "{} ", n.id);
    match &n.ty {
        NodeType::System(ru) => dump_rule(buf, ru),
        NodeType::UnsolvedAction(fs) => {
            for f in fs { dump_fact(buf, f); }
        }
        _ => {}
    }
}

fn dump_rule(buf: &mut String, ru: &RuleACInst) {
    for f in &ru.premises { dump_fact(buf, f); }
    for f in &ru.actions  { dump_fact(buf, f); }
    for f in &ru.conclusions { dump_fact(buf, f); }
}

fn dump_fact(buf: &mut String, fa: &LNFact) {
    use std::fmt::Write as _;
    let _ = write!(buf, "{}", tamarin_theory::fact::fact_tag_name(&fa.tag));
    for t in &fa.terms {
        let _ = write!(buf, "{} ", pretty_lnterm(t));
    }
}

// ---------------------------------------------------------------------
// Term collection & subterm helpers
// ---------------------------------------------------------------------

/// Walk a `GraphRepr` collecting every (sub)term that's a candidate for
/// abbreviation.  We exclude top-level pair-trees (Haskell `isPair`)
/// because pair siblings get rendered as `<a,b,c>` already.
fn collect_all_terms(repr: &GraphRepr) -> Vec<LNTerm> {
    let mut out: Vec<LNTerm> = Vec::new();
    for n in &repr.nodes {
        node_terms(n, &mut out);
    }
    for c in &repr.clusters {
        for n in &c.nodes {
            node_terms(n, &mut out);
        }
    }
    out
}

fn node_terms(n: &super::repr::GNode, out: &mut Vec<LNTerm>) {
    match &n.ty {
        NodeType::System(ru) => {
            for f in ru.premises.iter()
                    .chain(ru.actions.iter())
                    .chain(ru.conclusions.iter()) {
                fact_terms(f, out);
            }
        }
        NodeType::UnsolvedAction(fs) => {
            for f in fs { fact_terms(f, out); }
        }
        _ => {}
    }
}

fn fact_terms(fa: &LNFact, out: &mut Vec<LNTerm>) {
    for t in &fa.terms {
        sub_terms_no_pair(t, out);
    }
}

fn sub_terms_no_pair(t: &LNTerm, out: &mut Vec<LNTerm>) {
    if !is_pair(t) {
        out.push(t.clone());
    }
    if let Term::App(_, args) = t {
        for a in args.iter() {
            sub_terms_no_pair(a, out);
        }
    }
}

fn is_pair(t: &LNTerm) -> bool {
    if let Term::App(FunSym::NoEq(sym), args) = t {
        sym.name == b"pair" && args.len() == 2
    } else { false }
}

// ---------------------------------------------------------------------
// Weight
// ---------------------------------------------------------------------

/// Mirror of `judgeTerm` (Abbreviation.hs:79-101).
fn judge_term(
    abbrevs: &BTreeMap<LNTerm, LNTerm>,
    t: &LNTerm,
    occs: i64,
    legend_occs: &[i64],
) -> i64 {
    let lookup = |k: &LNTerm| abbrevs.get(k).cloned();
    let replaced = apply_abbreviations_term(&lookup, t);
    let term_weight = pretty_lnterm(&replaced).chars().count() as i64;
    if term_weight < 10 { return -1; }
    let relative = if occs == 1 && legend_occs == [1] { 0 } else { occs };
    if relative <= 1 { return -1; }
    relative * term_weight
}

// ---------------------------------------------------------------------
// Subterm-counting (used to decrement occurrences after chosing a term)
// ---------------------------------------------------------------------

/// Number of times `sub` appears as a proper subterm of `t`.
fn count_proper_subterms(t: &LNTerm, sub: &LNTerm) -> i64 {
    if t == sub {
        // Don't count the term itself.
        return count_subterms_inner(t, sub) - 1;
    }
    count_subterms_inner(t, sub)
}

fn count_subterms_inner(t: &LNTerm, sub: &LNTerm) -> i64 {
    let mut total = 0i64;
    if t == sub { total += 1; }
    if let Term::App(_, args) = t {
        for a in args.iter() {
            total += count_subterms_inner(a, sub);
        }
    }
    total
}

// ---------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------

/// Mirror of `computeAbbreviations` (Abbreviation.hs:166-254).
pub fn compute_abbreviations(
    repr: &GraphRepr,
    opts: &AbbreviationOptions,
) -> Abbreviations {
    // Step 1: collect all terms and their occurrence counts.
    let terms = collect_all_terms(repr);
    let mut term_occs: BTreeMap<LNTerm, (i64, Vec<i64>)> = BTreeMap::new();
    for t in &terms {
        let entry = term_occs.entry(t.clone()).or_insert((0, Vec::new()));
        entry.0 += 1;
    }
    let all_names = collect_all_names(repr);
    let mut abbrevs: BTreeMap<LNTerm, LNTerm> = BTreeMap::new();
    let mut prefix_map: PrefixMap = BTreeMap::new();
    // Iteratively pick the best candidate.
    loop {
        // Compute weights for each remaining term.
        let weighted: Vec<(LNTerm, i64)> = term_occs.iter()
            .map(|(t, (occs, legend_occs))|
                (t.clone(), judge_term(&abbrevs, t, *occs, legend_occs))).collect();
        let mut positives: Vec<(LNTerm, i64)> = weighted.into_iter()
            .filter(|(_, w)| *w > 0).collect();
        // Sort by descending weight, then by pretty string for determinism.
        positives.sort_by(|a, b| {
            b.1.cmp(&a.1).then_with(|| pretty_lnterm(&a.0).cmp(&pretty_lnterm(&b.0)))
        });
        let (candidate, weight) = match positives.into_iter().next() {
            Some(x) => x,
            None => break,
        };
        if weight < opts.always_abbrev_weight && abbrevs.len() >= opts.abbrevs_soft_limit {
            break;
        }
        let (new_pmap, abbrev_name) = abbreviate_term(opts, &all_names, prefix_map, &candidate);
        prefix_map = new_pmap;
        // Decrement subterm counts in legend_occs for every other term.
        let mut new_term_occs: BTreeMap<LNTerm, (i64, Vec<i64>)> = BTreeMap::new();
        for (term, (occs, legend_occs)) in term_occs {
            if term == candidate { continue; }
            let sub_count = count_proper_subterms(&term, &candidate);
            let mut new_legend_occs = legend_occs;
            new_legend_occs.push(sub_count);
            new_term_occs.insert(term, (occs, new_legend_occs));
        }
        term_occs = new_term_occs;
        abbrevs.insert(candidate, abbrev_name);
    }
    // Step 2: make abbreviations recursive --
    // each entry's expansion is the original term with all OTHER
    // abbreviation entries substituted (so the legend can read like
    // `SE1 = senc(SE2, k)` rather than `SE1 = senc(senc(...), k)`).
    let mut out: Abbreviations = BTreeMap::new();
    for (orig, name) in &abbrevs {
        let others_only = |k: &LNTerm| -> Option<LNTerm> {
            if k == orig { None } else { abbrevs.get(k).cloned() }
        };
        let expansion = apply_proper_subterms(&others_only, orig);
        out.insert(orig.clone(), (name.clone(), expansion));
    }
    out
}

/// Apply replacement to PROPER subterms only -- not to the top-level
/// term itself.  Mirror of `replaceProperSubterm`.
fn apply_proper_subterms(
    lookup: &dyn Fn(&LNTerm) -> Option<LNTerm>,
    t: &LNTerm,
) -> LNTerm {
    match t {
        Term::Lit(_) => t.clone(),
        Term::App(s, args) => {
            let new_args: Vec<LNTerm> = args.iter()
                .map(|a| apply_abbreviations_term(lookup, a))
                .collect();
            Term::App(s.clone(), new_args.into())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::function_symbols::{NoEqSym, Privacy, Constructability};
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::term::{f_app_no_eq, lit};

    fn var(name: &str, sort: LSort) -> LNTerm {
        lit(Lit::Var(LVar::new(name, sort, 0)))
    }

    fn senc_sym() -> NoEqSym {
        NoEqSym::new(b"senc".to_vec(), 2, Privacy::Public, Constructability::Constructor)
    }

    #[test]
    fn apply_abbreviations_replaces_top_level() {
        let t = f_app_no_eq(senc_sym(), vec![var("a", LSort::Msg), var("b", LSort::Msg)]);
        let abbrev = var("SE1", LSort::Msg);
        let map = |q: &LNTerm| if q == &t { Some(abbrev.clone()) } else { None };
        assert_eq!(apply_abbreviations_term(&map as &dyn Fn(&LNTerm) -> Option<LNTerm>, &t), abbrev);
    }

    #[test]
    fn apply_abbreviations_replaces_subterm() {
        let inner = f_app_no_eq(senc_sym(), vec![var("a", LSort::Msg), var("b", LSort::Msg)]);
        let outer = f_app_no_eq(senc_sym(), vec![inner.clone(), var("k", LSort::Msg)]);
        let abbrev = var("SE1", LSort::Msg);
        let map = |q: &LNTerm| if q == &inner { Some(abbrev.clone()) } else { None };
        let out = apply_abbreviations_term(&map as &dyn Fn(&LNTerm) -> Option<LNTerm>, &outer);
        // Top-level senc stays; inner senc replaced.
        if let Term::App(_, args) = &out {
            assert_eq!(&args[0], &abbrev);
        } else { panic!("expected App"); }
    }

    #[test]
    fn lookup_returns_first_field() {
        let mut abbrevs = Abbreviations::new();
        let t = f_app_no_eq(senc_sym(),
            vec![var("a", LSort::Msg), var("b", LSort::Msg)]);
        let name = var("SE1", LSort::Msg);
        abbrevs.insert(t.clone(), (name.clone(), t.clone()));
        assert_eq!(lookup_abbreviation(&abbrevs, &t), Some(&name));
    }
}
