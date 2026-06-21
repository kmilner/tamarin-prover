//! Port of `Theory.Constraint.System.Graph.Abbreviation`.
//!
//! Generates a per-graph map from "complex" `LNTerm`s to short
//! variable-style aliases (`SE1`, `PA2`, ...) so the rendered DOT
//! and JSON keep long compound terms compact.  A separate legend
//! table can be emitted alongside the graph to list `t_1 = ...`
//! expansions.
//!
//! See `lib/theory/src/Theory/Constraint/System/Graph/Abbreviation.hs`.

use std::collections::{BTreeMap, BTreeSet};

use tamarin_term::function_symbols::{CSym, FunSym};
use tamarin_term::lterm::{LNTerm, LSort, LVar};
use tamarin_term::pretty::pretty_lnterm;
use tamarin_term::term::Term;
use tamarin_term::vterm::Lit;

use tamarin_theory::fact::LNFact;
use tamarin_theory::rule::{
    IntrRuleACInfo, ProtoRuleACInstInfo, ProtoRuleName, RuleACInst, RuleInfo,
};

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
    all_names: &BTreeSet<String>,
    mut prefix_map: PrefixMap,
    t: &LNTerm,
) -> (PrefixMap, LNTerm) {
    let prefix = get_term_prefix(opts, t);
    let mut idx = prefix_map.get(&prefix).copied().unwrap_or(opts.first_index);
    loop {
        let candidate = format!("{}{}", prefix, idx);
        // `candidate` is already ASCII-uppercase (`prefix` is uppercased in
        // `get_term_prefix`, `idx` is digits) and `all_names` is the
        // uppercased global name set, mirroring the Haskell `T.toUpper` on
        // `allNames`, so an exact set lookup matches `nameCandidate `elem`
        // allNames`.
        if !all_names.contains(&candidate) {
            prefix_map.insert(prefix, idx + 1);
            let v = LVar::new(candidate, LSort::Msg, 0);
            return (prefix_map, Term::Lit(Lit::Var(v)));
        }
        idx += 1;
    }
}

/// Walk a `GraphRepr` collecting rendered string fragments and pick out
/// alphanumeric runs (uppercased, sorted, deduped).  Used to avoid
/// generating an abbreviation name that aliases an existing identifier.
///
/// Mirrors Haskell `allNames` (Abbreviation.hs:220-225): `sort . nub . map
/// toUpper . T.split (not . isAlphaNum) $ show repr`.  `show repr` is the
/// DERIVED Show of the whole `GraphRepr`, which for a `SystemNode` renders
/// the rule's `_rInfo` — exposing the RAW `StandRule "<name>"` string, the
/// `role = Just "<role>"` string, and the intruder `ConstrRule`/`DestrRule
/// "<name>"` byte string (verified against derived Show, e.g. a rule named
/// `Se1` contributes the token `SE1`, a role `I` contributes `I`).  We
/// therefore feed those user-controlled name/role tokens into `buf`
/// (`dump_rule`) so an abbreviation never aliases one.  The only tokens we
/// still omit are long constructor/field words (`ProtoInfo`,
/// `ProtoRuleACInstInfo`, `RuleAttributes`, …) and small ints (`PremIdx`
/// indices, `DestrRule` flags): none of those can match a generated name's
/// `<<=prefix_length alpha letters><digits>` shape, so omitting them cannot
/// change which abbreviation is chosen.
fn collect_all_names(repr: &GraphRepr) -> BTreeSet<String> {
    let mut buf = String::new();
    for n in &repr.nodes { dump_node(&mut buf, n); }
    for c in &repr.clusters {
        buf.push_str(&c.name); buf.push('\n');
        for n in &c.nodes { dump_node(&mut buf, n); }
    }
    let mut out: BTreeSet<String> = BTreeSet::new();
    let mut cur = String::new();
    for ch in buf.chars() {
        if ch.is_ascii_alphanumeric() {
            cur.push(ch.to_ascii_uppercase());
        } else if !cur.is_empty() {
            out.insert(std::mem::take(&mut cur));
        }
    }
    if !cur.is_empty() { out.insert(cur); }
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
    // `show repr` renders the rule's `_rInfo`, exposing the RAW rule name,
    // role, and intruder-rule name as alphanumeric tokens.  Feed exactly
    // those (and only those) user-controlled tokens — the derived Show's
    // long constructor/field words are harmless (see `collect_all_names`).
    dump_rule_info(buf, &ru.info);
    for f in &ru.premises { dump_fact(buf, f); }
    for f in &ru.actions  { dump_fact(buf, f); }
    for f in &ru.conclusions { dump_fact(buf, f); }
}

/// Emit the user-controlled name/role tokens that derived `Show` of a
/// rule's `_rInfo` exposes (Rule.hs:206-214, 397-400, 517-519): the raw
/// `StandRule "<name>"` string, the `role = Just "<role>"` string, and the
/// intruder `ConstrRule`/`DestrRule "<name>"` byte string.
fn dump_rule_info(
    buf: &mut String,
    info: &RuleInfo<ProtoRuleACInstInfo, IntrRuleACInfo>,
) {
    use std::fmt::Write as _;
    match info {
        RuleInfo::Proto(p) => {
            // `StandRule "<s>"`: the RAW stored string (derived Show emits it
            // verbatim — do NOT route through prettyProtoRuleName).  `FreshRule`
            // contributes the long, harmless token `FRESHRULE`.
            if let ProtoRuleName::Stand(s) = &p.name {
                let _ = write!(buf, "{} ", s);
            }
            // `role = Just "<role>"`.
            if let Some(role) = &p.attributes.role {
                let _ = write!(buf, "{} ", role);
            }
        }
        RuleInfo::Intr(i) => {
            // `ConstrRule "<name>"` / `DestrRule "<name>" _ _ _`: the byte-string
            // name.  Remaining intruder variants carry no user string.
            let name: Option<&[u8]> = match i {
                IntrRuleACInfo::ConstrRule(n) => Some(n),
                IntrRuleACInfo::DestrRule(n, _, _, _) => Some(n),
                _ => None,
            };
            if let Some(n) = name {
                let _ = write!(buf, "{} ", String::from_utf8_lossy(n));
            }
        }
    }
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

/// Walk a `GraphRepr` collecting candidate terms for abbreviation.
/// For each fact term we keep only the term itself and its IMMEDIATE
/// arguments (one level deep, mirroring `getSubTerms t = t : ts`),
/// excluding any that are pairs (Haskell `isPair`) because pair
/// siblings get rendered as `<a,b,c>` already.
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
    // Mirror `getFactTerms fact = filter (not . isPair) $ concatMap getSubTerms
    // $ factTerms fact`, where `getSubTerms t = t : ts` collects the term and
    // its IMMEDIATE arguments only (one level deep, not recursive).
    for t in &fa.terms {
        sub_terms_no_pair(t, out);
    }
}

fn sub_terms_no_pair(t: &LNTerm, out: &mut Vec<LNTerm>) {
    // `getSubTerms`: the term itself plus its immediate arguments.
    if !is_pair(t) {
        out.push(t.clone());
    }
    if let Term::App(_, args) = t {
        for a in args.iter() {
            if !is_pair(a) {
                out.push(a.clone());
            }
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

/// Number of times `needle` appears as a PROPER subterm of `haystack`.
/// Mirror of `countProperSubterms t (FApp _ ts) = sum $ map (countSubterms t) ts`
/// (Raw.hs:255-257).
fn count_proper_subterms(needle: &LNTerm, haystack: &LNTerm) -> i64 {
    match haystack {
        Term::App(_, args) => args.iter().map(|a| count_subterms(needle, a)).sum(),
        _ => 0,
    }
}

/// Mirror of `countSubterms t1 t2 = if t1 == t2 then 1 else countProperSubterms t1 t2`
/// (Raw.hs:252-253).  Note: when `needle == haystack` it returns 1 and does NOT
/// descend further (matches `if ... then 1 else ...`).
fn count_subterms(needle: &LNTerm, haystack: &LNTerm) -> i64 {
    if needle == haystack {
        1
    } else {
        count_proper_subterms(needle, haystack)
    }
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
        // Haskell `filterCandidateTerm`: `sortOn (Down . snd)` over the
        // `M.toList`-ordered (LNTerm `Ord`) weighted terms.  `sortOn` is
        // stable, so equal-weight ties fall back to ascending LNTerm `Ord`
        // (the BTreeMap iteration order).  `slice::sort_by` is likewise
        // stable, so sorting purely on descending weight preserves that
        // tie-break — do NOT add a pretty-string secondary key.
        positives.sort_by_key(|x| std::cmp::Reverse(x.1));
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
            // Haskell: `countProperSubterms term candidate` — occurrences of
            // `term` (needle) inside `candidate` (haystack).
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

    // A rule named `Se1` tokenises (via derived `show repr`) to `SE1`, exactly
    // the shape of a generated `senc` abbreviation.  Haskell's `allNames`
    // therefore contains `SE1`, so `abbreviateTerm` skips it and emits `SE2`.
    // This pins that `collect_all_names` feeds the raw rule name into the name
    // set, so the abbreviator skips `SE1` and emits `SE2` (matching HS).
    #[test]
    fn rule_name_blocks_aliasing_abbreviation() {
        use tamarin_theory::fact::{Fact, FactTag, Multiplicity};
        use tamarin_theory::rule::{ProtoRuleACInstInfo, RuleAttributes, Rule};
        use super::super::repr::{GNode, NodeType};

        // A senc(...) term long enough to clear the weight>=10 threshold and
        // appearing in two facts so its occurrence count exceeds 1.
        let enc = f_app_no_eq(
            senc_sym(),
            vec![var("plaintext", LSort::Msg), var("key", LSort::Msg)],
        );
        let mk_fact = |name: &str| {
            Fact::new(
                FactTag::Proto(Multiplicity::Linear, name.to_string(), 1),
                vec![enc.clone()],
            )
        };

        let plain_rule = |rule_name: &str, fact_name: &str| -> RuleACInst {
            Rule::new(
                RuleInfo::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(rule_name.to_string()),
                    attributes: RuleAttributes::default(),
                    loop_breakers: Vec::new(),
                }),
                vec![mk_fact(fact_name)], // premises
                Vec::new(),               // conclusions
                Vec::new(),               // actions
            )
        };

        let mut repr = GraphRepr::new();
        // Rule literally named `Se1` -> contributes token `SE1` to allNames.
        repr.nodes.push(GNode {
            id: LVar::new("i", LSort::Node, 1),
            ty: NodeType::System(plain_rule("Se1", "FactA")),
        });
        // Second node so the senc term occurs twice (occs > 1).
        repr.nodes.push(GNode {
            id: LVar::new("i", LSort::Node, 2),
            ty: NodeType::System(plain_rule("Other", "FactB")),
        });

        let abbrevs = compute_abbreviations(&repr, &AbbreviationOptions::default());
        let name = lookup_abbreviation(&abbrevs, &enc)
            .expect("senc term should be abbreviated");
        // HS skips SE1 (taken by the rule name) and uses SE2.
        assert_eq!(name, &var("SE2", LSort::Msg));
    }
}
