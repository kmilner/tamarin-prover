//! Port of `Theory.Model.Fact` from `lib/theory/src/Theory/Model/Fact.hs`.
//!
//! Multiset-rewriting facts. This port covers the data type plus the
//! tagging / construction / query API. The Maude-backed `unifyLNFactEqs`
//! and `unifiableLNFacts` entry points live in `rule.rs` and call the
//! live Maude unification bridge (`maude.unify_at`).

use std::collections::BTreeSet;

use tamarin_term::lterm::{HasFrees, LNTerm, LVar};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Multiplicity {
    Persistent,
    Linear,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactTag {
    /// A protocol fact: `ProtoFact(multiplicity, name, arity)`.
    /// Interned `&'static str` (see `tamarin_term::intern`): pointer-copy
    /// clone, no alloc/atomic, shared.
    Proto(Multiplicity, &'static str, usize),
    Fresh,
    Out,
    In,
    Ku,
    Kd,
    Ded,
    /// Internal: only for converting terms to facts during analysis.
    Term,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactAnnotation {
    SolveFirst,
    SolveLast,
    NoSources,
}

/// A multiset-rewriting fact carrying a tag, optional annotations, and
/// term arguments.
#[derive(Debug, Clone)]
pub struct Fact<T> {
    pub tag: FactTag,
    pub annotations: BTreeSet<FactAnnotation>,
    pub terms: Vec<T>,
}

// Equality and ordering ignore annotations, matching the Haskell semantics.
impl<T: PartialEq> PartialEq for Fact<T> {
    fn eq(&self, other: &Self) -> bool {
        self.tag == other.tag && self.terms == other.terms
    }
}
impl<T: Eq> Eq for Fact<T> {}
impl<T: PartialOrd> PartialOrd for Fact<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.tag.partial_cmp(&other.tag) {
            Some(std::cmp::Ordering::Equal) => self.terms.partial_cmp(&other.terms),
            ord => ord,
        }
    }
}
impl<T: Ord> Ord for Fact<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.tag.cmp(&other.tag).then(self.terms.cmp(&other.terms))
    }
}

impl<T> Fact<T> {
    pub fn new(tag: FactTag, terms: Vec<T>) -> Self {
        Fact { tag, annotations: BTreeSet::new(), terms }
    }
    pub fn with_annotations(mut self, ann: BTreeSet<FactAnnotation>) -> Self {
        self.annotations = ann;
        self
    }
    pub fn annotate(mut self, a: FactAnnotation) -> Self {
        self.annotations.insert(a);
        self
    }
    pub fn arity(&self) -> usize { self.terms.len() }
    pub fn map<U, F: FnMut(T) -> U>(self, f: F) -> Fact<U> {
        Fact {
            tag: self.tag,
            annotations: self.annotations,
            terms: self.terms.into_iter().map(f).collect(),
        }
    }
}

// =============================================================================
// HasFrees instance — visit/map over the fact's term arguments.
// =============================================================================

impl<T: HasFrees> HasFrees for Fact<T> {
    fn for_each_free(&self, f: &mut dyn FnMut(&LVar)) {
        for t in &self.terms { t.for_each_free(f); }
    }
    fn map_free_with(self, f: &mut dyn FnMut(LVar) -> LVar, monotone: bool) -> Self {
        Fact {
            tag: self.tag,
            annotations: self.annotations,
            terms: self.terms.into_iter().map(|t| t.map_free_with(f, monotone)).collect(),
        }
    }
}

// =============================================================================
// Tag queries
// =============================================================================

pub fn fact_tag_name(t: &FactTag) -> String {
    match t {
        FactTag::Proto(_, n, _) => n.to_string(),
        FactTag::Fresh => "Fr".into(),
        FactTag::Out => "Out".into(),
        FactTag::In => "In".into(),
        FactTag::Ku => "KU".into(),
        FactTag::Kd => "KD".into(),
        FactTag::Ded => "Ded".into(),
        FactTag::Term => "Term".into(),
    }
}

/// `showFactTag` (Fact.hs:516-523): `factTagName` prefixed with `!` for
/// persistent facts.
pub fn show_fact_tag(t: &FactTag) -> String {
    let prefix = if fact_tag_multiplicity(t) == Multiplicity::Persistent { "!" } else { "" };
    format!("{}{}", prefix, fact_tag_name(t))
}

pub fn fact_tag_arity(t: &FactTag) -> usize {
    match t {
        FactTag::Proto(_, _, n) => *n,
        FactTag::Fresh | FactTag::Out | FactTag::In => 1,
        FactTag::Ku | FactTag::Kd | FactTag::Ded | FactTag::Term => 1,
    }
}

pub fn fact_tag_multiplicity(t: &FactTag) -> Multiplicity {
    // Mirror Haskell's `factTagMultiplicity` (Fact.hs:353-358):
    //
    //   factTagMultiplicity tag = case tag of
    //       ProtoFact multi _ _ -> multi
    //       KUFact              -> Persistent
    //       KDFact              -> Persistent
    //       _                   -> Linear
    //
    // KU/KD are Persistent because adversary knowledge is inherently
    // reusable.
    match t {
        FactTag::Proto(m, _, _) => *m,
        FactTag::Ku | FactTag::Kd => Multiplicity::Persistent,
        _ => Multiplicity::Linear,
    }
}

// =============================================================================
// Predicates on Fact<T>
// =============================================================================

impl<T> Fact<T> {
    pub fn is_linear(&self) -> bool { fact_tag_multiplicity(&self.tag) == Multiplicity::Linear }
    pub fn is_persistent(&self) -> bool { fact_tag_multiplicity(&self.tag) == Multiplicity::Persistent }
    // Intentionally retained: faithful HS port; no caller yet.
    pub fn is_proto(&self) -> bool { matches!(self.tag, FactTag::Proto(_, _, _)) }
    // Intentionally retained: faithful HS port; no caller yet.
    pub fn is_in_fact(&self) -> bool { self.tag == FactTag::In }
    pub fn is_k_fact(&self) -> bool {
        matches!(self.tag, FactTag::Ku | FactTag::Kd)
    }
    pub fn is_ku(&self) -> bool { self.tag == FactTag::Ku }
    pub fn is_kd(&self) -> bool { self.tag == FactTag::Kd }
    /// Mirrors Haskell `Theory.Model.Fact.isNoSourcesFact`
    /// (Fact.hs:405-406): returns true iff this fact has the
    /// `NoSources` annotation (set via `[no_sources]` on a fact).
    /// Used by `safeGoal` to exclude premise solving during
    /// saturate-time `solveAllSafeGoals`.
    pub fn is_no_sources(&self) -> bool {
        self.annotations.contains(&FactAnnotation::NoSources)
    }
}

/// Mirrors Haskell `Theory.Model.Fact.isKDXorFact` (Fact.hs:241-243):
/// returns true iff this is a KD-tagged fact whose single term is
/// `xor`-headed.  Used by `safeGoal` and `isKDPrem` to exclude
/// Xor-KD goals from saturate-time solving — Xor-KD goals are
/// re-inserted directly by `insertAction` (Sources.hs:158-159).
pub fn is_kd_xor_fact(fa: &LNFact) -> bool {
    use tamarin_term::function_symbols::{FunSym, AcSym};
    use tamarin_term::term::Term;
    if fa.tag != FactTag::Kd || fa.terms.len() != 1 { return false; }
    matches!(&fa.terms[0],
        Term::App(FunSym::Ac(AcSym::Xor), _))
}

// =============================================================================
// Construction helpers (NFact / LNFact specialised)
// =============================================================================

pub type LNFact = Fact<LNTerm>;

pub fn fresh_fact(t: LNTerm) -> LNFact { Fact::new(FactTag::Fresh, vec![t]) }
pub fn out_fact(t: LNTerm) -> LNFact { Fact::new(FactTag::Out, vec![t]) }
pub fn in_fact(t: LNTerm) -> LNFact { Fact::new(FactTag::In, vec![t]) }
pub fn ku_fact(t: LNTerm) -> LNFact { Fact::new(FactTag::Ku, vec![t]) }
pub fn kd_fact(t: LNTerm) -> LNFact { Fact::new(FactTag::Kd, vec![t]) }
// Intentionally retained: faithful HS port; no caller yet.
pub fn ded_fact(t: LNTerm) -> LNFact { Fact::new(FactTag::Ded, vec![t]) }

/// `kLogFact` from Haskell's `Theory.Model.Fact:280`:
///   `kLogFact = protoFact Linear "K" . return`
///
/// ISend's action — the trace event "the intruder knows m".  A
/// regular ProtoFact tagged with name "K", not `FactTag::Ded`.
/// User formulas writing `K(t) @ j` parse into atoms with the
/// same tag (per the parser's fall-through for unknown fact
/// names), so action goals like `K(t) @ j` match ISend instances.
pub fn k_log_fact(t: LNTerm) -> LNFact {
    Fact::new(FactTag::Proto(Multiplicity::Linear, "K".into(), 1), vec![t])
}
pub fn term_fact(t: LNTerm) -> LNFact { Fact::new(FactTag::Term, vec![t]) }

pub fn proto_fact(mult: Multiplicity, name: &str, terms: Vec<LNTerm>) -> LNFact {
    Fact::new(FactTag::Proto(mult, tamarin_term::intern::intern_str(name), terms.len()), terms)
}

/// View a protocol or `In` fact's terms. Port of HS `protoOrInFactView`
/// (Fact.hs:331): a `ProtoFact` yields its terms; an `In` fact (arity 1)
/// yields its single term; anything else is `None`. A malformed `In` fact
/// (arity ≠ 1) panics, mirroring HS `errMalformed`.
pub fn proto_or_in_fact_view(fa: &LNFact) -> Option<Vec<LNTerm>> {
    match &fa.tag {
        FactTag::Proto(..) => Some(fa.terms.clone()),
        FactTag::In => match &fa.terms[..] {
            [m] => Some(vec![m.clone()]),
            _ => panic!("proto_or_in_fact_view: malformed In fact"),
        },
        _ => None,
    }
}

/// View a protocol or `Out` fact's terms. Port of HS `protoOrOutFactView`
/// (Fact.hs:339).
pub fn proto_or_out_fact_view(fa: &LNFact) -> Option<Vec<LNTerm>> {
    match &fa.tag {
        FactTag::Proto(..) => Some(fa.terms.clone()),
        FactTag::Out => match &fa.terms[..] {
            [m] => Some(vec![m.clone()]),
            _ => panic!("proto_or_out_fact_view: malformed Out fact"),
        },
        _ => None,
    }
}

pub fn proto_fact_ann(
    mult: Multiplicity,
    name: &str,
    annotations: BTreeSet<FactAnnotation>,
    terms: Vec<LNTerm>,
) -> LNFact {
    Fact {
        tag: FactTag::Proto(mult, tamarin_term::intern::intern_str(name), terms.len()),
        annotations,
        terms,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::builtin::msg_var;

    #[test]
    fn proto_fact_arity() {
        let f = proto_fact(Multiplicity::Linear, "P", vec![msg_var("x", 0), msg_var("y", 0)]);
        assert_eq!(f.arity(), 2);
        assert_eq!(fact_tag_arity(&f.tag), 2);
    }

    #[test]
    fn equality_ignores_annotations() {
        let a = fresh_fact(msg_var("x", 0)).annotate(FactAnnotation::SolveFirst);
        let b = fresh_fact(msg_var("x", 0));
        assert_eq!(a, b);
    }

    #[test]
    fn linear_vs_persistent() {
        let lin = proto_fact(Multiplicity::Linear, "P", vec![]);
        let per = proto_fact(Multiplicity::Persistent, "Q", vec![]);
        assert!(lin.is_linear());
        assert!(per.is_persistent());
    }

    #[test]
    fn k_fact_categorisation() {
        assert!(ku_fact(msg_var("x", 0)).is_ku());
        assert!(kd_fact(msg_var("x", 0)).is_kd());
    }

    // =========================================================================
    // Haskell-faithfulness invariants.
    //
    // Fact.hs:128:  `data Multiplicity = Persistent | Linear`
    // Fact.hs:132:  `data FactTag = ProtoFact ... | FreshFact | OutFact |
    //                              InFact | KUFact | KDFact | DedFact |
    //                              TermFact`
    //
    // FactTag Ord matters because BTreeSet<LNFact> is used in injective-fact
    // analysis and rule-conclusion sets.  If the tag order drifts, the
    // "Proto facts come first" iteration property breaks, which downstream
    // injective-fact code assumes.
    // =========================================================================

    /// Multiplicity: `Persistent < Linear` from Fact.hs:128.
    #[test]
    fn multiplicity_ord_matches_haskell_declaration() {
        assert!(Multiplicity::Persistent < Multiplicity::Linear,
                "Persistent must sort before Linear (Fact.hs:128)");
    }

    /// `FactTag` Ord — `Proto < Fresh < Out < In < Ku < Kd < Ded < Term`.
    ///
    /// Critical: Proto facts MUST sort before all built-in tags so that
    /// BTreeSet<LNFact> iteration puts protocol facts first.  Multiple
    /// downstream code paths (simpInjectiveFactEqMon, partial_atom_valuation
    /// nonUnifiableNodes) iterate fact sets and depend on Proto-first order
    /// for deterministic case ranking.
    #[test]
    fn fact_tag_ord_proto_sorts_before_builtins() {
        let proto = FactTag::Proto(Multiplicity::Linear, "Foo".into(), 0);
        let fresh = FactTag::Fresh;
        assert!(proto < fresh,
                "Proto must sort before Fresh (Haskell decl order Fact.hs:132)");
        assert!(fresh < FactTag::Out);
        assert!(FactTag::Out  < FactTag::In);
        assert!(FactTag::In   < FactTag::Ku);
        assert!(FactTag::Ku   < FactTag::Kd);
        assert!(FactTag::Kd   < FactTag::Ded);
        assert!(FactTag::Ded  < FactTag::Term);
    }

    /// `Proto` facts compare by `(multiplicity, name, arity)` triple.
    /// Specifically: Linear and Persistent same-named facts compare via
    /// Multiplicity first, then name, then arity.  If we drift, lemmas
    /// using both `!P(x)` (persistent) and `P(x)` (linear) versions get
    /// inconsistently bucketed.
    #[test]
    fn proto_fact_tag_compare_by_multiplicity_then_name_then_arity() {
        let lp = FactTag::Proto(Multiplicity::Linear,     "P".into(), 1);
        let pp = FactTag::Proto(Multiplicity::Persistent, "P".into(), 1);
        // Persistent < Linear (per Haskell Multiplicity Ord).
        assert!(pp < lp);

        // Same multiplicity, different name → name breaks tie.
        let la = FactTag::Proto(Multiplicity::Linear, "A".into(), 1);
        assert!(la < lp);

        // Same multiplicity+name, different arity → arity breaks tie.
        let lp2 = FactTag::Proto(Multiplicity::Linear, "P".into(), 2);
        assert!(lp < lp2);
    }

    /// `ku` and `kd` predicates are mutually exclusive.
    /// Used in `enforce_kd_fact_uniqueness` to skip KU facts.
    #[test]
    fn ku_and_kd_are_mutually_exclusive() {
        let ku = ku_fact(msg_var("x", 0));
        let kd = kd_fact(msg_var("x", 0));
        assert!(ku.is_ku() && !ku.is_kd());
        assert!(kd.is_kd() && !kd.is_ku());
    }
}
