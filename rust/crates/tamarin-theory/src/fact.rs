//! Port of `Theory.Model.Fact` from `lib/theory/src/Theory/Model/Fact.hs`.
//!
//! Multiset-rewriting facts. This port covers the data type plus the
//! tagging / construction / query API. The Maude-backed `unifyLNFactEqs`,
//! `unifiableLNFacts`, and normalisation entry points are not included
//! yet — those need the AC unification bridge that's still a stub.

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
    Proto(Multiplicity, String, usize),
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
    fn map_free(self, f: &mut dyn FnMut(LVar) -> LVar) -> Self {
        Fact {
            tag: self.tag,
            annotations: self.annotations,
            terms: self.terms.into_iter().map(|t| t.map_free(f)).collect(),
        }
    }
}

// =============================================================================
// Tag queries
// =============================================================================

pub fn fact_tag_name(t: &FactTag) -> String {
    match t {
        FactTag::Proto(_, n, _) => n.clone(),
        FactTag::Fresh => "Fr".into(),
        FactTag::Out => "Out".into(),
        FactTag::In => "In".into(),
        FactTag::Ku => "KU".into(),
        FactTag::Kd => "KD".into(),
        FactTag::Ded => "Ded".into(),
        FactTag::Term => "Term".into(),
    }
}

pub fn fact_tag_arity(t: &FactTag) -> usize {
    match t {
        FactTag::Proto(_, _, n) => *n,
        FactTag::Fresh | FactTag::Out | FactTag::In => 1,
        FactTag::Ku | FactTag::Kd | FactTag::Ded | FactTag::Term => 1,
    }
}

pub fn fact_tag_multiplicity(t: &FactTag) -> Multiplicity {
    match t {
        FactTag::Proto(m, _, _) => *m,
        // Built-in tags are Linear by default.
        _ => Multiplicity::Linear,
    }
}

// =============================================================================
// Predicates on Fact<T>
// =============================================================================

impl<T> Fact<T> {
    pub fn is_linear(&self) -> bool { fact_tag_multiplicity(&self.tag) == Multiplicity::Linear }
    pub fn is_persistent(&self) -> bool { fact_tag_multiplicity(&self.tag) == Multiplicity::Persistent }
    pub fn is_proto(&self) -> bool { matches!(self.tag, FactTag::Proto(_, _, _)) }
    pub fn is_in_fact(&self) -> bool { self.tag == FactTag::In }
    pub fn is_klog(&self) -> bool {
        matches!(self.tag, FactTag::Ku | FactTag::Kd | FactTag::Ded)
    }
    pub fn is_k_fact(&self) -> bool {
        matches!(self.tag, FactTag::Ku | FactTag::Kd)
    }
    pub fn is_ku(&self) -> bool { self.tag == FactTag::Ku }
    pub fn is_kd(&self) -> bool { self.tag == FactTag::Kd }
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
    Fact::new(FactTag::Proto(mult, name.into(), terms.len()), terms)
}

pub fn proto_fact_ann(
    mult: Multiplicity,
    name: &str,
    annotations: BTreeSet<FactAnnotation>,
    terms: Vec<LNTerm>,
) -> LNFact {
    Fact {
        tag: FactTag::Proto(mult, name.into(), terms.len()),
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
        assert!(ku_fact(msg_var("x", 0)).is_klog());
        assert!(!fresh_fact(msg_var("x", 0)).is_klog());
    }
}
