//! Port of the data-only portion of `Theory.Syntactic.Predicate` from
//! `lib/theory/src/Theory/Syntactic/Predicate.hs`.
//!
//! Predicates name a fact pattern and provide a formula expansion that
//! replaces the syntactic-sugar `Pred(...)` atom with a concrete logical
//! body. We port:
//! - `Predicate` data type + smart constructor (`mk_predicate`)
//! - `smaller_fact` and the `builtinPredicates` list (just `Smaller`)
//! - `lookup_predicate`
//!
//! Not yet ported: `expandFormula` — needs a full `traverseFormulaAtom`
//! and substitution machinery over `ProtoFormula`. That's deferred until
//! `Theory.Model.Formula` has its NNF / atom traversal helpers ported.

use crate::fact::{Fact, FactTag, Multiplicity};
use crate::formula::LNFormula;
use tamarin_term::lterm::LVar;

/// A user-defined predicate: a fact-pattern paired with a formula that
/// expands every reference to it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Predicate {
    pub fact: Fact<LVar>,
    pub formula: LNFormula,
}

impl Predicate {
    /// `mk_predicate name formula` — capitalise the leading character of
    /// `name`, then build a linear protocol fact carrying the formula's
    /// free variables.
    pub fn new(name: &str, formula: LNFormula, free_vars: Vec<LVar>) -> Self {
        let mut chars = name.chars();
        let cap = match chars.next() {
            Some(c) => c.to_ascii_uppercase().to_string() + chars.as_str(),
            None => String::new(),
        };
        let arity = free_vars.len();
        Predicate {
            fact: Fact::new(FactTag::Proto(Multiplicity::Linear, cap, arity), free_vars),
            formula,
        }
    }
}

/// `smallerFact t1 t2` — the pattern fact for the built-in `Smaller`
/// predicate.
pub fn smaller_fact<T>(t1: T, t2: T) -> Fact<T> {
    Fact::new(
        FactTag::Proto(Multiplicity::Linear, "Smaller".into(), 2),
        vec![t1, t2],
    )
}

/// `lookupPredicate fa preds`: find the predicate whose fact tag matches
/// `fa`'s tag. Only `preds` is searched; unlike the Haskell original this
/// does not append the built-in predicates list.
pub fn lookup_predicate<'a, T: Eq>(
    fa: &Fact<T>,
    preds: &'a [Predicate],
) -> Option<&'a Predicate> {
    preds
        .iter()
        .find(|p| p.fact.tag == fa.tag)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::ProtoFormula;
    use tamarin_term::lterm::LSort;

    #[test]
    fn capitalisation_in_constructor() {
        let f: LNFormula = ProtoFormula::ltrue();
        let p = Predicate::new("smaller", f, vec![]);
        assert!(matches!(p.fact.tag, FactTag::Proto(_, ref n, _) if n == "Smaller"));
    }

    #[test]
    fn smaller_fact_arity() {
        let f: Fact<LVar> = smaller_fact(
            LVar::new("x", LSort::Msg, 0),
            LVar::new("y", LSort::Msg, 0),
        );
        assert_eq!(f.arity(), 2);
    }

    #[test]
    fn lookup_finds_match() {
        let f: LNFormula = ProtoFormula::ltrue();
        let p = Predicate::new("foo", f, vec![]);
        let probe: Fact<LVar> = Fact::new(p.fact.tag.clone(), vec![]);
        let preds = vec![p];
        assert!(lookup_predicate(&probe, &preds).is_some());
    }
}
