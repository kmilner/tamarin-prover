//! Port of `Theory.Model.Formula` from
//! `lib/theory/src/Theory/Model/Formula.hs` — data type + basic builders.
//!
//! The Haskell version uses a locally-nameless representation: bound
//! variables are `BVar::Bound(de_bruijn_idx)`, free variables are `Free(v)`.
//!
//! Not yet ported: `nnf`, `pullquants`, `prenex`, `pnf`, `simplifyFormula`.
//! Those are pure transformations on the data type and can be added
//! incrementally. (Pretty-printing of the parser-AST formula representation
//! lives in `pretty_formula.rs`; this `ProtoFormula` has no pretty-printer.)

use crate::atom::{ProtoAtom, Unit2};
use tamarin_term::lterm::{BVar, LVar, Name};
use tamarin_term::vterm::VTerm;

/// Logical connectives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Connective {
    And,
    Or,
    Imp,
    Iff,
}

/// Quantifiers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Quantifier {
    All,
    Ex,
}

/// First-order formula in locally-nameless representation.
///
/// - `S`: syntactic-sugar type (use `()` for the post-parsing form)
/// - `H`: name/sort hint stored at each binder
/// - `C`: constant type for terms
/// - `V`: free-variable type for terms
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProtoFormula<S, H, C, V> {
    Atom(ProtoAtom<S, VTerm<C, BVar<V>>>),
    /// `true`/`false`.
    Tf(bool),
    Not(Box<ProtoFormula<S, H, C, V>>),
    Conn(
        Connective,
        Box<ProtoFormula<S, H, C, V>>,
        Box<ProtoFormula<S, H, C, V>>,
    ),
    Qua(Quantifier, H, Box<ProtoFormula<S, H, C, V>>),
}

/// `Formula` after parsing: no syntactic sugar.
pub type Formula<H, C, V> = ProtoFormula<Unit2, H, C, V>;
pub type LFormula<C> = Formula<(String, tamarin_term::lterm::LSort), C, LVar>;
pub type LNFormula = LFormula<Name>;

impl<S, H, C, V> ProtoFormula<S, H, C, V> {
    pub fn ltrue() -> Self { ProtoFormula::Tf(true) }
    pub fn lfalse() -> Self { ProtoFormula::Tf(false) }

    pub fn not(self) -> Self { ProtoFormula::Not(Box::new(self)) }

    pub fn and(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::And, Box::new(self), Box::new(other))
    }
    pub fn or(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::Or, Box::new(self), Box::new(other))
    }
    pub fn implies(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::Imp, Box::new(self), Box::new(other))
    }
    pub fn iff(self, other: Self) -> Self {
        ProtoFormula::Conn(Connective::Iff, Box::new(self), Box::new(other))
    }

    pub fn for_all(hint: H, body: Self) -> Self {
        ProtoFormula::Qua(Quantifier::All, hint, Box::new(body))
    }
    pub fn exists(hint: H, body: Self) -> Self {
        ProtoFormula::Qua(Quantifier::Ex, hint, Box::new(body))
    }
}

/// Scope-blind rewrite of every atom in the formula. Note that scope-aware
/// operations (`quantify`/`openFormula`/`shiftFreeIndices`) need the
/// `foldFormulaScope`-style binder-depth index, which this helper does not
/// thread, so they cannot be built directly on top of it.
pub fn map_atoms<S, H, C, V, F>(f: &mut F, formula: ProtoFormula<S, H, C, V>) -> ProtoFormula<S, H, C, V>
where
    F: FnMut(ProtoAtom<S, VTerm<C, BVar<V>>>) -> ProtoAtom<S, VTerm<C, BVar<V>>>,
{
    match formula {
        ProtoFormula::Atom(a) => ProtoFormula::Atom(f(a)),
        ProtoFormula::Tf(b) => ProtoFormula::Tf(b),
        ProtoFormula::Not(inner) => ProtoFormula::Not(Box::new(map_atoms(f, *inner))),
        ProtoFormula::Conn(c, l, r) => ProtoFormula::Conn(
            c,
            Box::new(map_atoms(f, *l)),
            Box::new(map_atoms(f, *r)),
        ),
        ProtoFormula::Qua(q, h, body) => {
            ProtoFormula::Qua(q, h, Box::new(map_atoms(f, *body)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::LSort;

    fn lftrue() -> LNFormula { ProtoFormula::ltrue() }
    fn lffalse() -> LNFormula { ProtoFormula::lfalse() }

    #[test]
    fn build_a_simple_formula() {
        // ∀ x:msg. true ∧ ¬false
        let body: LNFormula = lftrue().and(lffalse().not());
        let f: LNFormula = ProtoFormula::for_all(("x".into(), LSort::Msg), body);
        if let ProtoFormula::Qua(q, _, _) = f {
            assert_eq!(q, Quantifier::All);
        } else {
            panic!();
        }
    }

    #[test]
    fn implies_constructs_imp() {
        let f: LNFormula = lftrue().implies(lffalse());
        assert!(matches!(f, ProtoFormula::Conn(Connective::Imp, _, _)));
    }

    // =========================================================================
    // Haskell-faithfulness invariants for Connective and Quantifier order.
    //
    // Formula.hs:104-108: `data Connective = And | Or | Imp | Iff`
    //                     `data Quantifier = All | Ex`
    //
    // These orders matter for any BTreeMap<Connective,_> iteration or
    // structural comparison.  More importantly, Atom variant order
    // affects partial_atom_valuation iteration in simplifyGuarded.
    // =========================================================================

    /// `Connective` Ord — `And < Or < Imp < Iff` from Formula.hs:104.
    #[test]
    fn connective_ord_matches_haskell_declaration() {
        assert!(Connective::And < Connective::Or);
        assert!(Connective::Or  < Connective::Imp);
        assert!(Connective::Imp < Connective::Iff);
    }

    /// `Quantifier` Ord — `All < Ex` from Formula.hs:108.
    ///
    /// This is the order that downstream `partial_atom_valuation`
    /// and `simplify_guarded` use to decompose quantified formulas.
    /// If Ex sorted before All, the simplifier would visit existentials
    /// first and miss universal-driven contradictions.
    #[test]
    fn quantifier_ord_matches_haskell_declaration() {
        assert!(Quantifier::All < Quantifier::Ex,
                "All MUST sort before Ex (Formula.hs:108)");
    }
}
