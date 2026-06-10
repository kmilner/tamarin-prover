//! Port of `Theory.Model.Restriction` from
//! `lib/theory/src/Theory/Model/Restriction.hs` — data type only.
//!
//! `fromRuleRestriction` and the rewrite-then-quantify machinery is
//! deferred — it depends on a fully-ported `Formula` and on traversal
//! helpers we haven't built yet.

use crate::formula::LNFormula;
use tamarin_term::lterm::{LSort, LVar};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RestrictionAttribute {
    LhsRestriction,
    RhsRestriction,
    BothRestriction,
}

/// `ProtoRestriction f` from the Haskell version. We keep it generic to
/// match the SyntacticRestriction / Restriction split.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtoRestriction<F> {
    pub name: String,
    pub formula: F,
    pub original_formula: Option<F>,
}

impl<F> ProtoRestriction<F> {
    pub fn new(name: impl Into<String>, formula: F) -> Self {
        ProtoRestriction { name: name.into(), formula, original_formula: None }
    }
}

pub type Restriction = ProtoRestriction<LNFormula>;

/// `varNow`: the implicit "now" variable used in rule-level restrictions.
pub fn var_now() -> LVar {
    LVar::new("NOW", LSort::Node, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::ProtoFormula;

    #[test]
    fn build_restriction() {
        let f: LNFormula = ProtoFormula::ltrue();
        let r = Restriction::new("MyR", f);
        assert_eq!(r.name, "MyR");
    }

    #[test]
    fn var_now_is_node_sort() {
        assert_eq!(var_now().sort, LSort::Node);
    }
}
