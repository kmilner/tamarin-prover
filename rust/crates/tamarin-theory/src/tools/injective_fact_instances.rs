//! Skeleton port of `Theory.Tools.InjectiveFactInstances`.
//!
//! Computes an under-approximation of the set of fact tags whose
//! instances always occur uniquely in a state — protocols often rely
//! on this for security arguments (e.g. session-state facts).
//!
//! The full Haskell algorithm:
//! 1. For each fact tag, collect every protocol rule that produces or
//!    consumes it.
//! 2. Trace its first argument through the rule graph, tracking
//!    monotonic behaviour at each position (Constant / Increasing /
//!    Decreasing / StrictlyIncreasing / StrictlyDecreasing /
//!    Unstable / Unspecified).
//! 3. A tag is injective if every rule using it satisfies the
//!    Fr-fact-or-single-premise condition.
//!
//! The Rust port currently exposes the `MonotonicBehaviour` enum and
//! a `simple_injective_fact_instances` stub. A real implementation
//! follows once we have macro expansion + the typed rule layer.

use crate::fact::FactTag;
use crate::rule::ProtoRuleE;

/// How a particular term position evolves across rule applications.
/// Variant order matches Haskell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MonotonicBehaviour {
    Constant,
    Increasing,
    Decreasing,
    StrictlyIncreasing,
    StrictlyDecreasing,
    Unstable,
    Unspecified,
}

impl std::fmt::Display for MonotonicBehaviour {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            MonotonicBehaviour::Constant => "=",
            MonotonicBehaviour::Increasing => "≤",
            MonotonicBehaviour::Decreasing => "≥",
            MonotonicBehaviour::StrictlyIncreasing => "<",
            MonotonicBehaviour::StrictlyDecreasing => ">",
            MonotonicBehaviour::Unstable => ".",
            MonotonicBehaviour::Unspecified => "?",
        };
        write!(f, "{}", s)
    }
}

/// Combine two `MonotonicBehaviour`s — direct port of Haskell's
/// `combine` in `simpleInjectiveFactInstances`.  Used to merge the
/// per-rule shapes into a single behaviour vector for the tag.
pub fn combine_behaviour(x: MonotonicBehaviour, y: MonotonicBehaviour) -> MonotonicBehaviour {
    use MonotonicBehaviour::*;
    if x == y { return x; }
    match (x, y) {
        (Unstable, _) | (_, Unstable) => Unstable,
        (Unspecified, b) | (b, Unspecified) => b,
        (StrictlyIncreasing, Increasing) | (StrictlyIncreasing, Constant) => Increasing,
        (Increasing, StrictlyIncreasing) | (Constant, StrictlyIncreasing) => Increasing,
        (StrictlyDecreasing, Decreasing) | (StrictlyDecreasing, Constant) => Decreasing,
        (Decreasing, StrictlyDecreasing) | (Constant, StrictlyDecreasing) => Decreasing,
        (StrictlyIncreasing, _) | (_, StrictlyIncreasing) => Unstable,
        (StrictlyDecreasing, _) | (_, StrictlyDecreasing) => Unstable,
        (Increasing, Decreasing) | (Decreasing, Increasing) => Unstable,
        (Increasing, Constant) | (Constant, Increasing) => Increasing,
        (Decreasing, Constant) | (Constant, Decreasing) => Decreasing,
        _ => Unstable,
    }
}

/// Simple under-approximation of the injective-fact-instance set.
///
/// A linear fact tag `T` is **injective** iff for every protocol rule R
/// in which T appears as a conclusion, R either:
///   (a) consumes T as a premise with the same first term (a copy
///       step — Loop / Copy / Continue), or
///   (b) produces T from a `Fr(t)` premise where `t` is the first arg
///       of the new T fact (a creation step — Init / Setup).
///
/// Behaviour at non-first positions is computed per rule and combined
/// across rules via `combine_behaviour`:
///   - For a **copy rule** (T premise + T conclusion with same first
///     term), each non-first position contributes `Constant` if the
///     premise term and conclusion term are syntactically equal, else
///     `Unstable`.  (Haskell additionally checks the reducible-subterm
///     order; we leave that to the full port.)
///   - For a **fresh creation rule**, every position contributes
///     `Unspecified`.
///
/// The result is a per-position list of behaviours of length
/// `arity - 1` (the first position is the injectivity index).  Shape
/// flattening for pair-arguments (Haskell's `getPairTerms` /
/// `shapeTerm` / `trimmedPairTerms`) is currently treated as
/// non-flattened — a single behaviour per arg position rather than
/// per pair-leaf.
pub fn simple_injective_fact_instances(
    rules: &[ProtoRuleE],
    reducible: &tamarin_term::function_symbols::FunSig,
) -> Vec<(FactTag, Vec<MonotonicBehaviour>)> {
    use crate::fact::{LNFact, fact_tag_arity, fact_tag_multiplicity, Multiplicity};
    use MonotonicBehaviour::*;

    fn first_term(f: &LNFact) -> Option<&tamarin_term::lterm::LNTerm> {
        f.terms.first()
    }
    fn fresh_premise_for(rule: &ProtoRuleE, t: &tamarin_term::lterm::LNTerm) -> bool {
        rule.premises.iter().any(|p|
            p.tag == crate::fact::FactTag::Fresh
                && p.terms.first() == Some(t))
    }
    fn copy_premise_for<'a>(
        rule: &'a ProtoRuleE, tag: &crate::fact::FactTag,
        t: &tamarin_term::lterm::LNTerm,
    ) -> Option<&'a crate::fact::LNFact> {
        rule.premises.iter().find(|p|
            &p.tag == tag && p.terms.first() == Some(t))
    }

    // Candidate tags = Linear protocol-fact tags that appear as BOTH a
    // conclusion AND a premise in the SAME rule.  Mirrors Haskell's
    // `simpleInjectiveFactInstances` (InjectiveFactInstances.hs:121-132):
    //   guard $ (factTagMultiplicity tag == Linear)
    //        && (tag `elem` (factTag <$> rPrems ru))
    //
    // Previously over-permissive: we included any tag that appeared as a
    // conclusion in any rule.  That added spurious InjectiveFacts
    // less-atoms (via `nonInjectiveFactInstances`) for protocols whose
    // linear facts get *created* in one rule and *consumed* in another
    // (no round-trip).  E.g. Artificial.spthy: Step1 creates St(x, k),
    // Step2 consumes it — neither rule has both → St not injective in
    // Haskell, but was injective in our port, creating a spurious cycle
    // in Fin_unique's case_2.
    use std::collections::BTreeSet;
    let mut candidates: BTreeSet<FactTag> = BTreeSet::new();
    for r in rules {
        let prem_tags: BTreeSet<FactTag> = r.premises.iter()
            .map(|p| p.tag.clone()).collect();
        for c in &r.conclusions {
            if !matches!(c.tag, FactTag::Proto(_, _, _)) { continue; }
            if fact_tag_multiplicity(&c.tag) != Multiplicity::Linear { continue; }
            if fact_tag_arity(&c.tag) == 0 { continue; }
            if !prem_tags.contains(&c.tag) { continue; }
            candidates.insert(c.tag.clone());
        }
    }

    let mut out: Vec<(FactTag, Vec<MonotonicBehaviour>)> = Vec::new();
    'tags: for tag in candidates {
        let arity = fact_tag_arity(&tag);
        let behaviour_len = arity.saturating_sub(1);
        // Aggregate behaviour across all rules, starting from
        // `Unspecified` (the default candidate shape).
        let mut combined: Vec<MonotonicBehaviour> = vec![Unspecified; behaviour_len];

        for r in rules {
            for conc in r.conclusions.iter().filter(|c| c.tag == tag) {
                let t = match first_term(conc) { Some(x) => x, None => continue 'tags };
                if fresh_premise_for(r, t) { continue; }
                let prem = match copy_premise_for(r, &tag, t) {
                    Some(p) => p,
                    None => continue 'tags,  // not statically injective
                };
                // Compare position-by-position (positions ≥ 1).
                // Mirrors HS `getBehaviour` (InjectiveFactInstances.hs:213-219):
                //   getBehaviour (t1, t2) | t1 == t2 = Constant
                //   getBehaviour (t1, t2) | elemNotBelowReducible reducible t1 t2 = StrictlyIncreasing
                //   getBehaviour (t1, t2) | elemNotBelowReducible reducible t2 t1 = StrictlyDecreasing
                //   getBehaviour _ = Unstable
                // (constraints-based case omitted — not used by current callers.)
                for k in 1..arity {
                    let p_term = match prem.terms.get(k) { Some(x) => x, None => continue 'tags };
                    let c_term = match conc.terms.get(k) { Some(x) => x, None => continue 'tags };
                    let bh = if p_term == c_term {
                        Constant
                    } else if crate::tools::subterm_store::elem_not_below_reducible(
                        reducible, p_term, c_term) {
                        StrictlyIncreasing
                    } else if crate::tools::subterm_store::elem_not_below_reducible(
                        reducible, c_term, p_term) {
                        StrictlyDecreasing
                    } else {
                        Unstable
                    };
                    let i = k - 1;
                    combined[i] = combine_behaviour(combined[i], bh);
                }
            }
        }
        out.push((tag, combined));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn monotonic_behaviour_renders_unicode() {
        assert_eq!(MonotonicBehaviour::Constant.to_string(), "=");
        assert_eq!(MonotonicBehaviour::Increasing.to_string(), "≤");
        assert_eq!(MonotonicBehaviour::StrictlyIncreasing.to_string(), "<");
        assert_eq!(MonotonicBehaviour::Unstable.to_string(), ".");
    }

    #[test]
    fn empty_rules_no_injective_facts() {
        let r: Vec<ProtoRuleE> = Vec::new();
        assert!(simple_injective_fact_instances(&r, &Default::default()).is_empty());
    }

    /// Loop-style rules: `Start: Fr(x) → A(x); Loop: A(x) → A(x); Stop: A(x) → []`.
    /// `A` should be detected as injective because every rule producing it
    /// either consumes `A(x)` with same first arg or has `Fr(x)` premise.
    #[test]
    fn loop_pattern_detects_a_as_injective() {
        use crate::fact::{Fact, FactTag, Multiplicity, fresh_fact};
        use crate::rule::{Rule, ProtoRuleEInfo};
        use tamarin_term::builtin::msg_var;

        let a_tag = FactTag::Proto(Multiplicity::Linear, "A".to_string(), 1);
        let a_fact = Fact::new(a_tag.clone(), vec![msg_var("x", 0)]);
        let start: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Start"),
            vec![fresh_fact(msg_var("x", 0))],
            vec![a_fact.clone()],
            vec![],
        );
        let loop_r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Loop"),
            vec![a_fact.clone()],
            vec![a_fact.clone()],
            vec![],
        );
        let stop: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Stop"),
            vec![a_fact.clone()],
            vec![],
            vec![],
        );
        let rules = vec![start, loop_r, stop];
        let inj = simple_injective_fact_instances(&rules, &Default::default());
        assert_eq!(inj.len(), 1);
        assert_eq!(inj[0].0, a_tag);
    }

    /// `S(~id, k)` with copy rule that preserves `k` ⇒ position 1
    /// behaviour should be `Constant`.
    #[test]
    fn copy_preserving_arg_marks_position_constant() {
        use crate::fact::{Fact, FactTag, Multiplicity, fresh_fact};
        use crate::rule::{Rule, ProtoRuleEInfo};
        use tamarin_term::builtin::msg_var;

        let s_tag = FactTag::Proto(Multiplicity::Linear, "S".to_string(), 2);
        let s_fact = Fact::new(s_tag.clone(),
            vec![msg_var("id", 0), msg_var("k", 0)]);
        let init: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Init"),
            vec![fresh_fact(msg_var("id", 0))],
            vec![s_fact.clone()],
            vec![],
        );
        let copy: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Copy"),
            vec![s_fact.clone()],
            vec![s_fact.clone()],
            vec![],
        );
        let rules = vec![init, copy];
        let inj = simple_injective_fact_instances(&rules, &Default::default());
        assert_eq!(inj.len(), 1);
        assert_eq!(inj[0].0, s_tag);
        assert_eq!(inj[0].1.len(), 1);
        assert_eq!(inj[0].1[0], MonotonicBehaviour::Constant);
    }

    /// Non-injective: a rule produces `B(t)` but doesn't consume `B`
    /// or have a Fresh-premise binding `t`.
    #[test]
    fn arbitrary_production_not_injective() {
        use crate::fact::{Fact, FactTag, Multiplicity};
        use crate::rule::{Rule, ProtoRuleEInfo};
        use tamarin_term::builtin::msg_var;

        let b_tag = FactTag::Proto(Multiplicity::Linear, "B".to_string(), 1);
        let b_fact = Fact::new(b_tag.clone(), vec![msg_var("y", 0)]);
        // No Fresh premise binding `y`, no `B` premise.
        let weird: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Weird"),
            vec![],
            vec![b_fact.clone()],
            vec![],
        );
        assert!(simple_injective_fact_instances(&[weird], &Default::default()).is_empty());
    }

    // =========================================================================
    // Haskell-faithfulness invariants — pinning the candidate filter
    // (#206: `Artificial::Fin_unique` regression).
    //
    // Mirrors Haskell `simpleInjectiveFactInstances`
    // (InjectiveFactInstances.hs:121-132):
    //
    //   guard $ (factTagMultiplicity tag == Linear)
    //        && (tag `elem` (factTag <$> rPrems ru))
    //
    // The `tag elem prems` check is PER-RULE, not across all rules.
    // We previously had a broader filter (any rule that produces the
    // tag) which counted facts as injective when one rule created them
    // and another consumed them — but no SINGLE rule had both prems
    // AND concs.  This added spurious less-atoms and broke Fin_unique's
    // case_2.
    // =========================================================================

    /// Fact created in Rule1 and consumed in Rule2 (no single rule has
    /// it in both prems and concs) — must NOT be injective.
    ///
    /// This is the Artificial.spthy::Fin_unique shape:
    ///   Step1: Fr(x) → St(x, k)
    ///   Step2: St(x, k) → []
    /// No round-trip → St is NOT injective in Haskell.
    /// Without per-rule filter, we'd mark it injective and add a
    /// spurious less-atom in case_2.
    #[test]
    fn cross_rule_create_consume_is_not_injective() {
        use crate::fact::{Fact, FactTag, Multiplicity, fresh_fact};
        use crate::rule::{Rule, ProtoRuleEInfo};
        use tamarin_term::builtin::msg_var;

        let st_tag = FactTag::Proto(Multiplicity::Linear, "St".to_string(), 2);
        let st_fact = Fact::new(st_tag.clone(),
            vec![msg_var("x", 0), msg_var("k", 0)]);
        // Step1 creates St but doesn't consume it.
        let step1: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Step1"),
            vec![fresh_fact(msg_var("x", 0))],
            vec![st_fact.clone()],
            vec![],
        );
        // Step2 consumes St but doesn't produce it.
        let step2: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("Step2"),
            vec![st_fact.clone()],
            vec![],
            vec![],
        );

        let inj = simple_injective_fact_instances(&[step1, step2], &Default::default());
        assert!(inj.is_empty(),
            "St is created in Step1, consumed in Step2, but NO single rule \
             has St in both prems and concs → must NOT be marked injective. \
             Haskell `simpleInjectiveFactInstances` checks the per-rule \
             `tag elem rPrems ru` condition.  Otherwise spurious less-atoms \
             break Artificial::Fin_unique case_2.  (Memory: \
             project_rust_injective_fact_candidate_filter.md)");
    }

    /// Persistent facts (multiplicity = Persistent) are never marked
    /// injective.  Mirrors Haskell's
    /// `guard (factTagMultiplicity tag == Linear)`.
    #[test]
    fn persistent_facts_are_not_injective() {
        use crate::fact::{Fact, FactTag, Multiplicity};
        use crate::rule::{Rule, ProtoRuleEInfo};
        use tamarin_term::builtin::msg_var;

        let p_tag = FactTag::Proto(Multiplicity::Persistent, "P".to_string(), 1);
        let p_fact = Fact::new(p_tag.clone(), vec![msg_var("x", 0)]);
        // Even with both prems + concs (which would normally pass the
        // candidate filter), Persistent disqualifies.
        let r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("R"),
            vec![p_fact.clone()],
            vec![p_fact.clone()],
            vec![],
        );
        let inj = simple_injective_fact_instances(&[r], &Default::default());
        assert!(inj.is_empty(),
            "Persistent facts are never injective (Haskell: \
             `factTagMultiplicity tag == Linear` guard)");
    }

    /// Arity-0 facts (no args) cannot have monotonic behaviour and
    /// must be excluded.  Per Haskell `behaviourLen = max 0 (arity-1)`
    /// is 0; combined with the candidate filter check, arity-0 facts
    /// get filtered.  Our impl has an explicit `if arity == 0 continue`.
    #[test]
    fn arity_zero_facts_are_not_injective() {
        use crate::fact::{Fact, FactTag, Multiplicity};
        use crate::rule::{Rule, ProtoRuleEInfo};

        let z_tag = FactTag::Proto(Multiplicity::Linear, "Z".to_string(), 0);
        let z_fact = Fact::new(z_tag.clone(), vec![]);
        let r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("R"),
            vec![z_fact.clone()],
            vec![z_fact.clone()],
            vec![],
        );
        let inj = simple_injective_fact_instances(&[r], &Default::default());
        assert!(inj.is_empty(),
            "Arity-0 facts have no behaviour to track → never injective");
    }

    /// Built-in facts (Out, Ku, Kd, Fresh, etc.) are never injective.
    /// Only Proto-tagged facts get the analysis.
    #[test]
    fn builtin_facts_are_not_injective() {
        use crate::fact::{Fact, FactTag, fresh_fact};
        use crate::rule::{Rule, ProtoRuleEInfo};
        use tamarin_term::builtin::msg_var;

        // Two Out facts — never injective regardless of pattern.
        let out_fact = Fact::new(FactTag::Out, vec![msg_var("x", 0)]);
        let r: ProtoRuleE = Rule::new(
            ProtoRuleEInfo::standard("R"),
            vec![fresh_fact(msg_var("x", 0)), out_fact.clone()],
            vec![out_fact.clone()],
            vec![],
        );
        let inj = simple_injective_fact_instances(&[r], &Default::default());
        // Out should NOT appear (only Proto tags are candidates).
        assert!(inj.iter().all(|(t, _)| matches!(t, FactTag::Proto(_, _, _))),
            "Only Proto facts are injective candidates");
        assert!(!inj.iter().any(|(t, _)| matches!(t, FactTag::Out)),
            "Out is never injective");
    }
}
