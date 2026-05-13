//! Port of `Theory.Tools.RuleVariants` — computes the AC-variants of
//! a protocol rule via the Maude bridge.
//!
//! The Haskell reference does an "abstract → narrow → substitute →
//! simplify" dance:
//!
//! 1. Walk the rule's facts and replace each complex (reducible)
//!    sub-term with a fresh variable, remembering the bindings.
//! 2. Pack the replaced terms into a single tuple and ask Maude for
//!    its variants — `MaudeHandle::variants(packed) -> Vec<MSubst>`.
//! 3. For each variant subst, compose with the abstraction-bindings
//!    subst and renormalise.
//! 4. Simplify via `simp_disjunction`.
//! 5. Wrap as a `ProtoRuleAC` with the surviving substitutions stored
//!    in its `variants` field.
//!
//! For the first cut we implement steps 2-5 directly on the
//! rule's free variables (no abstraction). That's adequate for rules
//! whose terms are already in a form Maude can variant-narrow; it
//! covers most parsed rules. The full `abstrTerm` machinery follows
//! once we've ported `Term.Narrowing.Variants`.

use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle};
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::Term;

use crate::fact::Fact;
use crate::rule::{
    ProtoRuleAC, ProtoRuleACInfo, ProtoRuleE,
};

type LNSubst = Subst<Name, LVar>;

#[derive(Debug, Clone)]
pub enum VariantsError {
    Maude(String),
    NoVariants,
}

impl std::fmt::Display for VariantsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariantsError::Maude(s) => write!(f, "Maude error: {}", s),
            VariantsError::NoVariants => write!(f, "no variants returned by Maude"),
        }
    }
}
impl std::error::Error for VariantsError {}
impl From<MaudeError> for VariantsError {
    fn from(e: MaudeError) -> Self { VariantsError::Maude(format!("{}", e)) }
}

/// `variantsProtoRule`: compute the AC-variants of a protocol rule.
/// Returns `Ok(None)` when Maude reports no non-trivial variants; the
/// caller can keep the rule as-is. Returns `Ok(Some(ac_rule))` with
/// the variant substitutions populated.
pub fn variants_proto_rule(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> Result<Option<ProtoRuleAC>, VariantsError> {
    // Pack all rule terms into a single tuple so we get one
    // variants-call per rule.
    let packed = pack_rule_terms(rule);
    if packed.is_none() {
        // No reducible terms → no variants beyond the identity.
        return Ok(Some(make_proto_rule_ac(rule, vec![LNSubstVFresh::empty()])));
    }
    let packed = packed.unwrap();
    let raw = maude.variants(&packed)?;
    if raw.is_empty() {
        return Ok(None);
    }
    let substs: Vec<LNSubstVFresh> = raw.into_iter()
        .map(|pairs| LNSubstVFresh::from_list(pairs.into_iter()))
        .collect();
    // Haskell runs simpDisjunction here to factor out a common
    // substitution across variants; our simp_disjunction collapses
    // identity-containing disjunctions to `Nothing`, which throws away
    // the non-identity variants we need for destructor-narrowing chain
    // enumeration. Skip the simplification and surface the raw
    // variants — downstream code wants every narrowing alternative.
    Ok(Some(make_proto_rule_ac(rule, substs)))
}

/// Pack every term-argument of every fact in `rule` into a single
/// `list(...)` term so it can be passed to `MaudeHandle::variants`.
/// Returns `None` if the rule has no term arguments at all.
fn pack_rule_terms(rule: &ProtoRuleE) -> Option<LNTerm> {
    use tamarin_term::function_symbols::FunSym;
    let mut all = Vec::new();
    for f in &rule.premises   { all.extend(f.terms.iter().cloned()); }
    for f in &rule.actions    { all.extend(f.terms.iter().cloned()); }
    for f in &rule.conclusions { all.extend(f.terms.iter().cloned()); }
    if all.is_empty() { None }
    else { Some(Term::App(FunSym::List, all)) }
}

/// Build a `ProtoRuleAC` from a `ProtoRuleE` plus the precomputed
/// variants list.
fn make_proto_rule_ac(
    rule: &ProtoRuleE,
    variants: Vec<LNSubstVFresh>,
) -> ProtoRuleAC {
    let info = ProtoRuleACInfo {
        name: rule.info.name.clone(),
        attributes: rule.info.attributes.clone(),
        variants,
        loop_breakers: Vec::new(),
    };
    crate::rule::Rule {
        info,
        premises: rule.premises.clone(),
        conclusions: rule.conclusions.clone(),
        actions: rule.actions.clone(),
        new_vars: rule.new_vars.clone(),
    }
}

/// Compute the rule variants for `rule` and return one `ProtoRuleAC`
/// per Maude-returned variant, each with the variant's substitution
/// already applied to the rule's terms. Returns the empty vector when
/// Maude reports a single identity variant (caller can use the raw
/// rule).
///
/// Mirrors the result-shape of Haskell's `variantsProtoRule` plumbed
/// into the solver: `OpenProtoRule.variants` is a `Vec<ProtoRuleAC>`
/// where each entry has the variant's narrowing already baked in.
/// Destructor-narrowed conclusions (e.g. `Out(snd(sdec(msg, key)))`
/// reduced via `msg → senc(pair(_, t), key)` to `Out(t)`) become
/// enumerable by chain-fold without any extra Maude calls at search
/// time.
///
/// Only emits variants whose conclusion terms contain **no** reducible
/// function symbols — the partial-narrowing intermediates (e.g.
/// `Out(snd(senc-something))`) carry redundant destructor heads that
/// can't unify with a destructor-free goal and just bloat the search
/// case tree. The fully-narrowed forms are the ones chain-fold
/// actually needs.
pub fn expand_rule_variants(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
    reducible: &std::collections::BTreeSet<tamarin_term::function_symbols::FunSym>,
) -> Result<Vec<ProtoRuleAC>, VariantsError> {
    let ac = match variants_proto_rule(maude, rule)? {
        Some(ac) => ac,
        None => return Ok(Vec::new()),
    };
    let substs = &ac.info.variants;
    // Drop pure-renaming variants — Maude's identity variant comes
    // back as `x0 → ~mw1:Msg, x1 → ~mw2:Msg` etc., which carries no
    // information beyond α-renaming and is already covered by the
    // raw rule the solver instantiates. Keep only variants with at
    // least one App in their range (i.e. actually-narrowing).
    let useful: Vec<&LNSubstVFresh> = substs.iter()
        .filter(|s| s.range().any(|t| matches!(t, Term::App(_, _))))
        .collect();
    if useful.is_empty() {
        return Ok(Vec::new());
    }
    // After applying a variant substitution we must renormalise via
    // Maude so destructor terms reduce to their narrowed form: e.g.
    // `Out(snd(sdec(senc(pair(a,b), k), k)))` must reduce to `Out(b)`.
    // Without this, the rule conclusion stays as the literal pre-
    // reduction shape and won't unify with destructor-free goals.
    let normalize = |t: LNTerm| -> LNTerm {
        match maude.reduce(&t) { Ok(n) => n, Err(_) => t }
    };
    let mut out: Vec<ProtoRuleAC> = Vec::with_capacity(useful.len() + 1);
    // Include the raw (un-narrowed) rule alongside the narrowed
    // variants — Haskell's Disj-of-variants does include the
    // identity, and the chain-fold enumeration needs the un-narrowed
    // form for non-destructor-driven goals.
    {
        let info = ProtoRuleACInfo {
            name: rule.info.name.clone(),
            attributes: rule.info.attributes.clone(),
            variants: vec![LNSubstVFresh::empty()],
            loop_breakers: Vec::new(),
        };
        out.push(crate::rule::Rule {
            info,
            premises: rule.premises.clone(),
            conclusions: rule.conclusions.clone(),
            actions: rule.actions.clone(),
            new_vars: rule.new_vars.clone(),
        });
    }
    fn has_reducible(
        t: &LNTerm,
        rs: &std::collections::BTreeSet<tamarin_term::function_symbols::FunSym>,
    ) -> bool {
        match t {
            Term::Lit(_) => false,
            Term::App(f, args) =>
                rs.contains(f) || args.iter().any(|a| has_reducible(a, rs)),
        }
    }
    for vsubst in useful {
        let lnsubst: LNSubst = LNSubst::from_list(vsubst.to_list());
        let premises: Vec<Fact<LNTerm>> = rule.premises.iter()
            .map(|f| f.clone().map(|t| normalize(apply_vterm(&lnsubst, t))))
            .collect();
        let actions: Vec<Fact<LNTerm>> = rule.actions.iter()
            .map(|f| f.clone().map(|t| normalize(apply_vterm(&lnsubst, t))))
            .collect();
        let conclusions: Vec<Fact<LNTerm>> = rule.conclusions.iter()
            .map(|f| f.clone().map(|t| normalize(apply_vterm(&lnsubst, t))))
            .collect();
        let new_vars: Vec<LNTerm> = rule.new_vars.iter()
            .map(|t| normalize(apply_vterm(&lnsubst, t.clone())))
            .collect();
        // Skip partial-narrowing variants: if any conclusion term still
        // contains a reducible function symbol after normalisation, the
        // variant didn't fully narrow through. The raw rule already
        // covers this case shape, so emitting the intermediate just
        // bloats search.
        let has_destr_in_concs = conclusions.iter()
            .any(|f| f.terms.iter().any(|t| has_reducible(t, reducible)));
        if has_destr_in_concs { continue; }
        // Each per-variant ProtoRuleAC carries the identity inside —
        // the variant subst is already applied to the terms above.
        let info = ProtoRuleACInfo {
            name: rule.info.name.clone(),
            attributes: rule.info.attributes.clone(),
            variants: vec![LNSubstVFresh::empty()],
            loop_breakers: Vec::new(),
        };
        out.push(crate::rule::Rule {
            info,
            premises,
            conclusions,
            actions,
            new_vars,
        });
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_term::vterm::Lit;

    use crate::fact::{Fact, FactTag};
    use crate::rule::{ProtoRuleEInfo, ProtoRuleName, RuleAttributes, Rule};

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        let candidates = [
            "/home/linuxbrew/.linuxbrew/bin/maude",
            "/usr/local/bin/maude",
            "/usr/bin/maude",
            "maude",
        ];
        for c in &candidates {
            if std::path::Path::new(c).exists() { return Some((*c).to_string()); }
        }
        None
    }

    fn empty_rule(name: &str) -> ProtoRuleE {
        let info = ProtoRuleEInfo {
            name: ProtoRuleName::Stand(name.to_string()),
            attributes: RuleAttributes::empty(),
            restrictions: Vec::new(),
        };
        Rule::new(info, Vec::new(), Vec::new(), Vec::new())
    }

    #[test]
    fn variants_of_rule_with_no_terms_is_identity() {
        let path = match maude_path() {
            Some(p) => p,
            None => { eprintln!("skipping: no maude"); return; }
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let rule = empty_rule("R");
        let ac = variants_proto_rule(&h, &rule).expect("variants").unwrap();
        // No terms → identity variant.
        assert_eq!(ac.info.variants.len(), 1);
        assert!(ac.info.variants[0].is_empty());
    }

    #[test]
    fn variants_of_simple_rule_via_maude() {
        let path = match maude_path() {
            Some(p) => p,
            None => { eprintln!("skipping: no maude"); return; }
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        // Rule: [Fr(~k)] --> [Out(~k)]
        let k = LVar::new("k", LSort::Fresh, 0);
        let kt: LNTerm = Term::Lit(Lit::Var(k));
        let prem = Fact::new(FactTag::Fresh, vec![kt.clone()]);
        let conc = Fact::new(FactTag::Out, vec![kt.clone()]);
        let info = ProtoRuleEInfo {
            name: ProtoRuleName::Stand("R".into()),
            attributes: RuleAttributes::empty(),
            restrictions: Vec::new(),
        };
        let rule = Rule::new(info, vec![prem], vec![conc], Vec::new());
        let ac = variants_proto_rule(&h, &rule).expect("variants").unwrap();
        // For a rule with no reducible operators, Maude returns one
        // trivial variant (the identity).
        assert!(!ac.info.variants.is_empty(),
            "expected at least one variant, got none");
    }
}
