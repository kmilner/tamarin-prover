//! Wiring: run the SAPIC translation and inject the generated rules +
//! restriction + heuristic into BOTH the parsed theory (so the pretty-printer
//! renders them via the existing rule/restriction path — P0f) and the
//! elaborated theory (so the solver + AC-variant pre-computation see them).
//!
//! Mirrors the tail of HS `translate` (Sapic.hs:69-90):
//!   - `foldM liftedAddProtoRule th  (map (`OpenProtoRule` []) eProtoRule)`
//!   - `foldM liftedAddRestriction th1 rest`
//!   - `addHeuristic [SapicRanking]` unless the user set one
//!   - `_thyIsSapic = True`
//!
//! Scope: the CORE LINEAR subset (see `translate`/`base_translation`).

use tamarin_parser::ast as p;

use tamarin_theory::elaborate::ElabError;
use tamarin_theory::pretty_theory::lnfact_to_parser;
use tamarin_theory::pretty_sapic::pretty_sapic_top_level;
use tamarin_theory::rule::{ProtoRuleE, ProtoRuleName};
use tamarin_theory::theory::{OpenProtoRule, OpenRestriction, Theory, TheoryItem};

use crate::convert::convert_process;
use crate::translate::translate;
use crate::typing::type_and_rename_process;

/// Apply the SAPIC `process:` translation to a theory that contains exactly one
/// top-level process.  A no-op for non-process theories (`elaborated.is_sapic`
/// is false), so non-SAPIC corpus files are byte-unchanged.
///
/// `user_set_heuristic` is true when the source / CLI already fixed a heuristic
/// (in which case HS's `addHeuristic` returns `Nothing` and we do NOT add `p`).
pub fn apply_sapic(
    parsed: &mut p::Theory,
    elaborated: &mut Theory,
    user_set_heuristic: bool,
) -> Result<(), ElabError> {
    if !elaborated.is_sapic {
        return Ok(());
    }

    // Locate the single top-level process in the parsed theory.
    let top = parsed.items.iter().find_map(|i| match i {
        p::TheoryItem::TopLevelProcess(proc) => Some(proc.clone()),
        _ => None,
    });
    let Some(top) = top else {
        // `is_sapic` was set but no TopLevelProcess found — defensive no-op.
        return Ok(());
    };

    // P0a: parser AST → theory AST.
    let plain = convert_process(&top)
        .map_err(|e| ElabError { message: format!("SAPIC translation: {}", e.message) })?;

    // P0e: typeTheory (renameUnique + type inference), using the elaborated
    // signature's MaudeSig (HS `initTEFromSig`).
    let maude_sig = &elaborated.signature.maude_sig;
    let typed = type_and_rename_process(maude_sig, &plain)
        .map_err(|e| ElabError { message: format!("SAPIC typing: {e}") })?;

    // translate → rules + restrictions.  `needs_in_ev_res` = false for the
    // linear subset (no lemma needs the `in_event` restriction in typing2).
    let translation = translate(&typed, false)
        .map_err(|e| ElabError { message: format!("SAPIC translation: {e}") })?;

    // Inject each generated rule into BOTH theories.  In the parsed theory we
    // synthesise a `p::Rule` whose body mirrors the elaborated E-rule and whose
    // attributes carry the rendered color / process / role (the pretty-printer
    // reads these); in the elaborated theory we push the `OpenProtoRule` (the
    // AC-variant pre-computation + solver read these).
    for rule in &translation.rules {
        let parsed_rule = synth_parsed_rule(rule);
        parsed.items.push(p::TheoryItem::Rule(parsed_rule));
        elaborated
            .items
            .push(TheoryItem::Rule(OpenProtoRule::new(rule.clone())));
    }

    // Inject the restriction into both theories.
    for restr in &translation.restrictions {
        parsed.items.push(p::TheoryItem::Restriction(restr.clone()));
        elaborated.items.push(TheoryItem::Restriction(OpenRestriction::new(
            restr.name.clone(),
            restr.formula.clone(),
        )));
    }

    // `addHeuristic [SapicRanking]` unless a heuristic is already set
    // (Sapic.hs:82).  `SapicRanking` renders as `p`.
    if !user_set_heuristic && elaborated.heuristic.is_empty() {
        elaborated.heuristic.push("p".to_string());
    }

    Ok(())
}

/// Build the synthetic parsed-AST rule for a SAPIC-generated `ProtoRuleE`.
/// The body (premises/actions/conclusions) is the elaborated E-rule converted
/// back to parser facts; the attributes carry color / process / issapicrule /
/// role exactly as HS's `toRule` produced them.
fn synth_parsed_rule(rule: &ProtoRuleE) -> p::Rule {
    let name = match &rule.info.name {
        ProtoRuleName::Stand(n) => n.clone(),
        ProtoRuleName::Fresh => "Fresh".to_string(),
    };
    let attrs = synth_attrs(&rule.info.attributes);
    p::Rule {
        name,
        modulo: None,
        attributes: attrs,
        let_block: Vec::new(),
        premises: rule.premises.iter().map(lnfact_to_parser).collect(),
        actions: rule.actions.iter().map(lnfact_to_parser).collect(),
        conclusions: rule.conclusions.iter().map(lnfact_to_parser).collect(),
        embedded_restrictions: Vec::new(),
        variants: Vec::new(),
        left_right: None,
    }
}

/// Render the elaborated `RuleAttributes` into the parser-AST attribute list,
/// in HS's order: color, process, (no_derivcheck), issapicrule, role.  The
/// pretty-printer's `rule_attribute_parts` re-orders to the canonical render
/// order, so list order here is not load-bearing — but we keep it tidy.
fn synth_attrs(attr: &tamarin_theory::rule::RuleAttributes) -> Vec<p::RuleAttr> {
    let mut out = Vec::new();
    if let Some(c) = &attr.color {
        // `color=#rrggbb` — pretty_theory lowercases + strips the leading `#`,
        // so pass the hex without the `#` here.
        let hex = tamarin_utils::color::rgb_to_hex(*c);
        out.push(p::RuleAttr::Color(hex.trim_start_matches('#').to_string()));
    }
    if let Some(proc) = &attr.process {
        out.push(p::RuleAttr::Process(pretty_sapic_top_level(proc)));
    }
    if attr.ignore_deriv_checks {
        out.push(p::RuleAttr::NoDerivCheck);
    }
    if attr.is_sapic_rule {
        out.push(p::RuleAttr::IsSapicRule);
    }
    if let Some(r) = &attr.role {
        out.push(p::RuleAttr::Role(r.clone()));
    }
    out
}
