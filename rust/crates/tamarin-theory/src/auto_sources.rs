//! Port of Haskell's `--auto-sources` lemma generation
//! (`addAutoSourcesLemma`, `lib/theory/src/OpenTheory.hs:138-538`).
//!
//! When `--auto-sources` is set and the raw sources still contain open
//! chains (partial deconstructions), Tamarin generates a single `sources`
//! lemma that constrains every open-chain input variable: each input
//! subterm is tied to the earlier outputs it can unify with (via Maude) or
//! to the adversary's knowledge (`!KU`). Rules gain `AUTO_IN_*`/`AUTO_OUT_*`
//! action labels so the lemma can refer to those input/output events.
//!
//! This module builds the lemma **formula** as a parser-AST [`p::Formula`]
//! (the form RS stores and renders lemmas in), constructed to render
//! byte-identically to HS's `prettyLNFormula` of the `LNFormula` it builds.
//! The variable binders use HS's names (`x`, `m`/`m1..mn`, `i`, `j`).

use tamarin_parser::ast as p;

/// Bound-variable names, matching HS's quantifier binders in
/// `addAutoSourcesLemma` (`OpenTheory.hs:399-535`).
fn var(name: &str, sort: p::SortHint) -> p::VarSpec {
    p::VarSpec { name: name.to_string(), idx: 0, sort, typ: None }
}
fn var_term(name: &str, sort: p::SortHint) -> p::Term {
    p::Term::Var(var(name, sort))
}

/// `inputFactTerm pos ru terms var` (OpenTheory.hs:313): a linear proto fact
/// `AUTO_IN_TERM_<pos>_<rule>( terms.. , var )`.
fn input_fact_term(name: &str, terms: Vec<p::Term>, v: p::Term) -> p::Fact {
    let mut args = terms;
    args.push(v);
    p::Fact { persistent: false, name: name.to_string(), args, annotations: Vec::new() }
}

/// `outputFactTerm pos ru terms` (OpenTheory.hs:333).
fn output_fact_term(name: &str, terms: Vec<p::Term>) -> p::Fact {
    p::Fact { persistent: false, name: name.to_string(), args: terms, annotations: Vec::new() }
}

fn action(fa: p::Fact, tp: p::Term) -> p::Formula {
    p::Formula::Atom(p::Atom::Action(fa, tp))
}
fn less(a: p::Term, b: p::Term) -> p::Formula {
    p::Formula::Atom(p::Atom::Less(a, b))
}
fn and(a: p::Formula, b: p::Formula) -> p::Formula {
    p::Formula::And(Box::new(a), Box::new(b))
}
fn or(a: p::Formula, b: p::Formula) -> p::Formula {
    p::Formula::Or(Box::new(a), Box::new(b))
}
fn implies(a: p::Formula, b: p::Formula) -> p::Formula {
    p::Formula::Implies(Box::new(a), Box::new(b))
}
fn exists(vs: Vec<p::VarSpec>, body: p::Formula) -> p::Formula {
    p::Formula::Exists(vs, Box::new(body))
}
fn forall(vs: Vec<p::VarSpec>, body: p::Formula) -> p::Formula {
    p::Formula::Forall(vs, Box::new(body))
}

const MSG: p::SortHint = p::SortHint::Msg;
const NODE: p::SortHint = p::SortHint::Node;

/// `orKU` (OpenTheory.hs:484): `∃ j. !KU(x) @ j ∧ j < i`. Here `i` is the
/// input timepoint and `x` the input-term variable.
fn or_ku() -> p::Formula {
    let ku = p::Fact { persistent: true, name: "KU".to_string(), args: vec![var_term("x", MSG)], annotations: Vec::new() };
    exists(
        vec![var("j", NODE)],
        and(action(ku, var_term("j", NODE)), less(var_term("j", NODE), var_term("i", NODE))),
    )
}

/// `toFactsTerm ru p f''` (OpenTheory.hs:502): `f'' ∨ (∃ j. AUTO_OUT_TERM(m) @ j ∧ j < i)`.
fn to_facts_term(out_name: &str, inner: p::Formula) -> p::Formula {
    let out = output_fact_term(out_name, vec![var_term("m", MSG)]);
    or(
        inner,
        exists(
            vec![var("j", NODE)],
            and(action(out, var_term("j", NODE)), less(var_term("j", NODE), var_term("i", NODE))),
        ),
    )
}

/// `addForm` protected-subterm case WITH matching outputs (OpenTheory.hs:419):
/// `∀ x m i. AUTO_IN_TERM(m,x) @ i ⇒ (orKU ∨ (∃ j. AUTO_OUT_TERM(m) @ j ∧ j < i))`.
pub fn term_input_form_with_outputs(in_name: &str, out_name: &str) -> p::Formula {
    let in_fact = input_fact_term(in_name, vec![var_term("m", MSG)], var_term("x", MSG));
    forall(
        vec![var("x", MSG), var("m", MSG), var("i", NODE)],
        implies(
            action(in_fact, var_term("i", NODE)),
            to_facts_term(out_name, or_ku()),
        ),
    )
}

/// `addForm` protected-subterm case with NO matching outputs (OpenTheory.hs:395):
/// `∀ x m i. AUTO_IN_TERM(m,x) @ i ⇒ orKU`.
pub fn term_input_form_no_outputs(in_name: &str) -> p::Formula {
    let in_fact = input_fact_term(in_name, vec![var_term("m", MSG)], var_term("x", MSG));
    forall(
        vec![var("x", MSG), var("m", MSG), var("i", NODE)],
        implies(action(in_fact, var_term("i", NODE)), or_ku()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty_formula::lemma_header_line;

    // Ground truth: the `AUTO_typing` lemma body emitted by the Haskell
    // prover for examples/features/auto-sources/running-example/running.spthy
    // (HS `--auto-sources`). The formula is `(⊤) ∧ (the term-input form)`.
    #[test]
    fn running_example_auto_typing_renders_byte_identically() {
        let in_name = "AUTO_IN_TERM_1_0_0_1_1__Rule_R";
        let out_name = "AUTO_OUT_TERM_1_0_0_1_1__Rule_R";
        let f = and(
            p::Formula::True,
            term_input_form_with_outputs(in_name, out_name),
        );
        let rendered = lemma_header_line("all-traces", &f);
        let expected = "  all-traces\n  \"(⊤) ∧\n   (∀ x m #i.\n     (AUTO_IN_TERM_1_0_0_1_1__Rule_R( m, x ) @ #i) ⇒\n     ((∃ #j. (!KU( x ) @ #j) ∧ (#j < #i)) ∨\n      (∃ #j. (AUTO_OUT_TERM_1_0_0_1_1__Rule_R( m ) @ #j) ∧ (#j < #i))))\"";
        assert_eq!(rendered, expected);
    }
}
