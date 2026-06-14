//! Parser-AST level macro expansion.
//!
//! Port of `Term.Macro.applyMacros` (HS: lib/term/src/Term/Macro.hs:40-50)
//! plus the call-sites that drive it:
//!
//!   - `applyMacroInRule`     — lib/theory/src/Theory/Model/Rule.hs:1032-1037
//!   - `applyMacroInFact`     — lib/theory/src/Theory/Model/Fact.hs:301-303
//!   - `applyMacroInFormula`  — lib/theory/src/Theory/Model/Formula.hs:311-313
//!   - `applyMacroInLemma`    — lib/theory/src/Lemma.hs:83-88
//!   - `applyMacroInRestriction` — lib/theory/src/Theory/Model/Restriction.hs:163-165
//!   - `closeProtoRule` calls applyMacroInRule BEFORE variantsProtoRule
//!     — lib/theory/src/Rule.hs:96-98
//!   - `parseLemmaWithMacros`  — lib/theory/src/Theory/Text/Parser.hs:97-105
//!
//! HS works at the typed `LNTerm` / `LNFact` / `LNFormula` level, with
//! macro matching keyed on the `FunSym` (a `NoEq (name, (arity, Private,
//! Destructor))` tuple — Macro.hs:30).  RS parses lemma/restriction
//! formulas as `parser::ast::Formula` and only converts to `LNFormula`
//! later (via `formula_to_guarded`), so the natural place to expand is
//! the parser AST.  This is observationally faithful: every macro call
//! site is rewritten to its body before either side's typed conversion
//! runs.  The macro fun-syms themselves are still registered in MaudeSig
//! (HS Parser/Macro.hs:48 `addMacroSym`) so any unexpanded reference —
//! and Maude — still see them.
//!
//! Recursion semantics mirror HS exactly:
//!   - args are recursively expanded FIRST (Macro.hs:46),
//!   - then substitution into the body,
//!   - then the EXPANDED body is recursively re-expanded
//!     (Macro.hs:48 `applyMacros macros (apply subst mout)`).
//!
//! This handles chained / nested macros (e.g. `hashdec` calling `decrypt`
//! in `examples/features/macros/MacroExample.spthy`).

use std::collections::BTreeMap;

use tamarin_parser::ast as p;

/// Apply all macros to a term, recursing into args first and re-expanding
/// the body after substitution.  Mirrors HS `applyMacros` exactly
/// (Term/Macro.hs:40-50).
pub fn apply_macros_term(macros: &[p::Macro], term: &p::Term) -> p::Term {
    match term {
        p::Term::App(name, args) => {
            // Recurse on args first (HS `processedArgs = map (applyMacros macros) args`).
            let processed_args: Vec<p::Term> =
                args.iter().map(|a| apply_macros_term(macros, a)).collect();
            // Match on (name, arity) — HS matches on FunSym which includes
            // arity (Macro.hs:30 `macroToFunSym (op,args,_) = NoEq (op,
            // (length args, Private, Destructor))` ; matching macros are
            // found via Macro.hs:53-54 `find (\m -> macroToFunSym m == f)`).
            if let Some(m) = find_matching_macro(name, processed_args.len(), macros) {
                // Build the param→arg substitution (by name).
                let mut subst: BTreeMap<String, p::Term> = BTreeMap::new();
                for (param, value) in m.args.iter().zip(processed_args.iter()) {
                    subst.insert(param.name.clone(), value.clone());
                }
                let expanded = subst_term(&m.body, &subst);
                // Re-expand the EXPANDED body to handle nested macros.
                apply_macros_term(macros, &expanded)
            } else {
                p::Term::App(name.clone(), processed_args)
            }
        }
        p::Term::AlgApp(name, a, b) => p::Term::AlgApp(
            name.clone(),
            Box::new(apply_macros_term(macros, a)),
            Box::new(apply_macros_term(macros, b)),
        ),
        p::Term::Pair(items) => p::Term::Pair(
            items.iter().map(|t| apply_macros_term(macros, t)).collect(),
        ),
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(apply_macros_term(macros, a)),
            Box::new(apply_macros_term(macros, b)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(apply_macros_term(macros, a)),
            Box::new(apply_macros_term(macros, b)),
        ),
        p::Term::PatMatch(inner) => p::Term::PatMatch(
            Box::new(apply_macros_term(macros, inner)),
        ),
        // Literals and bare variables: no recursion (HS Macro.hs:51 `Lit l -> lit l`).
        p::Term::Var(_) | p::Term::PubLit(_) | p::Term::FreshLit(_)
        | p::Term::NatLit(_) | p::Term::Number(_) | p::Term::NumberOne
        | p::Term::NatOne | p::Term::DhNeutral => term.clone(),
    }
}

/// HS `findMatchingMacro f macros = find (\m -> macroToFunSym m == f)`
/// (Macro.hs:53-54).  At parser-AST level a call-site has no FunSym
/// flags so we match by (name, arity) — equivalent for non-clashing
/// macro names since `addMacroSym` rejects redefinitions and built-in
/// fun-syms have known fixed arity (parser/Macro.hs:45-49 `case lookup
/// op (stFunSyms ++ macroNames) -> fail`).
fn find_matching_macro<'a>(
    name: &str,
    arity: usize,
    macros: &'a [p::Macro],
) -> Option<&'a p::Macro> {
    macros.iter().find(|m| m.name == name && m.args.len() == arity)
}

/// Apply substitution to a parser term.  HS's typed `apply subst term`
/// (Macro.hs:48) becomes a structural name-keyed walk.
fn subst_term(t: &p::Term, subst: &BTreeMap<String, p::Term>) -> p::Term {
    match t {
        p::Term::Var(v) => match subst.get(&v.name) {
            Some(replacement) => replacement.clone(),
            None => t.clone(),
        },
        p::Term::App(name, args) => p::Term::App(
            name.clone(),
            args.iter().map(|a| subst_term(a, subst)).collect(),
        ),
        p::Term::AlgApp(name, a, b) => p::Term::AlgApp(
            name.clone(),
            Box::new(subst_term(a, subst)),
            Box::new(subst_term(b, subst)),
        ),
        p::Term::Pair(items) => p::Term::Pair(
            items.iter().map(|a| subst_term(a, subst)).collect(),
        ),
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(subst_term(a, subst)),
            Box::new(subst_term(b, subst)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(subst_term(a, subst)),
            Box::new(subst_term(b, subst)),
        ),
        p::Term::PatMatch(inner) => p::Term::PatMatch(
            Box::new(subst_term(inner, subst)),
        ),
        other => other.clone(),
    }
}

/// Apply macros to every term in a fact.  Mirrors HS `applyMacroInFact`
/// (Fact.hs:301-303 `applyMacroInFact mcs (Fact tag annot terms) =
/// Fact tag annot (map (applyMacros mcs) terms)`).
pub fn apply_macros_fact(macros: &[p::Macro], f: &p::Fact) -> p::Fact {
    p::Fact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(|a| apply_macros_term(macros, a)).collect(),
        annotations: f.annotations.clone(),
    }
}

/// Apply macros to every term in a formula.  Mirrors HS
/// `applyMacroInFormula` (Formula.hs:311-313) — `mapAtoms (... applyMacros
/// (lnMacrosToBNMacros macros))`.  In RS, parser-AST quantifiers carry
/// `VarSpec`s with names; macro params have their declared names; the
/// substitution-by-name suffices because the body is closed over the
/// param names and call args at every call site, so no quantifier-bound
/// variable in the surrounding formula can ever be a param (the macro
/// definition is independent of the use site).
pub fn apply_macros_formula(macros: &[p::Macro], f: &p::Formula) -> p::Formula {
    match f {
        p::Formula::True | p::Formula::False => f.clone(),
        p::Formula::Atom(a) => p::Formula::Atom(apply_macros_atom(macros, a)),
        p::Formula::Not(g) => p::Formula::Not(Box::new(apply_macros_formula(macros, g))),
        p::Formula::And(a, b) => p::Formula::And(
            Box::new(apply_macros_formula(macros, a)),
            Box::new(apply_macros_formula(macros, b)),
        ),
        p::Formula::Or(a, b) => p::Formula::Or(
            Box::new(apply_macros_formula(macros, a)),
            Box::new(apply_macros_formula(macros, b)),
        ),
        p::Formula::Implies(a, b) => p::Formula::Implies(
            Box::new(apply_macros_formula(macros, a)),
            Box::new(apply_macros_formula(macros, b)),
        ),
        p::Formula::Iff(a, b) => p::Formula::Iff(
            Box::new(apply_macros_formula(macros, a)),
            Box::new(apply_macros_formula(macros, b)),
        ),
        p::Formula::Forall(vs, body) => p::Formula::Forall(
            vs.clone(),
            Box::new(apply_macros_formula(macros, body)),
        ),
        p::Formula::Exists(vs, body) => p::Formula::Exists(
            vs.clone(),
            Box::new(apply_macros_formula(macros, body)),
        ),
    }
}

fn apply_macros_atom(macros: &[p::Macro], a: &p::Atom) -> p::Atom {
    match a {
        p::Atom::Eq(s, t) => p::Atom::Eq(
            apply_macros_term(macros, s),
            apply_macros_term(macros, t),
        ),
        p::Atom::Less(s, t) => p::Atom::Less(
            apply_macros_term(macros, s),
            apply_macros_term(macros, t),
        ),
        p::Atom::LessMset(s, t) => p::Atom::LessMset(
            apply_macros_term(macros, s),
            apply_macros_term(macros, t),
        ),
        p::Atom::Subterm(s, t) => p::Atom::Subterm(
            apply_macros_term(macros, s),
            apply_macros_term(macros, t),
        ),
        p::Atom::Action(fact, t) => p::Atom::Action(
            apply_macros_fact(macros, fact),
            apply_macros_term(macros, t),
        ),
        p::Atom::Last(t) => p::Atom::Last(apply_macros_term(macros, t)),
        p::Atom::Pred(fact) => p::Atom::Pred(apply_macros_fact(macros, fact)),
    }
}

/// Apply macros to all items in a theory.  Mirrors HS's call-sites:
///   - rule prems/concs/acts (Rule.hs:1032-1037 + ClosedTheory.hs:322-323)
///   - lemma formula (Lemma.hs:83-88, called from Parser.hs:105)
///   - restriction formula (Restriction.hs:163-165)
///   - case-test / acc-lemma formula (mirror lemma)
///   - embedded restriction in rule (treat as formula)
///   - rule let-block RHS (already inlined into the rule by
///     `apply_let_block` at elaborate time)
///
/// Macros are collected from `TheoryItem::Macros` items in the theory.
/// If no macros are declared, the theory is left unchanged (HS:
/// `applyMacroInFormula [] fm = fm`).
pub fn expand_theory_macros(thy: &mut p::Theory) {
    let macros: Vec<p::Macro> = thy.items.iter().filter_map(|i| match i {
        p::TheoryItem::Macros(ms) => Some(ms.clone()),
        _ => None,
    }).flatten().collect();

    if macros.is_empty() { return; }

    for item in thy.items.iter_mut() {
        match item {
            p::TheoryItem::Rule(r) | p::TheoryItem::IntrRule(r) => {
                expand_rule(&macros, r);
            }
            p::TheoryItem::Lemma(l) => {
                l.formula = apply_macros_formula(&macros, &l.formula);
            }
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                r.formula = apply_macros_formula(&macros, &r.formula);
            }
            p::TheoryItem::CaseTest(c) => {
                c.formula = apply_macros_formula(&macros, &c.formula);
            }
            p::TheoryItem::AccLemma(a) => {
                a.formula = apply_macros_formula(&macros, &a.formula);
            }
            // Predicates: bodies are themselves formula templates. Apply
            // macros so a predicate body that calls a macro is expanded
            // before predicate-expand inlines it.
            p::TheoryItem::Predicates(ps) => {
                for pred in ps.iter_mut() {
                    pred.formula = apply_macros_formula(&macros, &pred.formula);
                    pred.fact = apply_macros_fact(&macros, &pred.fact);
                }
            }
            _ => {}
        }
    }
}

fn expand_rule(macros: &[p::Macro], r: &mut p::Rule) {
    for f in &mut r.premises { *f = apply_macros_fact(macros, f); }
    for f in &mut r.actions { *f = apply_macros_fact(macros, f); }
    for f in &mut r.conclusions { *f = apply_macros_fact(macros, f); }
    for phi in &mut r.embedded_restrictions {
        *phi = apply_macros_formula(macros, phi);
    }
    // Let-block: macros can appear on the RHS.  apply_let_block (in
    // elaborate.rs) substitutes these into the body after parsing; we
    // expand on the LHS-and-RHS terms here so a let `x = macro(...)`
    // sees its RHS rewritten before `apply_let_block` substitutes it.
    for b in &mut r.let_block {
        b.value = apply_macros_term(macros, &b.value);
        b.var = apply_macros_term(macros, &b.var);
    }
    // Variants / diff sides: `variants` holds the user-written explicit
    // `variants ...` block (HS OpenProtoRule's ruAC) and `left_right` holds
    // the diff `left ... right ...` block (HS DiffProtoRule's sides). HS does
    // NOT macro-expand these: applyMacroInProtoRule / applyMacroInDiffProtoRule
    // (ClosedTheory.hs) only run applyMacroInRule on the main rule and pass
    // the variants/sides through unchanged. RS recurses into them anyway; this
    // is harmless because these nested rules normally carry no macro call-sites
    // (and re-expanding an already-expanded body is idempotent).
    for v in &mut r.variants {
        expand_rule(macros, v);
    }
    if let Some((l, r2)) = &mut r.left_right {
        expand_rule(macros, l);
        expand_rule(macros, r2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parse_theory;

    fn parse(src: &str) -> p::Theory {
        parse_theory(src, &[]).expect("parse")
    }

    #[test]
    fn simple_term_macro_replaces_call() {
        // macro `id(x) = x`; call `id(a)` → `a`.
        let src = "theory T begin\n\
            macros: id(x) = x\n\
            rule R: [ In(id(a)) ] --> [ ]\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let rule = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        }).unwrap();
        // Premise was In(id(a)); after expansion: In(a).
        let arg = &rule.premises[0].args[0];
        assert!(matches!(arg, p::Term::Var(v) if v.name == "a"), "got {:?}", arg);
    }

    #[test]
    fn nested_macro_is_re_expanded() {
        // hashdec(x, y) = h(decrypt(x, y)); decrypt(x, y) = adec(x, y).
        // Expanding hashdec(a, b) should produce h(adec(a, b)).
        let src = "theory T begin\n\
            builtins: hashing, asymmetric-encryption\n\
            macros: decrypt(x, y) = adec(x, y), hashdec(x, y) = h(decrypt(x, y))\n\
            rule R: [ In(hashdec(a, b)) ] --> [ ]\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let rule = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        }).unwrap();
        let arg = &rule.premises[0].args[0];
        // Expected: App("h", [App("adec", [Var(a), Var(b)])])
        if let p::Term::App(h_name, h_args) = arg {
            assert_eq!(h_name, "h");
            assert_eq!(h_args.len(), 1);
            if let p::Term::App(adec_name, adec_args) = &h_args[0] {
                assert_eq!(adec_name, "adec");
                assert_eq!(adec_args.len(), 2);
            } else {
                panic!("expected adec, got {:?}", h_args[0]);
            }
        } else {
            panic!("expected h(...), got {:?}", arg);
        }
    }

    #[test]
    fn macro_in_lemma_formula_expands() {
        // Lemma uses a macro that wraps Action(A(m(x))).
        let src = "theory T begin\n\
            macros: m(x) = x\n\
            rule R: [ In(x) ] --[ A(m(x)) ]-> [ ]\n\
            lemma L: exists-trace \"Ex x #i. A(m(x)) @ #i\"\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let lemma = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::Lemma(l) => Some(l),
            _ => None,
        }).unwrap();
        // The Action atom's fact's arg should be Var(x) (not App("m", [Var(x)])).
        fn check(f: &p::Formula) {
            match f {
                p::Formula::Exists(_, body) => check(body),
                p::Formula::And(a, b) => { check(a); check(b); }
                p::Formula::Atom(p::Atom::Action(fact, _)) => {
                    assert!(matches!(&fact.args[0], p::Term::Var(v) if v.name == "x"),
                        "got {:?}", fact.args[0]);
                }
                _ => {}
            }
        }
        check(&lemma.formula);
    }

    #[test]
    fn macro_with_pair_body_via_pair_syntax() {
        // m2(x, y) = <x, y>; call m2(a, b) → Pair([a, b]).
        let src = "theory T begin\n\
            macros: m2(x, y) = <x, y>\n\
            rule R: [ In(m2(a, b)) ] --> [ ]\n\
            end\n";
        let mut thy = parse(src);
        expand_theory_macros(&mut thy);
        let rule = thy.items.iter().find_map(|i| match i {
            p::TheoryItem::Rule(r) => Some(r),
            _ => None,
        }).unwrap();
        let arg = &rule.premises[0].args[0];
        if let p::Term::Pair(items) = arg {
            assert_eq!(items.len(), 2);
        } else {
            panic!("expected Pair, got {:?}", arg);
        }
    }

    #[test]
    fn no_macro_means_no_change() {
        let src = "theory T begin\n\
            rule R: [ In(a) ] --> [ ]\n\
            end\n";
        let mut thy = parse(src);
        let before = thy.clone();
        expand_theory_macros(&mut thy);
        assert_eq!(thy, before);
    }
}
