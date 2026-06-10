//! Port of `Theory.Syntactic.Predicate.expandFormula` —
//! substitutes predicate-atom occurrences in a formula with the body
//! of the matching predicate definition. Uses parser-AST formulas /
//! predicates throughout.
//!
//! A predicate `P(x_1, ..., x_n) <=> phi` is "applied" to a use-site
//! atom `P(t_1, ..., t_n)` by substituting each variable `x_i` in
//! `phi` with the corresponding term `t_i`.

use std::collections::BTreeMap;

use tamarin_parser::ast as p;

#[derive(Debug, Clone)]
pub struct ExpandError {
    pub message: String,
}

impl std::fmt::Display for ExpandError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
impl std::error::Error for ExpandError {}

/// Recursively expand every predicate-atom in `formula`. Returns a
/// new formula whose atoms are only `Action`, `Eq`, `Less`,
/// `LessMset`, `Subterm`, `Last` — i.e. no `Pred(_)` left.
pub fn expand_formula(
    formula: &p::Formula,
    predicates: &[p::Predicate],
) -> Result<p::Formula, ExpandError> {
    expand(formula, predicates, &Subst::default())
}

/// Convenience: expand every formula in a theory's lemmas / restrictions
/// against the theory's own predicate definitions. Returns a new theory
/// (a copy with the formulas rewritten). Items that don't carry a
/// formula are returned unchanged.
pub fn expand_theory_formulas(thy: &mut p::Theory) -> Result<(), ExpandError> {
    let predicates: Vec<p::Predicate> = thy.items.iter().filter_map(|i| match i {
        p::TheoryItem::Predicates(ps) => Some(ps.clone()),
        _ => None,
    }).flatten().collect();

    if predicates.is_empty() { return Ok(()); }

    for item in thy.items.iter_mut() {
        match item {
            p::TheoryItem::Lemma(l) => {
                l.formula = expand_formula(&l.formula, &predicates)?;
            }
            p::TheoryItem::Restriction(r) | p::TheoryItem::LegacyAxiom(r) => {
                r.formula = expand_formula(&r.formula, &predicates)?;
            }
            p::TheoryItem::CaseTest(c) => {
                c.formula = expand_formula(&c.formula, &predicates)?;
            }
            p::TheoryItem::AccLemma(a) => {
                a.formula = expand_formula(&a.formula, &predicates)?;
            }
            _ => {}
        }
    }
    Ok(())
}

// =============================================================================
// Substitution
// =============================================================================

/// Map from variable name → replacement term. Used when applying a
/// predicate's body to a use-site.
#[derive(Debug, Clone, Default)]
struct Subst {
    /// Indexed by variable name (the parser doesn't track de-Bruijn indices
    /// for formula scopes — we use names directly).
    map: BTreeMap<String, p::Term>,
}

impl Subst {
    fn lookup(&self, name: &str) -> Option<&p::Term> {
        self.map.get(name)
    }
}

// =============================================================================
// Recursion
// =============================================================================

fn expand(
    f: &p::Formula,
    preds: &[p::Predicate],
    subst: &Subst,
) -> Result<p::Formula, ExpandError> {
    match f {
        p::Formula::True | p::Formula::False => Ok(f.clone()),
        p::Formula::Atom(a) => expand_atom(a, preds, subst),
        p::Formula::Not(g) => Ok(p::Formula::Not(Box::new(expand(g, preds, subst)?))),
        p::Formula::And(a, b) => Ok(p::Formula::And(
            Box::new(expand(a, preds, subst)?),
            Box::new(expand(b, preds, subst)?),
        )),
        p::Formula::Or(a, b) => Ok(p::Formula::Or(
            Box::new(expand(a, preds, subst)?),
            Box::new(expand(b, preds, subst)?),
        )),
        p::Formula::Implies(a, b) => Ok(p::Formula::Implies(
            Box::new(expand(a, preds, subst)?),
            Box::new(expand(b, preds, subst)?),
        )),
        p::Formula::Iff(a, b) => Ok(p::Formula::Iff(
            Box::new(expand(a, preds, subst)?),
            Box::new(expand(b, preds, subst)?),
        )),
        p::Formula::Forall(vs, body) => {
            // Drop any subst entries that this binder shadows.
            let new_subst = strip_shadowed(subst, vs);
            Ok(p::Formula::Forall(vs.clone(),
                Box::new(expand(body, preds, &new_subst)?)))
        }
        p::Formula::Exists(vs, body) => {
            let new_subst = strip_shadowed(subst, vs);
            Ok(p::Formula::Exists(vs.clone(),
                Box::new(expand(body, preds, &new_subst)?)))
        }
    }
}

fn strip_shadowed(subst: &Subst, vs: &[p::VarSpec]) -> Subst {
    let mut out = subst.clone();
    for v in vs { out.map.remove(&v.name); }
    out
}

fn expand_atom(
    a: &p::Atom,
    preds: &[p::Predicate],
    subst: &Subst,
) -> Result<p::Formula, ExpandError> {
    match a {
        p::Atom::Pred(fact) => {
            // Substitute the use-site arguments first.
            let sub_args: Vec<p::Term> = fact.args.iter()
                .map(|t| subst_term(t, subst))
                .collect();
            // Look up predicate definition.
            match find_predicate(preds, &fact.name) {
                Some(pred) => {
                    if pred.fact.args.len() != sub_args.len() {
                        return Err(ExpandError {
                            message: format!("predicate `{}` arity mismatch ({} vs {})",
                                fact.name, pred.fact.args.len(), sub_args.len()),
                        });
                    }
                    // Build a fresh subst from the predicate's parameters
                    // (which the parser stores as terms — typically Var)
                    // to the use-site arguments.
                    let mut new_subst = Subst::default();
                    for (param, value) in pred.fact.args.iter().zip(sub_args.iter()) {
                        if let p::Term::Var(v) = param {
                            new_subst.map.insert(v.name.clone(), value.clone());
                        } else {
                            // Non-variable in predicate parameter list — can't
                            // do simple substitution. Skip.
                            return Err(ExpandError {
                                message: format!("predicate `{}` has non-variable parameter; \
                                    predicate definitions must use plain variables",
                                    fact.name),
                            });
                        }
                    }
                    expand(&pred.formula, preds, &new_subst)
                }
                None => {
                    // No matching predicate. If it's the builtin `Smaller`,
                    // expand it inline (a hard-coded multiset less-than).
                    if fact.name.eq_ignore_ascii_case("smaller") && sub_args.len() == 2 {
                        // Smaller(x, y) <=> ∃ z. y = x + z
                        let z = p::VarSpec {
                            name: "z".to_string(),
                            idx: 0,
                            sort: p::SortHint::Untagged,
                            typ: None,
                        };
                        let z_term = p::Term::Var(z.clone());
                        let sum = p::Term::BinOp(
                            p::BinOp::Union,
                            Box::new(sub_args[0].clone()),
                            Box::new(z_term),
                        );
                        return Ok(p::Formula::Exists(vec![z],
                            Box::new(p::Formula::Atom(p::Atom::Eq(
                                sub_args[1].clone(), sum)))));
                    }
                    Err(ExpandError {
                        message: format!("undefined predicate `{}`", fact.name),
                    })
                }
            }
        }
        // For non-Pred atoms, just substitute through their terms.
        p::Atom::Eq(s, t) => Ok(p::Formula::Atom(p::Atom::Eq(
            subst_term(s, subst), subst_term(t, subst)))),
        p::Atom::Less(s, t) => Ok(p::Formula::Atom(p::Atom::Less(
            subst_term(s, subst), subst_term(t, subst)))),
        p::Atom::LessMset(s, t) => Ok(p::Formula::Atom(p::Atom::LessMset(
            subst_term(s, subst), subst_term(t, subst)))),
        p::Atom::Subterm(s, t) => Ok(p::Formula::Atom(p::Atom::Subterm(
            subst_term(s, subst), subst_term(t, subst)))),
        p::Atom::Action(fact, t) => {
            let new_fact = p::Fact {
                persistent: fact.persistent,
                name: fact.name.clone(),
                args: fact.args.iter().map(|a| subst_term(a, subst)).collect(),
                annotations: fact.annotations.clone(),
            };
            Ok(p::Formula::Atom(p::Atom::Action(new_fact, subst_term(t, subst))))
        }
        p::Atom::Last(t) => Ok(p::Formula::Atom(p::Atom::Last(subst_term(t, subst)))),
    }
}

fn find_predicate<'a>(preds: &'a [p::Predicate], name: &str) -> Option<&'a p::Predicate> {
    preds.iter().find(|pr| pr.fact.name == name)
}

fn subst_term(t: &p::Term, subst: &Subst) -> p::Term {
    match t {
        p::Term::Var(v) => match subst.lookup(&v.name) {
            Some(replacement) => replacement.clone(),
            None => t.clone(),
        },
        p::Term::App(name, args) =>
            p::Term::App(name.clone(), args.iter().map(|a| subst_term(a, subst)).collect()),
        p::Term::AlgApp(name, a, b) => p::Term::AlgApp(
            name.clone(),
            Box::new(subst_term(a, subst)),
            Box::new(subst_term(b, subst)),
        ),
        p::Term::Pair(items) => p::Term::Pair(items.iter().map(|a| subst_term(a, subst)).collect()),
        p::Term::Diff(a, b) =>
            p::Term::Diff(Box::new(subst_term(a, subst)), Box::new(subst_term(b, subst))),
        p::Term::BinOp(op, a, b) =>
            p::Term::BinOp(*op, Box::new(subst_term(a, subst)), Box::new(subst_term(b, subst))),
        p::Term::PatMatch(inner) =>
            p::Term::PatMatch(Box::new(subst_term(inner, subst))),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parser::parse_formula_str;

    fn pred(decl: &str) -> Vec<p::Predicate> {
        // Parse a tiny theory containing only `predicates: <decl>`.
        let src = format!("theory T begin\npredicates: {}\nend", decl);
        let thy = tamarin_parser::parse_theory(&src, &[]).unwrap();
        thy.items.into_iter().filter_map(|it| match it {
            p::TheoryItem::Predicates(ps) => Some(ps),
            _ => None,
        }).flatten().collect()
    }

    #[test]
    fn expand_simple_predicate() {
        // P(x) <=> A(x) @ #i  (note: x is bound in the use-site, #i not).
        let preds = pred("P(x) <=> Ex #i. A(x) @ #i");
        let f = parse_formula_str("All x. P(x)").unwrap();
        let expanded = expand_formula(&f, &preds).unwrap();
        // Should NO LONGER contain a Pred atom.
        assert!(!has_pred_atom(&expanded), "got {:?}", expanded);
    }

    #[test]
    fn expand_undefined_predicate_errors() {
        let preds: Vec<p::Predicate> = Vec::new();
        let f = parse_formula_str("All x. UndefinedPred(x)").unwrap();
        let res = expand_formula(&f, &preds);
        // UndefinedPred is parsed as an Action atom (no @) by the parser
        // — actually as a Pred. So expansion fails because there's no
        // such predicate.
        assert!(res.is_err(), "got {:?}", res);
    }

    fn has_pred_atom(f: &p::Formula) -> bool {
        match f {
            p::Formula::Atom(p::Atom::Pred(_)) => true,
            p::Formula::True | p::Formula::False => false,
            p::Formula::Atom(_) => false,
            p::Formula::Not(g) => has_pred_atom(g),
            p::Formula::And(a, b) | p::Formula::Or(a, b)
            | p::Formula::Implies(a, b) | p::Formula::Iff(a, b) => {
                has_pred_atom(a) || has_pred_atom(b)
            }
            p::Formula::Forall(_, b) | p::Formula::Exists(_, b) => has_pred_atom(b),
        }
    }
}
