//! Port of HS `liftedAddProtoRule` (Theory/Text/Parser.hs:166-193) +
//! `fromRuleRestriction` / `rewrite` (Theory/Model/Restriction.hs:89-161).
//!
//! Expands the `_restrict(...)` embedded-restriction construct that the
//! parser captures into `Rule.embedded_restrictions: Vec<Formula>`
//! (parser ast.rs:104).  For each such formula, HS:
//!   1. expands predicate atoms (`liftedExpandFormula`),
//!   2. abstracts every subterm containing free variables into a fresh
//!      `x`/`x.1`/… var (`rewrite`),
//!   3. builds a fresh restriction `Restr_<rule>_<i>` whose body is
//!      `∀ <frees>. (Restr_<rule>_<i>(<free-var terms>) @ #NOW) ⇒ φ'`,
//!   4. inserts that restriction BEFORE the rule, and
//!   5. appends the action `Restr_<rule>_<i>(<original abstracted terms>)`
//!      to the rule's actions, clearing its embedded restrictions.
//!
//! HS performs this DURING parsing (the parser calls `liftedAddProtoRule`
//! per rule, building the `OpenTheory` with restrictions inserted and
//! actions rewritten).  The RS port mirrors that by running this pass over
//! the parser-AST theory `parsed` right after `parse_theory`, so the
//! transformed theory drives BOTH wellformedness/elaboration AND
//! pretty-printing (the renderer iterates the parser AST).
//!
//! We operate on parser-AST `Formula`/`Term`/`Fact` throughout — the same
//! universe `predicate_expand::expand_formula` works in — so the generated
//! restriction flows through `render_parsed_restriction` and the rewritten
//! action through `render_rule` unchanged.

use std::collections::BTreeMap;

use tamarin_parser::ast as p;

use crate::predicate_expand::{expand_formula, ExpandError};

/// HS `varNow = LVar "NOW" LSortNode 0` (Restriction.hs:87).  The implicit
/// timepoint variable bound by the generated `∀ … #NOW.` restriction.
fn var_now() -> p::VarSpec {
    p::VarSpec { name: "NOW".to_string(), idx: 0, sort: p::SortHint::Node, typ: None }
}

/// HS `restrPrefix = "Restr_"` (Restriction.hs:130).
const RESTR_PREFIX: &str = "Restr_";

/// Run the `_restrict` lifting pass over a parsed theory in place.
///
/// Mirrors HS `liftedAddProtoRule` invoked per rule during parsing.  For
/// every `TheoryItem::Rule` carrying `embedded_restrictions`, generate the
/// `Restr_<rule>_<i>` restrictions (inserted immediately before the rule)
/// and rewrite the rule's actions, clearing `embedded_restrictions`.
///
/// Predicate atoms inside each `_restrict` formula are expanded against the
/// theory's `predicate:` declarations first (HS `liftedExpandFormula`).
/// `let` bindings are applied to the rule body before lifting so the
/// abstracted terms see their expansions (HS applies `let` at parse time,
/// Rule.hs:131, before `liftedAddProtoRule`).
pub fn lift_rule_restrictions(thy: &mut p::Theory) -> Result<(), ExpandError> {
    // Collect predicate definitions once (declared before the rules).
    let predicates: Vec<p::Predicate> = thy.items.iter().filter_map(|i| match i {
        p::TheoryItem::Predicates(ps) => Some(ps.clone()),
        _ => None,
    }).flatten().collect();

    // Build a new item list, expanding rules-with-restrictions into
    // [generated restrictions..., rewritten rule].  Other items pass
    // through untouched.
    let mut new_items: Vec<p::TheoryItem> = Vec::with_capacity(thy.items.len());
    for item in std::mem::take(&mut thy.items) {
        match item {
            p::TheoryItem::Rule(rule) if !rule.embedded_restrictions.is_empty() => {
                let (restrs, new_rule) = lift_one_rule(rule, &predicates)?;
                // HS adds the restrictions to the theory accumulated so far,
                // THEN adds the rule → restrictions precede the rule.
                for r in restrs {
                    new_items.push(p::TheoryItem::Restriction(r));
                }
                new_items.push(p::TheoryItem::Rule(new_rule));
            }
            other => new_items.push(other),
        }
    }
    thy.items = new_items;
    Ok(())
}

/// Lift one rule's embedded restrictions.  Returns the generated
/// restrictions (in `1..n` order) and the rewritten rule.
fn lift_one_rule(
    rule: p::Rule,
    predicates: &[p::Predicate],
) -> Result<(Vec<p::Restriction>, p::Rule), ExpandError> {
    let rname = rule.name.clone();
    // HS applies the `let` block to (ps, as, cs, rs) at parse time
    // (Rule.hs:131) BEFORE `liftedAddProtoRule` runs.  Mirror by desugaring
    // the let block here, so the abstracted restriction terms (and the
    // appended action terms, which join the rule body) carry the let
    // expansion exactly once.  `apply_let_block` returns the rule with an
    // empty `let_block`; downstream `apply_let_block` calls (elaborate /
    // render) then become no-ops, matching HS where no let block survives
    // parse.
    let mut rule = if rule.let_block.is_empty() {
        rule
    } else {
        crate::elaborate::apply_let_block(&rule)
    };

    let formulas = std::mem::take(&mut rule.embedded_restrictions);
    let mut restrictions: Vec<p::Restriction> = Vec::with_capacity(formulas.len());
    let mut new_actions: Vec<p::Fact> = Vec::with_capacity(formulas.len());

    // HS `counter = zip [1..]`: 1-indexed.
    for (i, phi) in formulas.into_iter().enumerate() {
        let idx = i + 1;
        // HS `liftedExpandFormula thy` — expand predicate atoms.
        let expanded = expand_formula(&phi, predicates)?;
        // HS `fromRuleRestriction (rname ++ "_" ++ show i) f`.
        let sub_name = format!("{}_{}", rname, idx);
        let (restr, action) = from_rule_restriction(&sub_name, &expanded);
        restrictions.push(restr);
        new_actions.push(action);
    }

    // HS `addActions = modify rActs (++ actions)`: APPEND the restriction
    // actions after the rule's existing actions.
    rule.actions.extend(new_actions);
    Ok((restrictions, rule))
}

/// HS `fromRuleRestriction rname f` (Restriction.hs:140-161): produce the
/// generated restriction plus the action fact inserted into the rule.
fn from_rule_restriction(rname: &str, f: &p::Formula) -> (p::Restriction, p::Fact) {
    // HS `rewrite f` returns `(rewritten formula, M.Map LVar Term)`.
    let (rewr_f, subst) = rewrite(f);

    // --- the restriction ----------------------------------------------
    // HS `mkRestriction f' = Restriction (restrPrefix++rname)
    //        (foldr (hinted forAll) f'' (frees f'')) Nothing`
    //   where f'' = (Action #NOW fact) ==> f'
    //         fact = mkFact (getBVarTerms f')
    //         getBVarTerms = map (varTerm.Free) . delete varNow . freesList
    let bvar_terms: Vec<p::Term> = frees_list(&rewr_f)
        .into_iter()
        .filter(|v| !is_var_now(v))
        .map(p::Term::Var)
        .collect();
    let restr_fact = mk_fact(rname, bvar_terms);
    // f'' = (Restr_<rname>(...) @ #NOW) ⇒ f'
    let now_term = p::Term::Var(var_now());
    let antecedent = p::Formula::Atom(p::Atom::Action(restr_fact, now_term));
    let f2 = p::Formula::Implies(
        Box::new(antecedent),
        Box::new(rewr_f.clone()),
    );
    // foldr forAll f'' (frees f''): bind ALL free vars of f'' (sorted,
    // dedup), outermost-first matching HS `foldr`.
    let quant_vars = frees_sorted(&f2);
    let restr_formula = if quant_vars.is_empty() {
        f2
    } else {
        p::Formula::Forall(quant_vars, Box::new(f2))
    };
    let restriction = p::Restriction {
        name: format!("{}{}", RESTR_PREFIX, rname),
        formula: restr_formula,
        attributes: Vec::new(),
    };

    // --- the action fact inserted into the rule -----------------------
    // HS `mkFact $ getVarTerms (rewrSubst f) (rewrF f)` where
    //   getVarTerms subst = map (apply subst . varTerm) . delete varNow . freesList
    // i.e. for each free var of the rewritten formula (minus NOW), look up
    // the ORIGINAL term it abstracted; vars with no entry stay themselves.
    let action_args: Vec<p::Term> = frees_list(&rewr_f)
        .into_iter()
        .filter(|v| !is_var_now(v))
        .map(|v| match subst.get(&var_key(&v)) {
            Some(t) => t.clone(),
            None => p::Term::Var(v),
        })
        .collect();
    let action = mk_fact(rname, action_args);

    (restriction, action)
}

/// HS `mkFact = protoFactAnn Linear (restrPrefix ++ rname) S.empty`
/// (Restriction.hs:161): a linear fact named `Restr_<rname>`.
fn mk_fact(rname: &str, args: Vec<p::Term>) -> p::Fact {
    p::Fact {
        persistent: false,
        name: format!("{}{}", RESTR_PREFIX, rname),
        args,
        annotations: Vec::new(),
    }
}

// =============================================================================
// rewrite (HS Restriction.hs:89-127)
// =============================================================================

/// A fresh-variable substitution: maps each minted fresh var (by key) to
/// the ORIGINAL term it abstracted.  Keyed by `(name, idx)` — the fresh
/// vars are all `LSortMsg` so the sort is implicit.
type RewriteSubst = BTreeMap<(String, u64), p::Term>;

/// HS `rewrite f = runState (evalFreshT (traverseFormulaAtom fAt' f) 0) M.empty`
/// (Restriction.hs:95): traverse every term of every atom, abstracting
/// subterms that contain free variables into fresh vars.  Returns the
/// rewritten formula and the `{fresh ↦ original}` map.
fn rewrite(f: &p::Formula) -> (p::Formula, RewriteSubst) {
    let mut st = RewriteState { counter: 0, subst: RewriteSubst::new() };
    let bound: Vec<String> = Vec::new();
    let out = rewrite_formula(f, &bound, &mut st);
    (out, st.subst)
}

struct RewriteState {
    /// HS `evalFreshT … 0` fresh counter: 0 → `x`, 1 → `x.1`, …
    counter: u64,
    subst: RewriteSubst,
}

impl RewriteState {
    /// HS `substitute t' = do v <- freshLVar "x" LSortMsg; … return varTerm (Free v)`.
    /// Mint a fresh `LSortMsg` var, record `{v ↦ t}`, return `Var(v)`.
    fn substitute(&mut self, t: &p::Term) -> p::Term {
        let idx = self.counter;
        self.counter += 1;
        let v = p::VarSpec { name: "x".to_string(), idx, sort: p::SortHint::Msg, typ: None };
        self.subst.insert((v.name.clone(), v.idx), t.clone());
        p::Term::Var(v)
    }
}

/// Traverse a formula's atoms (HS `traverseFormulaAtom`), rewriting their
/// terms.  `bound` carries the names bound by enclosing quantifiers.
fn rewrite_formula(f: &p::Formula, bound: &[String], st: &mut RewriteState) -> p::Formula {
    use p::Formula::*;
    match f {
        True | False => f.clone(),
        Atom(a) => Atom(rewrite_atom(a, bound, st)),
        Not(g) => Not(Box::new(rewrite_formula(g, bound, st))),
        And(a, b) => And(
            Box::new(rewrite_formula(a, bound, st)),
            Box::new(rewrite_formula(b, bound, st)),
        ),
        Or(a, b) => Or(
            Box::new(rewrite_formula(a, bound, st)),
            Box::new(rewrite_formula(b, bound, st)),
        ),
        Implies(a, b) => Implies(
            Box::new(rewrite_formula(a, bound, st)),
            Box::new(rewrite_formula(b, bound, st)),
        ),
        Iff(a, b) => Iff(
            Box::new(rewrite_formula(a, bound, st)),
            Box::new(rewrite_formula(b, bound, st)),
        ),
        Forall(vs, body) => {
            let mut b2 = bound.to_vec();
            for v in vs { b2.push(v.name.clone()); }
            Forall(vs.clone(), Box::new(rewrite_formula(body, &b2, st)))
        }
        Exists(vs, body) => {
            let mut b2 = bound.to_vec();
            for v in vs { b2.push(v.name.clone()); }
            Exists(vs.clone(), Box::new(rewrite_formula(body, &b2, st)))
        }
    }
}

fn rewrite_atom(a: &p::Atom, bound: &[String], st: &mut RewriteState) -> p::Atom {
    use p::Atom::*;
    match a {
        Eq(l, r) => Eq(rewrite_term(l, bound, st), rewrite_term(r, bound, st)),
        Less(l, r) => Less(rewrite_term(l, bound, st), rewrite_term(r, bound, st)),
        LessMset(l, r) => LessMset(rewrite_term(l, bound, st), rewrite_term(r, bound, st)),
        Subterm(l, r) => Subterm(rewrite_term(l, bound, st), rewrite_term(r, bound, st)),
        Action(fa, t) => {
            let fa2 = p::Fact {
                persistent: fa.persistent,
                name: fa.name.clone(),
                args: fa.args.iter().map(|x| rewrite_term(x, bound, st)).collect(),
                annotations: fa.annotations.clone(),
            };
            Action(fa2, rewrite_term(t, bound, st))
        }
        Last(t) => Last(rewrite_term(t, bound, st)),
        // A `Pred` should never survive predicate expansion, but rewrite it
        // structurally just in case (HS would also traverse it).
        Pred(fa) => {
            let fa2 = p::Fact {
                persistent: fa.persistent,
                name: fa.name.clone(),
                args: fa.args.iter().map(|x| rewrite_term(x, bound, st)).collect(),
                annotations: fa.annotations.clone(),
            };
            Pred(fa2)
        }
    }
}

/// HS `fAt` (Restriction.hs:98-111): the per-term abstraction.
///   - `Var v`, v free            → substitute (fresh var)
///   - `Var _`, v bound           → keep
///   - `FApp _ as`, any free & no bound → substitute the WHOLE term
///   - `FApp f as`, any free & any bound → recurse into args
///   - otherwise                  → keep
/// where free/bound are computed with `varNow` treated as NOT free.
fn rewrite_term(t: &p::Term, bound: &[String], st: &mut RewriteState) -> p::Term {
    match t {
        p::Term::Var(v) => {
            if is_free(v, bound) {
                st.substitute(t)
            } else {
                t.clone()
            }
        }
        // Compound terms: App / Pair / AlgApp / Diff / BinOp.  HS treats
        // every non-Lit as `FApp _ as`; mirror by classifying on the args.
        _ => {
            let args = term_children(t);
            if args.is_empty() {
                // No sub-terms (e.g. literals / nullary App) → keep.
                return t.clone();
            }
            let any_free = args.iter().any(|c| contains_free(c, bound));
            let any_bound = args.iter().any(|c| contains_bound(c, bound));
            if any_free && !any_bound {
                st.substitute(t)
            } else if any_free && any_bound {
                rebuild_term(t, |c| rewrite_term(c, bound, st))
            } else {
                t.clone()
            }
        }
    }
}

/// HS `isFree (Bound _) = False; isFree (Free v) = v /= varNow`.
/// In the parser AST a var is "bound" if its name is bound by an enclosing
/// quantifier; the special `#NOW` node var is treated as not-free.
fn is_free(v: &p::VarSpec, bound: &[String]) -> bool {
    if bound.iter().any(|n| n == &v.name) {
        return false;
    }
    !is_var_now(v)
}

/// HS `containsVar p t`: does `t` mention a variable satisfying `p`?
fn contains_var(t: &p::Term, bound: &[String], free_pred: bool) -> bool {
    match t {
        p::Term::Var(v) => {
            let free = is_free(v, bound);
            if free_pred { free } else { !free }
        }
        _ => term_children(t).iter().any(|c| contains_var(c, bound, free_pred)),
    }
}

fn contains_free(t: &p::Term, bound: &[String]) -> bool {
    contains_var(t, bound, true)
}

fn contains_bound(t: &p::Term, bound: &[String]) -> bool {
    contains_var(t, bound, false)
}

/// Direct sub-terms of a compound term (the `as` in HS `FApp _ as`).
fn term_children(t: &p::Term) -> Vec<&p::Term> {
    match t {
        p::Term::App(_, args) | p::Term::Pair(args) => args.iter().collect(),
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
            vec![a, b]
        }
        p::Term::PatMatch(inner) => vec![inner.as_ref()],
        _ => Vec::new(),
    }
}

/// Rebuild a compound term, mapping `f` over its direct children.
fn rebuild_term(t: &p::Term, mut f: impl FnMut(&p::Term) -> p::Term) -> p::Term {
    match t {
        p::Term::App(name, args) =>
            p::Term::App(name.clone(), args.iter().map(&mut f).collect()),
        p::Term::Pair(items) =>
            p::Term::Pair(items.iter().map(&mut f).collect()),
        p::Term::AlgApp(name, a, b) =>
            p::Term::AlgApp(name.clone(), Box::new(f(a)), Box::new(f(b))),
        p::Term::Diff(a, b) =>
            p::Term::Diff(Box::new(f(a)), Box::new(f(b))),
        p::Term::BinOp(op, a, b) =>
            p::Term::BinOp(*op, Box::new(f(a)), Box::new(f(b))),
        p::Term::PatMatch(inner) =>
            p::Term::PatMatch(Box::new(f(inner))),
        other => other.clone(),
    }
}

// =============================================================================
// frees / freesList over the rewritten formula
// =============================================================================

/// Is this var the special `#NOW` timepoint (HS `varNow`)?
fn is_var_now(v: &p::VarSpec) -> bool {
    v.name == "NOW" && matches!(v.sort, p::SortHint::Node) && v.idx == 0
}

/// Substitution key for a (fresh) var: `(name, idx)`.
fn var_key(v: &p::VarSpec) -> (String, u64) {
    (v.name.clone(), v.idx)
}

/// HS `freesList`: all free vars in first-appearance order, WITH
/// duplicates removed only by the `D.toList` dlist (HS keeps duplicates in
/// `freesList`, but `getBVarTerms`/`getVarTerms` then feed the action fact;
/// for the formulas this pass produces every free var occurs once after
/// abstraction, so first-appearance dedup matches HS output).
fn frees_list(f: &p::Formula) -> Vec<p::VarSpec> {
    let mut out: Vec<p::VarSpec> = Vec::new();
    let mut bound: Vec<String> = Vec::new();
    collect_frees_formula(f, &mut bound, &mut out);
    // HS `freesDList` is a difference list of every free occurrence (with
    // repeats); `getBVarTerms`/`getVarTerms` rely on positional `freesList`.
    // We dedup by (name,idx,sort) keeping first appearance — the rewritten
    // formula introduces each fresh var exactly once on the LHS but it may
    // recur (e.g. an abstracted var reused), and HS's action fact would
    // then list it once per the `nub`-free `freesList`… in practice the
    // abstracted vars are distinct, so first-appearance is the HS order.
    dedup_first(out)
}

/// HS `frees = sortednub . freesList`: sorted (by LVar Ord) and dedup.
fn frees_sorted(f: &p::Formula) -> Vec<p::VarSpec> {
    let mut vs = frees_list(f);
    vs.sort_by(cmp_lvar);
    vs.dedup_by(|a, b| cmp_lvar(a, b) == std::cmp::Ordering::Equal);
    vs
}

fn dedup_first(vs: Vec<p::VarSpec>) -> Vec<p::VarSpec> {
    let mut seen: std::collections::BTreeSet<(String, u64, u8)> = std::collections::BTreeSet::new();
    let mut out = Vec::with_capacity(vs.len());
    for v in vs {
        let key = (v.name.clone(), v.idx, sort_rank(v.sort));
        if seen.insert(key) {
            out.push(v);
        }
    }
    out
}

/// HS `LVar` Ord: `compare idx <> compare sort <> compare name`
/// (LTerm.hs:522-524).  LSort order: Pub < Fresh < Msg < Node < Nat
/// (LTerm.hs:161-166).
fn cmp_lvar(a: &p::VarSpec, b: &p::VarSpec) -> std::cmp::Ordering {
    a.idx.cmp(&b.idx)
        .then(sort_rank(a.sort).cmp(&sort_rank(b.sort)))
        .then(a.name.cmp(&b.name))
}

/// Rank a parser `SortHint` to mirror HS `LSort` Ord.  Untagged vars in a
/// restriction formula stand for Msg-sorted message variables.
fn sort_rank(s: p::SortHint) -> u8 {
    use p::SortHint::*;
    use p::SuffixSort;
    match s {
        Pub | Suffix(SuffixSort::Pub) => 0,
        Fresh | Suffix(SuffixSort::Fresh) => 1,
        Msg | Suffix(SuffixSort::Msg) | Untagged => 2,
        Node | Suffix(SuffixSort::Node) => 3,
        Nat | Suffix(SuffixSort::Nat) => 4,
    }
}

fn collect_frees_formula(f: &p::Formula, bound: &mut Vec<String>, out: &mut Vec<p::VarSpec>) {
    use p::Formula::*;
    match f {
        True | False => {}
        Atom(a) => collect_frees_atom(a, bound, out),
        Not(g) => collect_frees_formula(g, bound, out),
        And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b) => {
            collect_frees_formula(a, bound, out);
            collect_frees_formula(b, bound, out);
        }
        Forall(vs, body) | Exists(vs, body) => {
            let saved = bound.len();
            for v in vs { bound.push(v.name.clone()); }
            collect_frees_formula(body, bound, out);
            bound.truncate(saved);
        }
    }
}

fn collect_frees_atom(a: &p::Atom, bound: &[String], out: &mut Vec<p::VarSpec>) {
    use p::Atom::*;
    match a {
        Eq(l, r) | Less(l, r) | LessMset(l, r) | Subterm(l, r) => {
            collect_frees_term(l, bound, out);
            collect_frees_term(r, bound, out);
        }
        Action(fa, t) => {
            for arg in &fa.args { collect_frees_term(arg, bound, out); }
            collect_frees_term(t, bound, out);
        }
        Last(t) => collect_frees_term(t, bound, out),
        Pred(fa) => for arg in &fa.args { collect_frees_term(arg, bound, out); },
    }
}

fn collect_frees_term(t: &p::Term, bound: &[String], out: &mut Vec<p::VarSpec>) {
    match t {
        p::Term::Var(v) => {
            if !bound.iter().any(|n| n == &v.name) {
                out.push(v.clone());
            }
        }
        _ => for c in term_children(t) { collect_frees_term(c, bound, out); },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parser::parse_formula_str;

    fn preds(decl: &str) -> Vec<p::Predicate> {
        let src = format!("theory T begin\npredicates: {}\nend", decl);
        let thy = tamarin_parser::parse_theory(&src, &[]).unwrap();
        thy.items.into_iter().filter_map(|it| match it {
            p::TheoryItem::Predicates(ps) => Some(ps),
            _ => None,
        }).flatten().collect()
    }

    #[test]
    fn minimal_trace() {
        // True(x) <=> (x = true()); restriction True(eq(x,x)).
        let ps = preds("True(x) <=> (x = true())");
        let phi = parse_formula_str("True(eq(x, x))").unwrap();
        let expanded = expand_formula(&phi, &ps).unwrap();
        let (restr, action) = from_rule_restriction("A_1", &expanded);
        // Restriction name.
        assert_eq!(restr.name, "Restr_A_1");
        // Action fact name + ORIGINAL args.
        assert_eq!(action.name, "Restr_A_1");
        assert_eq!(action.args.len(), 1);
        // The single abstracted arg is the ORIGINAL eq(x,x).
        match &action.args[0] {
            p::Term::App(n, args) => {
                assert_eq!(n, "eq");
                assert_eq!(args.len(), 2);
            }
            other => panic!("expected eq(x,x), got {:?}", other),
        }
        // Restriction formula: ∀ x #NOW. (Restr_A_1(x) @ #NOW) ⇒ (x = true)
        match &restr.formula {
            p::Formula::Forall(vs, body) => {
                // Two binders: the abstracted x (Msg) and #NOW (Node), in
                // sorted order x then NOW.
                assert_eq!(vs.len(), 2);
                assert_eq!(vs[0].name, "x");
                assert_eq!(vs[1].name, "NOW");
                // Body is an implication.
                assert!(matches!(**body, p::Formula::Implies(_, _)));
            }
            other => panic!("expected forall, got {:?}", other),
        }
    }

    #[test]
    fn lift_inserts_restriction_before_rule() {
        let src = "theory T begin\n\
            functions: true/0, eq/2\n\
            equations: eq(x,x)=x\n\
            predicate: True(x) <=> (x = true())\n\
            rule A:\n  [In(x)] --[ _restrict(True(eq(x,x))) ]-> []\n\
            end";
        let mut thy = tamarin_parser::parse_theory(src, &[]).unwrap();
        lift_rule_restrictions(&mut thy).unwrap();
        // Find rule A and the generated restriction.
        let restr_pos = thy.items.iter().position(|i| matches!(i,
            p::TheoryItem::Restriction(r) if r.name == "Restr_A_1"));
        let rule_pos = thy.items.iter().position(|i| matches!(i,
            p::TheoryItem::Rule(r) if r.name == "A"));
        assert!(restr_pos.is_some(), "restriction not generated");
        assert!(rule_pos.is_some(), "rule missing");
        assert!(restr_pos.unwrap() < rule_pos.unwrap(),
            "restriction must precede rule");
        // Rule action rewritten, embedded restrictions cleared.
        if let p::TheoryItem::Rule(r) = &thy.items[rule_pos.unwrap()] {
            assert!(r.embedded_restrictions.is_empty());
            assert_eq!(r.actions.len(), 1);
            assert_eq!(r.actions[0].name, "Restr_A_1");
        }
    }
}
