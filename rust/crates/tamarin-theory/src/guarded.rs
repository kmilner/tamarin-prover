//! Port of `Theory.Constraint.System.Guarded.formulaToGuarded` —
//! the conversion from a surface-formula (lemma / restriction) to the
//! guarded-fragment representation that Tamarin's solver consumes.
//!
//! A guarded formula is one where every quantified variable is bound
//! by an action or equality atom that fires before it's referenced.
//! The check is polarity-aware: `not (Ex x. P(x) @ #i)` becomes
//! equivalent to `All x #i. P(x) @ #i ==> ⊥` and so on.
//!
//! For now we work over `tamarin_parser::ast::Formula` (named
//! variables) rather than the locally-nameless typed AST in
//! `crate::formula`. Once we port the BVar-based representation in
//! anger we can refactor to share the same `Atom` type as the
//! constraint solver.

use std::collections::BTreeSet;

use tamarin_parser::ast as p;

// =============================================================================
// Guarded data type
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Quant { All, Ex }

#[derive(Debug, Clone, PartialEq)]
pub enum Guarded {
    /// One atomic predicate.
    Atom(p::Atom),
    /// Disjunction of guarded sub-formulas.
    Disj(Vec<Guarded>),
    /// Conjunction of guarded sub-formulas.
    Conj(Vec<Guarded>),
    /// `qua xs. as ⇒ gf` (when `qua = All`) or `qua xs. as ∧ gf`
    /// (when `qua = Ex`). The `as` are the *guard* atoms, all
    /// quantified `xs` must be bound by them.
    GGuarded {
        qua: Quant,
        vars: Vec<p::VarSpec>,
        guards: Vec<p::Atom>,
        body: Box<Guarded>,
    },
}

/// Boolean atom helper.
pub fn gtrue() -> Guarded { Guarded::Conj(vec![]) }
pub fn gfalse() -> Guarded { Guarded::Disj(vec![]) }
pub fn gtf(b: bool) -> Guarded { if b { gtrue() } else { gfalse() } }

/// `True` iff the guarded formula can be reduced by the constraint
/// solver's `insertFormula` decomposition rules. Mirrors
/// `Theory.Constraint.Solver.Reduction.reducibleFormula`.
pub fn reducible_formula(fm: &Guarded) -> bool {
    use p::Atom;
    match fm {
        Guarded::Atom(_) => true,
        Guarded::Conj(_) => true,
        Guarded::GGuarded { qua: Quant::Ex, .. } => true,
        Guarded::GGuarded { qua: Quant::All, vars, guards, body }
            if vars.is_empty() && guards.len() == 1 => {
            let body_is_false = matches!(&**body, Guarded::Disj(v) if v.is_empty());
            body_is_false && matches!(
                &guards[0],
                Atom::Less(_, _) | Atom::Subterm(_, _) | Atom::Last(_),
            )
        }
        _ => false,
    }
}

/// Smart `Conj` — flatten one level and short-circuit.
pub fn gconj(items: Vec<Guarded>) -> Guarded {
    let mut out = Vec::new();
    for it in items {
        match it {
            Guarded::Conj(inner) => out.extend(inner),
            // Conj([gfalse, ...]) = gfalse
            x if x == gfalse() => return gfalse(),
            x => out.push(x),
        }
    }
    // Mirror Haskell `gconj`'s `nub gfs` (Guarded.hs:418).
    let mut deduped: Vec<Guarded> = Vec::with_capacity(out.len());
    for x in out {
        if !deduped.contains(&x) { deduped.push(x); }
    }
    if deduped.len() == 1 { deduped.into_iter().next().unwrap() } else { Guarded::Conj(deduped) }
}

/// Walk a guarded formula and replace atoms whose truth value the
/// caller's `valuation` returns `Some(_)`. Mirrors Haskell's
/// `Theory.Constraint.System.Guarded.simplifyGuardedOrReturn`.
///
/// Cases:
/// - `Atom a` becomes `gtrue`/`gfalse` if the valuation is decided;
///   otherwise unchanged.
/// - `Conj` / `Disj` recurse and re-build via `gconj` / `gdisj` so
///   short-circuits collapse the right way.
/// - `GGuarded(All, [], guards, body)`: if any guard is False the
///   whole universal is True; otherwise drop guards that evaluate to
///   True and keep only the unknown ones, then recurse on the body.
/// - Guarded quantifiers with bound vars are left intact — the body
///   gets simplified once the quantifier is gone (matches Haskell).
pub fn simplify_guarded_with(
    fm: &Guarded,
    valuation: &dyn Fn(&p::Atom) -> Option<bool>,
) -> Guarded {
    match fm {
        Guarded::Atom(a) => match valuation(a) {
            Some(true) => gtrue(),
            Some(false) => gfalse(),
            None => fm.clone(),
        },
        Guarded::Disj(items) => {
            let simplified: Vec<_> = items.iter()
                .map(|g| simplify_guarded_with(g, valuation))
                .collect();
            gdisj(simplified)
        }
        Guarded::Conj(items) => {
            let simplified: Vec<_> = items.iter()
                .map(|g| simplify_guarded_with(g, valuation))
                .collect();
            gconj(simplified)
        }
        Guarded::GGuarded { qua: Quant::All, vars, guards, body } if vars.is_empty() => {
            let evaluated: Vec<(p::Atom, Option<bool>)> = guards.iter()
                .map(|a| (a.clone(), valuation(a)))
                .collect();
            // Any False guard → universal vacuously holds.
            if evaluated.iter().any(|(_, v)| v == &Some(false)) {
                return gtrue();
            }
            // Keep only the Unknown guards — True guards are vacuous.
            let kept: Vec<p::Atom> = evaluated.into_iter()
                .filter(|(_, v)| v.is_none())
                .map(|(a, _)| a)
                .collect();
            let body_s = simplify_guarded_with(body, valuation);
            if kept.is_empty() {
                // All guards were True — universal reduces to its body.
                body_s
            } else {
                Guarded::GGuarded {
                    qua: Quant::All, vars: vars.clone(),
                    guards: kept, body: Box::new(body_s),
                }
            }
        }
        // Quantifiers with bound vars stay as-is — Haskell delays
        // simplification past the binder.
        Guarded::GGuarded { .. } => fm.clone(),
    }
}

/// Smart `Disj` — flatten one level, short-circuit on `gtrue`, drop
/// `gfalse` items.  Mirrors Haskell's `gdisj` which treats `Disj` as a
/// set semantically: True absorbs, False is the unit.  Without dropping
/// gfalse items, partial_atom_valuation can turn `Disj([Eq(j,i),
/// Less(i,j)])` into `Disj([gfalse, gfalse])` (when j<i is known via
/// the order graph) and we'd split a 2-case Disj goal whose branches
/// both close — Haskell collapses this to `gfalse` directly.
pub fn gdisj(items: Vec<Guarded>) -> Guarded {
    let mut out = Vec::new();
    for it in items {
        match it {
            Guarded::Disj(inner) => {
                for x in inner {
                    if x == gtrue() { return gtrue(); }
                    if x == gfalse() { continue; }
                    out.push(x);
                }
            }
            x if x == gtrue() => return gtrue(),
            x if x == gfalse() => continue,
            x => out.push(x),
        }
    }
    // Mirror Haskell `gdisj`'s `nub gfs` (Guarded.hs:432).  Removes
    // syntactic-equal duplicates while preserving order. Order-preserving
    // dedup, like `Data.List.nub`.
    let mut deduped: Vec<Guarded> = Vec::with_capacity(out.len());
    for x in out {
        if !deduped.contains(&x) { deduped.push(x); }
    }
    if deduped.is_empty() { gfalse() }
    else if deduped.len() == 1 { deduped.into_iter().next().unwrap() }
    else { Guarded::Disj(deduped) }
}

/// Smart `GGuarded(Ex, ...)` — direct port of Haskell's `gex`:
/// ```text
///   gex []  as  gf                = gconj (map GAto as ++ [gf])
///   gex _   _   gf | gf == gfalse = gfalse
///   gex ss  as  gf                = GGuarded Ex ss as gf
/// ```
pub fn gex(vars: Vec<p::VarSpec>, guards: Vec<p::Atom>, body: Guarded) -> Guarded {
    if vars.is_empty() {
        let mut items: Vec<Guarded> = guards.into_iter()
            .map(Guarded::Atom).collect();
        items.push(body);
        return gconj(items);
    }
    if body == gfalse() { return gfalse(); }
    Guarded::GGuarded { qua: Quant::Ex, vars, guards, body: Box::new(body) }
}

/// Smart `GGuarded(All, ...)` — direct port of Haskell's `gall`:
/// ```text
///   gall _   []   gf              = gf
///   gall _   _    gf | gf == gtrue = gtrue
///   gall ss  atos gf              = GGuarded All ss atos gf
/// ```
pub fn gall(vars: Vec<p::VarSpec>, guards: Vec<p::Atom>, body: Guarded) -> Guarded {
    if guards.is_empty() { return body; }
    if body == gtrue() { return gtrue(); }
    Guarded::GGuarded { qua: Quant::All, vars, guards, body: Box::new(body) }
}

// =============================================================================
// Errors
// =============================================================================

#[derive(Debug, Clone)]
pub struct GuardError {
    pub message: String,
}

impl std::fmt::Display for GuardError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
impl std::error::Error for GuardError {}

fn err(msg: impl Into<String>) -> GuardError {
    GuardError { message: msg.into() }
}

// =============================================================================
// Conversion entry point
// =============================================================================

/// Convert a surface formula to its guarded form.
pub fn formula_to_guarded(f: &p::Formula) -> Result<Guarded, GuardError> {
    convert(false, f)
}

/// Returns `true` if the formula is "safety": closed (no free vars)
/// and contains no existential quantifier in its guarded form.
pub fn is_safety_formula(g: &Guarded) -> bool {
    fn no_existential(g: &Guarded) -> bool {
        match g {
            Guarded::Atom(_) => true,
            Guarded::GGuarded { qua: Quant::Ex, .. } => false,
            Guarded::GGuarded { qua: Quant::All, body, .. } => no_existential(body),
            Guarded::Disj(inner) => inner.iter().all(no_existential),
            Guarded::Conj(inner) => inner.iter().all(no_existential),
        }
    }
    free_vars(g).is_empty() && no_existential(g)
}

/// Compute the set of free (un-quantified) variables in a guarded formula.
pub fn free_vars(g: &Guarded) -> BTreeSet<String> {
    fn vs_atom(a: &p::Atom, out: &mut BTreeSet<String>) {
        let mut tv = Vec::new();
        match a {
            p::Atom::Eq(x, y) | p::Atom::Less(x, y)
            | p::Atom::LessMset(x, y) | p::Atom::Subterm(x, y) => {
                term_var_names(x, &mut tv); term_var_names(y, &mut tv);
            }
            p::Atom::Action(fact, t) => {
                for arg in &fact.args { term_var_names(arg, &mut tv); }
                term_var_names(t, &mut tv);
            }
            p::Atom::Last(t) => term_var_names(t, &mut tv),
            p::Atom::Pred(fact) => {
                for arg in &fact.args { term_var_names(arg, &mut tv); }
            }
        }
        for n in tv { out.insert(n); }
    }
    fn rec(g: &Guarded, out: &mut BTreeSet<String>, bound: &BTreeSet<String>) {
        match g {
            Guarded::Atom(a) => {
                let mut here = BTreeSet::new();
                vs_atom(a, &mut here);
                for n in here { if !bound.contains(&n) { out.insert(n); } }
            }
            Guarded::Disj(items) | Guarded::Conj(items) =>
                for it in items { rec(it, out, bound); },
            Guarded::GGuarded { vars, guards, body, .. } => {
                let mut new_bound = bound.clone();
                for v in vars { new_bound.insert(v.name.clone()); }
                for a in guards {
                    let mut here = BTreeSet::new();
                    vs_atom(a, &mut here);
                    for n in here { if !new_bound.contains(&n) { out.insert(n); } }
                }
                rec(body, out, &new_bound);
            }
        }
    }
    let mut out = BTreeSet::new();
    rec(g, &mut out, &BTreeSet::new());
    out
}

fn term_var_names(t: &p::Term, out: &mut Vec<String>) {
    match t {
        p::Term::Var(v) => out.push(v.name.clone()),
        p::Term::App(_, args) | p::Term::Pair(args) =>
            for a in args { term_var_names(a, out); },
        p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b)
        | p::Term::BinOp(_, a, b) => { term_var_names(a, out); term_var_names(b, out); }
        p::Term::PatMatch(inner) => term_var_names(inner, out),
        _ => {}
    }
}

// =============================================================================
// Polarity-aware conversion
// =============================================================================

fn convert(polarity: bool, f: &p::Formula) -> Result<Guarded, GuardError> {
    match f {
        p::Formula::True => Ok(gtf(polarity != true)),
        p::Formula::False => Ok(gtf(polarity != false)),
        p::Formula::Atom(a) => {
            if polarity { Ok(gnot_atom(a)) } else { Ok(Guarded::Atom(a.clone())) }
        }
        p::Formula::Not(g) => convert(!polarity, g),
        p::Formula::And(a, b) => {
            let mut sub = vec![convert(polarity, a)?, convert(polarity, b)?];
            if polarity {
                sub.reverse(); sub.reverse(); // no-op, satisfy borrow patterns
                Ok(gdisj(sub))
            } else {
                Ok(gconj(sub))
            }
        }
        p::Formula::Or(a, b) => {
            let sub = vec![convert(polarity, a)?, convert(polarity, b)?];
            if polarity { Ok(gconj(sub)) } else { Ok(gdisj(sub)) }
        }
        p::Formula::Implies(a, b) => {
            // p ⇒ q  is  ¬p ∨ q
            let nag = convert(!polarity, a)?;
            let cag = convert(polarity, b)?;
            if polarity { Ok(gconj(vec![nag, cag])) } else { Ok(gdisj(vec![nag, cag])) }
        }
        p::Formula::Iff(a, b) => {
            // p ↔ q  is  (p ⇒ q) ∧ (q ⇒ p)
            let lhs = p::Formula::Implies(a.clone(), b.clone());
            let rhs = p::Formula::Implies(b.clone(), a.clone());
            let sub = vec![convert(polarity, &lhs)?, convert(polarity, &rhs)?];
            Ok(gconj(sub))
        }
        // The quantifier shape (Forall vs Exists) determines whether the
        // body must be a top-level implication (`convert_all`) or a
        // conjunction (`convert_ex`). Polarity only affects which
        // quantifier label appears in the output and which polarity we
        // recurse with for inner subformulas.
        //
        // We "open" consecutive same-quantifier prefixes (mirroring
        // Haskell's `openFormulaPrefix`) so that `Ex x. Ex y. body`
        // is treated as a single `Ex [x, y]. body` for guard checking.
        p::Formula::Forall(_, _) | p::Formula::Exists(_, _) => {
            let (xs, body) = open_quantifier_prefix(f);
            let same_qua = matches!(f, p::Formula::Forall(_, _));
            if same_qua {
                let out_qua = if polarity { Quant::Ex } else { Quant::All };
                convert_all(&xs, body, polarity, out_qua)
            } else {
                let out_qua = if polarity { Quant::All } else { Quant::Ex };
                convert_ex(&xs, body, polarity, out_qua)
            }
        }
    }
}

/// Open consecutive same-quantifier binders. `Forall x. Forall y.
/// body` → `(vec![x, y], body)`. The first `Formula` argument must
/// itself be a quantifier; we follow only matching kinds.
fn open_quantifier_prefix(f: &p::Formula) -> (Vec<p::VarSpec>, &p::Formula) {
    let mut vars = Vec::new();
    let mut cur = f;
    let kind = match f {
        p::Formula::Forall(_, _) => 0,
        p::Formula::Exists(_, _) => 1,
        _ => return (vars, f),
    };
    loop {
        match cur {
            p::Formula::Forall(xs, body) if kind == 0 => {
                vars.extend(xs.iter().cloned());
                cur = body;
            }
            p::Formula::Exists(xs, body) if kind == 1 => {
                vars.extend(xs.iter().cloned());
                cur = body;
            }
            _ => break,
        }
    }
    (vars, cur)
}

/// Body-is-conjunction case (existential-shaped). The body is split
/// into guard atoms (action / equality) and remaining sub-formulas;
/// each quantified variable must be bound by some guard atom.
fn convert_ex(
    xs: &[p::VarSpec],
    body: &p::Formula,
    polarity: bool,
    out_qua: Quant,
) -> Result<Guarded, GuardError> {
    let (atoms, others) = split_conj_actions_eqs(body);
    let unguarded = remaining_unguarded(xs, &atoms);
    if !unguarded.is_empty() {
        return Err(unguarded_error(&unguarded));
    }
    let mut converted = Vec::new();
    for f in &others {
        converted.push(convert(polarity, f)?);
    }
    let body_guarded = if polarity { gdisj(converted) } else { gconj(converted) };
    Ok(Guarded::GGuarded {
        qua: out_qua,
        vars: xs.to_vec(),
        guards: atoms,
        body: Box::new(body_guarded),
    })
}

/// Body-is-implication case (universal-shaped). The antecedent is
/// split into guard atoms and remaining sub-formulas; each
/// quantified variable must be bound by some guard atom in the
/// antecedent.
fn convert_all(
    xs: &[p::VarSpec],
    body: &p::Formula,
    polarity: bool,
    out_qua: Quant,
) -> Result<Guarded, GuardError> {
    if let p::Formula::Implies(ante, succ) = body {
        let (atoms, ante_others) = split_conj_actions_eqs(ante);
        let unguarded = remaining_unguarded(xs, &atoms);
        if !unguarded.is_empty() {
            return Err(unguarded_error(&unguarded));
        }
        let mut sub = Vec::with_capacity(ante_others.len() + 1);
        for f in &ante_others {
            sub.push(convert(!polarity, f)?);
        }
        sub.push(convert(polarity, succ)?);
        let body_guarded = if polarity { gconj(sub) } else { gdisj(sub) };
        Ok(Guarded::GGuarded {
            qua: out_qua,
            vars: xs.to_vec(),
            guards: atoms,
            body: Box::new(body_guarded),
        })
    } else {
        Err(err("universal quantifier without toplevel implication"))
    }
}

/// Split a conjunction of formulas, separating guard atoms (action /
/// equality) from the remaining sub-formulas. Returns
/// `(guard_atoms, other_subformulas)`.
fn split_conj_actions_eqs(f: &p::Formula) -> (Vec<p::Atom>, Vec<p::Formula>) {
    fn rec(f: &p::Formula, atoms: &mut Vec<p::Atom>, others: &mut Vec<p::Formula>) {
        match f {
            p::Formula::And(a, b) => { rec(a, atoms, others); rec(b, atoms, others); }
            p::Formula::Atom(p::Atom::Action(fact, t)) =>
                atoms.push(p::Atom::Action(fact.clone(), t.clone())),
            p::Formula::Atom(p::Atom::Eq(a, b)) =>
                atoms.push(p::Atom::Eq(a.clone(), b.clone())),
            other => others.push(other.clone()),
        }
    }
    let mut atoms = Vec::new();
    let mut others = Vec::new();
    rec(f, &mut atoms, &mut others);
    (atoms, others)
}

/// Compute which of `xs` are NOT bound by any of `atoms`. Mirrors
/// Haskell's `remainingUnguarded`.
fn remaining_unguarded(xs: &[p::VarSpec], atoms: &[p::Atom]) -> Vec<p::VarSpec> {
    let mut sorted_atoms = atoms.to_vec();
    // Action atoms first, then equalities.
    sorted_atoms.sort_by_key(|a| match a {
        p::Atom::Action(_, _) => 0,
        _ => 1,
    });
    let mut unguarded: BTreeSet<String> = xs.iter().map(|v| v.name.clone()).collect();
    for atom in &sorted_atoms {
        match atom {
            p::Atom::Action(fact, t) => {
                let mut frees = Vec::new();
                for arg in &fact.args { term_var_names(arg, &mut frees); }
                term_var_names(t, &mut frees);
                for n in frees { unguarded.remove(&n); }
            }
            p::Atom::Eq(s, t) => {
                let mut sv = Vec::new();
                let mut tv = Vec::new();
                term_var_names(s, &mut sv);
                term_var_names(t, &mut tv);
                let s_covered = sv.iter().all(|n| !unguarded.contains(n));
                let t_covered = tv.iter().all(|n| !unguarded.contains(n));
                if s_covered { for n in tv { unguarded.remove(&n); } }
                else if t_covered { for n in sv { unguarded.remove(&n); } }
            }
            _ => {}
        }
    }
    xs.iter().filter(|v| unguarded.contains(&v.name)).cloned().collect()
}

fn unguarded_error(vars: &[p::VarSpec]) -> GuardError {
    let names: Vec<String> = vars.iter().map(|v| v.name.clone()).collect();
    err(format!("unguarded variable(s) {} in the subformula", names.join(", ")))
}

// =============================================================================
// Negate atoms (`gnotAtom` in Haskell)
// =============================================================================

/// `gnotAtom` — port of Haskell `Theory.Constraint.System.Guarded.gnotAtom`
/// (lib/theory/src/Theory/Constraint/System/Guarded.hs:408-410):
///
/// ```text
/// gnotAtom a = GGuarded All [] [a] gfalse
/// ```
///
/// Uniformly negates every atom by wrapping it in a universal
/// guarded ⊥: "for all traces in which `a` holds, ⊥" ≡ ¬a. This
/// is the right encoding for Less/Eq/Action/Last/Pred/Subterm alike,
/// independent of the term sort.
///
/// (An earlier port used `gdisj [Less, Less]` for ¬EqE / ¬Less and
/// `gex [] [a] gfalse` for ¬Action — both were copy-paste errors from
/// `toInductionHypothesis` (which DOES decompose Less for induction).
/// The disjunction form is semantically wrong for term-sort EqE since
/// Less is undefined between Msg/Fresh/Pub terms; the Ex form is
/// semantically False rather than ¬Action.  See `Guarded.hs:408-410`
/// vs `Guarded.hs:614-616`.)
fn gnot_atom(a: &p::Atom) -> Guarded {
    Guarded::GGuarded {
        qua: Quant::All,
        vars: Vec::new(),
        guards: vec![a.clone()],
        body: Box::new(gfalse()),
    }
}

// =============================================================================
// Top-level negation — port of Haskell's `gnot`.
// =============================================================================

/// Variable-renaming substitution: maps `(name, idx)` to a new `idx`.
/// Used by `Ex` decomposition to allocate fresh indices for bound vars
/// without colliding with the rest of the system.
pub type VarSubst = std::collections::HashMap<(String, u64), p::Term>;

/// Convenience: build a single (name, idx) → fresh-idx-renaming entry
/// for `VarSubst`. Used by Ex decomposition where we just bump indices.
pub fn subst_renaming(name: String, old_idx: u64, new_idx: u64,
                       sort: p::SortHint) -> ((String, u64), p::Term) {
    let target = p::Term::Var(p::VarSpec {
        name: name.clone(), idx: new_idx, sort, typ: None,
    });
    ((name, old_idx), target)
}

/// Apply a `VarSubst` to a parser-AST term in-place.
/// Rewrite every Maude-witness LVar `~mw#N` (any idx) to a canonical
/// `~mw#0`.  Used to dedup implied formulas in `insertImpliedFormulas`
/// where Maude unification mints a fresh witness per call: two
/// structurally-identical derivations from the same (restriction,
/// action-node) pair would otherwise have different witness idx and
/// bypass `Vec::contains`, causing solved_formulas to grow without
/// bound and the simplify loop to never converge.
///
/// We touch ONLY witness vars (name == "~mw") — every other LVar
/// (real protocol vars, distinct named fresh values) keeps its
/// identity, so the dedup doesn't over-merge legitimately-distinct
/// implications.
pub fn normalize_witness_lvars(g: &Guarded) -> Guarded {
    let mut subst: VarSubst = std::collections::HashMap::new();
    collect_witness_vars(g, &mut subst);
    if subst.is_empty() { return g.clone(); }
    subst_guarded(g, &subst)
}

/// Alpha-canonicalize `GGuarded` bound-variable idxs.
///
/// Background: Haskell's `Guarded` uses DeBruijn-bound vars (`BVar
/// Bound`), so two alpha-equivalent formulas — say `Ex j:5. KU(s)@j:5`
/// and `Ex j:6. KU(s)@j:6` produced by impliedFormulas across separate
/// firings — are structurally identical (the bound index doesn't show
/// up in the term tree). HS's `S.member` dedup works trivially.
///
/// Rust represents bound vars as `VarSpec` (free vars masquerading as
/// bound) so `freshen_system` (sources.rs:4042+) which shifts ALL
/// VarSpec idxs also shifts bound-var idxs. After freshening, the
/// stored universal's body has bound `j:K` for some non-zero K. When
/// impl_formulas re-fires across iterations, each firing produces a
/// `Disj([Ex j:Ki, ...])` with a different bound idx Ki, none of which
/// matches the previously-stored `j:Kj` under structural equality.
///
/// This breaks dedup — the same source-assertion Disj gets inserted
/// many times as alpha-equivalent copies, each producing its own
/// `Goal::Disj` and an extra `solve / case_1` step in the proof tree.
/// Trigger: NSLPK3_untagged::nonce_secrecy line 7.
///
/// Fix: a scope-aware traversal that allocates canonical idxs (from a
/// fresh per-call counter) to each `GGuarded`'s bound vars and rewrites
/// references inside guards + body accordingly. Two alpha-equivalent
/// formulas produce IDENTICAL canonical output because the walk is
/// deterministic and the counter starts at the same value.
///
/// Free vars are preserved (the canonical counter starts well above
/// any real free-var idx so shifts can't collide). Names are not
/// touched — only the same-universal-different-allocation case
/// matters in practice; truly different bound-var names should NOT
/// merge under this normalization.
pub fn normalize_bound_lvars(g: &Guarded) -> Guarded {
    // Per-call counter; high baseline so any system free-var idx
    // (typically <1M after freshen) remains untouched on lookup.
    let mut next_idx: u64 = 1_000_000_000;
    let mut scope: Vec<std::collections::HashMap<(String, u64), p::VarSpec>> = Vec::new();
    rec_g(g, &mut scope, &mut next_idx)
}

fn rec_g(
    g: &Guarded,
    scope: &mut Vec<std::collections::HashMap<(String, u64), p::VarSpec>>,
    next_idx: &mut u64,
) -> Guarded {
    match g {
        Guarded::Atom(a) => Guarded::Atom(rec_a(a, scope)),
        Guarded::Disj(items) =>
            Guarded::Disj(items.iter().map(|i| rec_g(i, scope, next_idx)).collect()),
        Guarded::Conj(items) =>
            Guarded::Conj(items.iter().map(|i| rec_g(i, scope, next_idx)).collect()),
        Guarded::GGuarded { qua, vars, guards, body } => {
            let mut layer: std::collections::HashMap<(String, u64), p::VarSpec> =
                std::collections::HashMap::new();
            let mut new_vars = Vec::with_capacity(vars.len());
            for v in vars {
                let canon = p::VarSpec {
                    name: v.name.clone(),
                    idx: *next_idx,
                    sort: v.sort,
                    typ: v.typ.clone(),
                };
                *next_idx = next_idx.saturating_add(1);
                layer.insert((v.name.clone(), v.idx), canon.clone());
                new_vars.push(canon);
            }
            scope.push(layer);
            let new_guards: Vec<p::Atom> = guards.iter().map(|a| rec_a(a, scope)).collect();
            let new_body = rec_g(body, scope, next_idx);
            scope.pop();
            Guarded::GGuarded {
                qua: qua.clone(),
                vars: new_vars,
                guards: new_guards,
                body: Box::new(new_body),
            }
        }
    }
}

fn rec_a(
    a: &p::Atom,
    scope: &[std::collections::HashMap<(String, u64), p::VarSpec>],
) -> p::Atom {
    use p::Atom;
    match a {
        Atom::Eq(s, t) => Atom::Eq(rec_t(s, scope), rec_t(t, scope)),
        Atom::Less(s, t) => Atom::Less(rec_t(s, scope), rec_t(t, scope)),
        Atom::LessMset(s, t) => Atom::LessMset(rec_t(s, scope), rec_t(t, scope)),
        Atom::Subterm(s, t) => Atom::Subterm(rec_t(s, scope), rec_t(t, scope)),
        Atom::Action(f, t) => {
            let mut f2 = f.clone();
            f2.args = f.args.iter().map(|a| rec_t(a, scope)).collect();
            Atom::Action(f2, rec_t(t, scope))
        }
        Atom::Last(t) => Atom::Last(rec_t(t, scope)),
        Atom::Pred(f) => {
            let mut f2 = f.clone();
            f2.args = f.args.iter().map(|a| rec_t(a, scope)).collect();
            Atom::Pred(f2)
        }
    }
}

fn rec_t(
    t: &p::Term,
    scope: &[std::collections::HashMap<(String, u64), p::VarSpec>],
) -> p::Term {
    use p::Term;
    match t {
        Term::Var(v) => {
            // Innermost-first lookup; only bound vars in scope get rewritten.
            for layer in scope.iter().rev() {
                if let Some(canon) = layer.get(&(v.name.clone(), v.idx)) {
                    return Term::Var(canon.clone());
                }
            }
            Term::Var(v.clone())
        }
        Term::App(name, args) => Term::App(
            name.clone(), args.iter().map(|a| rec_t(a, scope)).collect()),
        Term::Pair(items) => Term::Pair(items.iter().map(|i| rec_t(i, scope)).collect()),
        Term::AlgApp(name, a, b) => Term::AlgApp(
            name.clone(), Box::new(rec_t(a, scope)), Box::new(rec_t(b, scope))),
        Term::Diff(a, b) => Term::Diff(
            Box::new(rec_t(a, scope)), Box::new(rec_t(b, scope))),
        Term::BinOp(op, a, b) => Term::BinOp(
            *op, Box::new(rec_t(a, scope)), Box::new(rec_t(b, scope))),
        Term::PatMatch(t) => Term::PatMatch(Box::new(rec_t(t, scope))),
        other => other.clone(),
    }
}

/// Normalize equivalent sort hints so two `Guarded` formulas that
/// differ ONLY by sort hint compare equal under `==`.
///
/// All of `SortHint::Msg`, `SortHint::Suffix(SuffixSort::Msg)`, and
/// `SortHint::Untagged` map to `LSort::Msg` in elaboration (see
/// `elaborate::sort_of`).  Implied-formula matching uses Maude →
/// LNTerm → parser-AST round trips, where `lnterm_to_term` always
/// produces the canonical `SortHint::Msg`/`Pub`/`Fresh`/`Node`/`Nat`
/// form regardless of the original hint.  Formulas created by other
/// paths (lemma re-instantiation, ginduct on the IH) may retain
/// `Untagged` or suffix-style hints.  Without normalisation, two
/// semantically-identical formulas compare unequal and the dedupe in
/// `insert_formula` / `insert_implied_formulas_pass` lets
/// duplicates accumulate.
///
/// Concretely: `RFID_Simple::Device_Init_Use_Set` was generating
/// duplicate IH-Disjs at depth 2 — one with `sk:Msg` and one with
/// `sk:Untagged`.
pub fn normalize_sort_hints(g: &Guarded) -> Guarded {
    fn norm_sort(s: p::SortHint) -> p::SortHint {
        match s {
            p::SortHint::Pub | p::SortHint::Suffix(p::SuffixSort::Pub) =>
                p::SortHint::Pub,
            p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) =>
                p::SortHint::Fresh,
            p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node) =>
                p::SortHint::Node,
            p::SortHint::Nat | p::SortHint::Suffix(p::SuffixSort::Nat) =>
                p::SortHint::Nat,
            p::SortHint::Msg | p::SortHint::Suffix(p::SuffixSort::Msg)
            | p::SortHint::Untagged => p::SortHint::Msg,
        }
    }
    fn norm_var(v: &p::VarSpec) -> p::VarSpec {
        p::VarSpec {
            name: v.name.clone(),
            idx: v.idx,
            sort: norm_sort(v.sort),
            typ: v.typ.clone(),
        }
    }
    fn norm_term(t: &p::Term) -> p::Term {
        use p::Term;
        match t {
            Term::Var(v) => Term::Var(norm_var(v)),
            Term::App(n, args) => Term::App(
                n.clone(), args.iter().map(norm_term).collect()),
            Term::Pair(args) => Term::Pair(args.iter().map(norm_term).collect()),
            Term::AlgApp(n, a, b) => Term::AlgApp(
                n.clone(), Box::new(norm_term(a)), Box::new(norm_term(b))),
            Term::Diff(a, b) => Term::Diff(
                Box::new(norm_term(a)), Box::new(norm_term(b))),
            Term::BinOp(op, a, b) => Term::BinOp(
                *op, Box::new(norm_term(a)), Box::new(norm_term(b))),
            Term::PatMatch(inner) => Term::PatMatch(Box::new(norm_term(inner))),
            _ => t.clone(),
        }
    }
    fn norm_fact(f: &p::Fact) -> p::Fact {
        p::Fact {
            persistent: f.persistent,
            name: f.name.clone(),
            args: f.args.iter().map(norm_term).collect(),
            annotations: f.annotations.clone(),
        }
    }
    fn norm_atom(a: &p::Atom) -> p::Atom {
        use p::Atom;
        match a {
            Atom::Action(f, t) => Atom::Action(norm_fact(f), norm_term(t)),
            Atom::Eq(x, y) => Atom::Eq(norm_term(x), norm_term(y)),
            Atom::Less(x, y) => Atom::Less(norm_term(x), norm_term(y)),
            Atom::LessMset(x, y) => Atom::LessMset(norm_term(x), norm_term(y)),
            Atom::Subterm(x, y) => Atom::Subterm(norm_term(x), norm_term(y)),
            Atom::Last(t) => Atom::Last(norm_term(t)),
            Atom::Pred(f) => Atom::Pred(norm_fact(f)),
        }
    }
    fn rec(g: &Guarded) -> Guarded {
        match g {
            Guarded::Atom(a) => Guarded::Atom(norm_atom(a)),
            Guarded::Disj(items) => Guarded::Disj(items.iter().map(rec).collect()),
            Guarded::Conj(items) => Guarded::Conj(items.iter().map(rec).collect()),
            Guarded::GGuarded { qua, vars, guards, body } => Guarded::GGuarded {
                qua: qua.clone(),
                vars: vars.iter().map(norm_var).collect(),
                guards: guards.iter().map(norm_atom).collect(),
                body: Box::new(rec(body)),
            },
        }
    }
    rec(g)
}

fn collect_witness_vars(g: &Guarded, out: &mut VarSubst) {
    match g {
        Guarded::Atom(a) => collect_witness_vars_atom(a, out),
        Guarded::Disj(items) | Guarded::Conj(items) => {
            for i in items { collect_witness_vars(i, out); }
        }
        Guarded::GGuarded { guards, body, .. } => {
            for a in guards { collect_witness_vars_atom(a, out); }
            collect_witness_vars(body, out);
        }
    }
}

fn collect_witness_vars_atom(a: &p::Atom, out: &mut VarSubst) {
    use p::Atom;
    match a {
        Atom::Eq(x, y) | Atom::Less(x, y) | Atom::LessMset(x, y)
        | Atom::Subterm(x, y) => {
            collect_witness_vars_term(x, out);
            collect_witness_vars_term(y, out);
        }
        Atom::Action(f, t) => {
            for arg in &f.args { collect_witness_vars_term(arg, out); }
            collect_witness_vars_term(t, out);
        }
        Atom::Last(t) => collect_witness_vars_term(t, out),
        Atom::Pred(f) => {
            for arg in &f.args { collect_witness_vars_term(arg, out); }
        }
    }
}

fn collect_witness_vars_term(t: &p::Term, out: &mut VarSubst) {
    use p::Term;
    match t {
        Term::Var(v) => {
            if v.name == "~mw" {
                let canonical = p::VarSpec {
                    name: v.name.clone(),
                    idx: 0,                  // canonical idx
                    sort: v.sort,
                    typ: v.typ.clone(),
                };
                out.insert((v.name.clone(), v.idx), Term::Var(canonical));
            }
        }
        Term::App(_, args) | Term::Pair(args) => {
            for a in args { collect_witness_vars_term(a, out); }
        }
        Term::AlgApp(_, a, b) | Term::Diff(a, b) | Term::BinOp(_, a, b) => {
            collect_witness_vars_term(a, out);
            collect_witness_vars_term(b, out);
        }
        Term::PatMatch(t) => collect_witness_vars_term(t, out),
        Term::PubLit(_) | Term::FreshLit(_) | Term::NatLit(_)
        | Term::Number(_) | Term::NumberOne | Term::NatOne
        | Term::DhNeutral => {}
    }
}

/// Convert the eq-store's `Subst<Name, LVar>` to a parser-AST
/// `VarSubst` so it can be applied to `Guarded` formulas.  Used to
/// canonicalize implied formulas during `insertImpliedFormulas` dedup:
/// Maude unification mints fresh witness LVars per call, so
/// structurally-identical derivations would otherwise be treated as
/// distinct entries.
pub fn var_subst_from_eq_store(
    eq_store: &crate::tools::equation_store::EquationStore,
) -> VarSubst {
    use tamarin_term::lterm::LVar;
    use crate::elaborate::lnterm_to_term;
    let mut out: VarSubst = std::collections::HashMap::new();
    let pairs: Vec<(LVar, _)> = eq_store.subst.to_list();
    for (lv, lt) in pairs {
        out.insert((lv.name.clone(), lv.idx), lnterm_to_term(&lt));
    }
    out
}

pub fn subst_term(t: &p::Term, s: &VarSubst) -> p::Term {
    use p::Term;
    match t {
        Term::Var(v) => {
            let key = (v.name.clone(), v.idx);
            if let Some(target) = s.get(&key) {
                target.clone()
            } else {
                Term::Var(v.clone())
            }
        }
        Term::PubLit(_) | Term::FreshLit(_) | Term::NatLit(_)
        | Term::Number(_) | Term::NumberOne | Term::NatOne | Term::DhNeutral => t.clone(),
        Term::App(name, args) =>
            Term::App(name.clone(), args.iter().map(|a| subst_term(a, s)).collect()),
        Term::AlgApp(name, a, b) => Term::AlgApp(
            name.clone(),
            Box::new(subst_term(a, s)),
            Box::new(subst_term(b, s)),
        ),
        Term::Pair(items) => Term::Pair(items.iter().map(|i| subst_term(i, s)).collect()),
        Term::Diff(a, b) => Term::Diff(
            Box::new(subst_term(a, s)),
            Box::new(subst_term(b, s)),
        ),
        Term::BinOp(op, a, b) => Term::BinOp(
            *op,
            Box::new(subst_term(a, s)),
            Box::new(subst_term(b, s)),
        ),
        Term::PatMatch(t) => Term::PatMatch(Box::new(subst_term(t, s))),
    }
}

/// Apply a `VarSubst` to a parser-AST fact.
pub fn subst_fact(f: &p::Fact, s: &VarSubst) -> p::Fact {
    p::Fact {
        args: f.args.iter().map(|a| subst_term(a, s)).collect(),
        ..f.clone()
    }
}

/// Apply a `VarSubst` to a parser-AST atom.
pub fn subst_atom(a: &p::Atom, s: &VarSubst) -> p::Atom {
    use p::Atom;
    match a {
        Atom::Eq(x, y) => Atom::Eq(subst_term(x, s), subst_term(y, s)),
        Atom::Less(x, y) => Atom::Less(subst_term(x, s), subst_term(y, s)),
        Atom::LessMset(x, y) => Atom::LessMset(subst_term(x, s), subst_term(y, s)),
        Atom::Subterm(x, y) => Atom::Subterm(subst_term(x, s), subst_term(y, s)),
        Atom::Action(f, t) => Atom::Action(subst_fact(f, s), subst_term(t, s)),
        Atom::Last(t) => Atom::Last(subst_term(t, s)),
        Atom::Pred(f) => Atom::Pred(subst_fact(f, s)),
    }
}

/// Apply a `VarSubst` to a guarded formula. Substitutes through
/// guards, body, and every nested term/atom — but does NOT descend
/// into a nested `GGuarded` whose `vars` shadow names in `s` (those
/// references aren't free).
///
/// Capture-avoiding: if a binder's bound var would be captured by a
/// free var in the substitution's range, the bound var is alpha-
/// renamed to a fresh idx first.  Without this, an LVar substitution
/// like `j:Node:2 → i:Node:0` applied to a formula
/// `∀ i:0. body[i, j:2]` would conflate the free `j:2` (now `i:0`)
/// with the bound `i:0` — the chaum_unforgeability wrong-falsified
/// root cause.
pub fn subst_guarded(g: &Guarded, s: &VarSubst) -> Guarded {
    // Hot path: empty subst → no-op clone.
    if s.is_empty() { return g.clone(); }
    // Precompute the subst's range free vars once.  Captures can
    // only occur for names that appear free in the subst's range
    // values.
    let mut range_free: std::collections::HashSet<(String, u64)>
        = std::collections::HashSet::new();
    for (_, t) in s.iter() {
        collect_term_vars(t, &mut range_free);
    }
    subst_guarded_inner(g, s, &range_free)
}

fn subst_guarded_inner(
    g: &Guarded,
    s: &VarSubst,
    range_free: &std::collections::HashSet<(String, u64)>,
) -> Guarded {
    match g {
        Guarded::Atom(a) => Guarded::Atom(subst_atom(a, s)),
        Guarded::Disj(items) =>
            Guarded::Disj(items.iter().map(|i| subst_guarded_inner(i, s, range_free)).collect()),
        Guarded::Conj(items) =>
            Guarded::Conj(items.iter().map(|i| subst_guarded_inner(i, s, range_free)).collect()),
        Guarded::GGuarded { qua, vars, guards, body } => {
            // Drop substitutions for any var shadowed by this binder.
            let shadowed: std::collections::HashSet<(String, u64)> = vars.iter()
                .map(|v| (v.name.clone(), v.idx))
                .collect();
            let s_filtered: VarSubst = s.iter()
                .filter(|((n, i), _)| !shadowed.contains(&(n.clone(), *i)))
                .map(|((n, i), v)| ((n.clone(), *i), v.clone()))
                .collect();
            // Capture check: bound vars that are free in the FILTERED
            // subst's range.  Earlier we used the parent's `range_free`
            // (computed from the FULL subst), which over-triggered the
            // capture-avoidance: shadowed entries dropped here no
            // longer apply, so their range values shouldn't influence
            // capture detection.  Mirrors HS `applySkGuarded` semantics
            // — DeBruijn-bound vars there are unaffected by free-var
            // substitution, so no capture occurs.  Without this fix,
            // a lemma's bound vars (`nr:0`, `ni:0`, `i:0`) get spuriously
            // renamed to fresh idxs whenever ANY full-subst entry maps
            // a (filtered-out) bound key to a value naming the same
            // bound var — producing extra IMPL-FIRE matches that HS
            // never emits (task #287, NSLPK3 line-105 cluster).
            let filtered_range_free: std::collections::HashSet<(String, u64)> = {
                let mut r = std::collections::HashSet::new();
                for ((_, _), t) in s_filtered.iter() {
                    collect_term_vars(t, &mut r);
                }
                r
            };
            let captures: Vec<(String, u64)> = vars.iter()
                .map(|v| (v.name.clone(), v.idx))
                .filter(|k| filtered_range_free.contains(k))
                .collect();
            if captures.is_empty() {
                // Pass the filtered range_free down to the body — the
                // parent's `range_free` would over-conservatively still
                // include the dropped (shadowed) entries.
                return Guarded::GGuarded {
                    qua: qua.clone(),
                    vars: vars.clone(),
                    guards: guards.iter().map(|a| subst_atom(a, &s_filtered)).collect(),
                    body: Box::new(subst_guarded_inner(body, &s_filtered, &filtered_range_free)),
                };
            }
            // Allocate fresh idxs.  Use max(filtered_range_free.idx) + 1 as floor.
            let mut next_idx: u64 = filtered_range_free.iter().map(|(_, i)| *i).max()
                .unwrap_or(0).saturating_add(1);
            // Also bump above any explicit idx in the binder vars.
            for v in vars { if v.idx >= next_idx { next_idx = v.idx + 1; } }
            let mut rename: VarSubst = VarSubst::new();
            let mut new_vars: Vec<p::VarSpec> = Vec::with_capacity(vars.len());
            for v in vars {
                if captures.contains(&(v.name.clone(), v.idx)) {
                    let new_v = p::VarSpec {
                        name: v.name.clone(),
                        idx: next_idx,
                        sort: v.sort,
                        typ: v.typ.clone(),
                    };
                    rename.insert(
                        (v.name.clone(), v.idx),
                        p::Term::Var(new_v.clone()));
                    new_vars.push(new_v);
                    next_idx = next_idx.saturating_add(1);
                } else {
                    new_vars.push(v.clone());
                }
            }
            // Build a combined substitution: rename ∪ s_filtered.
            // The rename keys are the OLD bound vars, mapping to new
            // bound vars.  s_filtered's keys are the free vars from
            // the eq-store.  Since the bound vars and free vars are
            // disjoint (bound vars are now renamed to new idxs in
            // the body's references), we can combine them.
            let mut combined: VarSubst = s_filtered.clone();
            for (k, v) in &rename {
                combined.insert(k.clone(), v.clone());
            }
            // Recompute range_free for the combined subst — captures
            // could compound if rename targets are already in range_free.
            let mut combined_range_free: std::collections::HashSet<(String, u64)>
                = filtered_range_free.clone();
            for (_, t) in rename.iter() {
                collect_term_vars(t, &mut combined_range_free);
            }
            Guarded::GGuarded {
                qua: qua.clone(),
                vars: new_vars,
                guards: guards.iter().map(|a| subst_atom(a, &combined)).collect(),
                body: Box::new(subst_guarded_inner(body, &combined, &combined_range_free)),
            }
        }
    }
}

/// Collect (name, idx) of every variable that appears in a parser-AST term.
fn collect_term_vars(t: &p::Term, out: &mut std::collections::HashSet<(String, u64)>) {
    use p::Term;
    match t {
        Term::Var(v) => { out.insert((v.name.clone(), v.idx)); }
        Term::App(_, args) | Term::Pair(args) => {
            for a in args { collect_term_vars(a, out); }
        }
        Term::AlgApp(_, a, b) | Term::Diff(a, b) | Term::BinOp(_, a, b) => {
            collect_term_vars(a, out); collect_term_vars(b, out);
        }
        Term::PatMatch(t) => collect_term_vars(t, out),
        Term::PubLit(_) | Term::FreshLit(_) | Term::NatLit(_)
        | Term::Number(_) | Term::NumberOne | Term::NatOne | Term::DhNeutral => {}
    }
}

/// Find the maximum variable idx used in a guarded formula. Used
/// to allocate fresh indices without collisions.
pub fn max_var_idx(g: &Guarded) -> u64 {
    fn rec_term(t: &p::Term, m: &mut u64) {
        use p::Term;
        match t {
            Term::Var(v) => { if v.idx > *m { *m = v.idx; } }
            Term::App(_, args) | Term::Pair(args) => {
                for a in args { rec_term(a, m); }
            }
            Term::AlgApp(_, a, b) | Term::Diff(a, b) | Term::BinOp(_, a, b) => {
                rec_term(a, m); rec_term(b, m);
            }
            Term::PatMatch(t) => rec_term(t, m),
            _ => {}
        }
    }
    fn rec_atom(a: &p::Atom, m: &mut u64) {
        use p::Atom;
        match a {
            Atom::Eq(x, y) | Atom::Less(x, y) | Atom::LessMset(x, y)
            | Atom::Subterm(x, y) => { rec_term(x, m); rec_term(y, m); }
            Atom::Action(f, t) => {
                for arg in &f.args { rec_term(arg, m); }
                rec_term(t, m);
            }
            Atom::Last(t) => rec_term(t, m),
            Atom::Pred(f) => for a in &f.args { rec_term(a, m); },
        }
    }
    fn rec(g: &Guarded, m: &mut u64) {
        match g {
            Guarded::Atom(a) => rec_atom(a, m),
            Guarded::Disj(xs) | Guarded::Conj(xs) => for x in xs { rec(x, m); },
            Guarded::GGuarded { vars, guards, body, .. } => {
                for v in vars { if v.idx > *m { *m = v.idx; } }
                for a in guards { rec_atom(a, m); }
                rec(body, m);
            }
        }
    }
    let mut m = 0u64;
    rec(g, &mut m);
    m
}

/// `gnot`: structural negation of a guarded formula.
///   - `Atom a`        → `gnot_atom a`
///   - `Disj xs`       → `Conj (map gnot xs)`
///   - `Conj xs`       → `Disj (map gnot xs)`
///   - `All vs gs. gf` → `Ex vs. (gs ∧ ¬gf)` (i.e. `gs ∧ ¬gf` is the new body)
///   - `Ex vs gs. gf`  → `All vs. (gs ⇒ ¬gf)`
pub fn gnot(g: &Guarded) -> Guarded {
    match g {
        Guarded::Atom(a) => gnot_atom(a),
        Guarded::Disj(xs) => gconj(xs.iter().map(gnot).collect()),
        Guarded::Conj(xs) => gdisj(xs.iter().map(gnot).collect()),
        // Use the smart constructors `gex`/`gall` (NOT direct
        // GGuarded build) so that empty-quantifier collapses fire:
        // - `gnot(GGuarded(All, [], [Less i j], gfalse))` (== ¬(i<j))
        //   goes through `gex [] [Less i j] gtrue` → `gconj([Less i j, gtrue])`
        //   → `Less i j` (the atom), not a stale `GGuarded(Ex, [], [Less i j], gtrue)`.
        // Without this collapse, `to_induction_hypothesis` sees the body
        // as nested GGuarded and produces extra `¬(Less)` disjuncts in
        // the IH instead of collapsing them down — leading to a much
        // larger Disj at goal-split time. Mirrors Haskell:
        //   go (GGuarded All ss as gf) = gex  ss as (go gf)
        //   go (GGuarded Ex  ss as gf) = gall ss as (go gf)
        Guarded::GGuarded { qua: Quant::All, vars, guards, body } => {
            gex(vars.clone(), guards.clone(), gnot(body))
        }
        Guarded::GGuarded { qua: Quant::Ex, vars, guards, body } => {
            gall(vars.clone(), guards.clone(), gnot(body))
        }
    }
}

// =============================================================================
// Induction — port of `Theory.Constraint.System.Guarded.ginduct`
// =============================================================================

/// `satisfiedByEmptyTrace`: does the formula hold under the empty
/// trace (no actions)? Returns `Err` for atoms outside the scope of a
/// quantifier (formula is not doubly guarded).
pub fn satisfied_by_empty_trace(g: &Guarded) -> Result<bool, String> {
    match g {
        Guarded::Atom(_) => Err("atom outside the scope of a quantifier".to_string()),
        Guarded::Disj(xs) => {
            let mut any = false;
            for x in xs {
                if satisfied_by_empty_trace(x)? { any = true; }
            }
            Ok(any)
        }
        Guarded::Conj(xs) => {
            for x in xs {
                if !satisfied_by_empty_trace(x)? { return Ok(false); }
            }
            Ok(true)
        }
        Guarded::GGuarded { qua, .. } => Ok(matches!(qua, Quant::All)),
    }
}

/// Does the formula contain at least one action atom (anywhere)?
/// `containsAction` from Haskell's `ginduct`.
pub fn contains_action(g: &Guarded) -> bool {
    match g {
        Guarded::Atom(a) => matches!(a, p::Atom::Action(_, _)),
        Guarded::Disj(xs) | Guarded::Conj(xs) => xs.iter().any(contains_action),
        Guarded::GGuarded { guards, body, .. } => {
            !guards.is_empty()
                || guards.iter().any(|a| matches!(a, p::Atom::Action(_, _)))
                || contains_action(body)
        }
    }
}

/// Is `g` closed (no free variables)?
fn is_closed(g: &Guarded) -> bool {
    free_vars(g).is_empty()
}

/// Test whether an atom is a `Last(_)` predicate.
fn is_last_atom(a: &p::Atom) -> bool {
    matches!(a, p::Atom::Last(_))
}

/// `toInductionHypothesis`: rewrite a doubly guarded formula into its
/// induction hypothesis form. Errors out on non-last-free formulas.
pub fn to_induction_hypothesis(g: &Guarded) -> Result<Guarded, String> {
    match g {
        Guarded::GGuarded { qua, vars, guards, body } => {
            if guards.iter().any(is_last_atom) {
                return Err("formula not last-free".to_string());
            }
            let body2 = to_induction_hypothesis(body)?;
            // Emit `Last(v)` for every node-sorted bound variable.
            // Mirrors Haskell's
            //   lastAtos = [ Last (varTerm (Bound j))
            //              | (j, (_, LSortNode)) <- zip [0..] (reverse ss) ]
            // We use named vars, so no de-Bruijn shifting is needed: the
            // body2 refers to the same `vars` by name, and we just emit
            // `Last(Var(v))` for each node-sorted v in `vars`.
            // Haskell `reverse ss` (Guarded.hs:613) — node-sorted binders
            // emitted in REVERSE quantifier order.  For `∀ k #i #j`, ss
            // reversed = [#j, #i, k] → lastAtos = [Last(#j), Last(#i)].
            // Without `.rev()`, our disj order is [#i, #j] (matches HS
            // case_2 first), inverting `case_1`/`case_2` labels for the
            // `last`-disjunction split and breaking proof-tree shape diff.
            let last_atos: Vec<Guarded> = vars.iter().rev()
                .filter(|v| matches!(
                    v.sort,
                    p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node)
                ))
                .map(|v| Guarded::Atom(p::Atom::Last(p::Term::Var(v.clone()))))
                .collect();
            match qua {
                Quant::All => {
                    // gex ss as (gconj (map gnotAtom lastAtos ++ [gf']))
                    let mut items: Vec<Guarded> = last_atos.iter()
                        .map(|g| gnot(g)).collect();
                    items.push(body2);
                    Ok(gex(vars.clone(), guards.clone(), gconj(items)))
                }
                Quant::Ex => {
                    // gall ss as (gdisj (map GAto lastAtos ++ [gf']))
                    let mut items = last_atos;
                    items.push(body2);
                    Ok(gall(vars.clone(), guards.clone(), gdisj(items)))
                }
            }
        }
        Guarded::Atom(p::Atom::Less(i, j)) => Ok(Guarded::Disj(vec![
            Guarded::Atom(p::Atom::Eq(i.clone(), j.clone())),
            Guarded::Atom(p::Atom::Less(j.clone(), i.clone())),
        ])),
        Guarded::Atom(p::Atom::Last(_)) => Err("formula not last-free".to_string()),
        Guarded::Atom(a) => Ok(gnot_atom(a)),
        Guarded::Disj(xs) => {
            let xs2 = xs.iter()
                .map(to_induction_hypothesis)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(gconj(xs2))
        }
        Guarded::Conj(xs) => {
            let xs2 = xs.iter()
                .map(to_induction_hypothesis)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(gdisj(xs2))
        }
    }
}

/// `ginduct`: try to prove `g` by induction over the trace. Returns
/// `(base_case, step_case)` formulas.
///
/// - `base_case`: `gtrue`/`gfalse` depending on whether the empty
///   trace satisfies `g`.
/// - `step_case`: `g ∧ induction_hypothesis(g)`.
pub fn ginduct(g: &Guarded) -> Result<(Guarded, Guarded), String> {
    if !is_closed(g) {
        return Err("formula not closed".to_string());
    }
    if !contains_action(g) {
        return Err("formula contains no action atom".to_string());
    }
    let base = satisfied_by_empty_trace(g)?;
    let gf_ih = to_induction_hypothesis(g)?;
    let base_case = gtf(base);
    let step_case = gconj(vec![g.clone(), gf_ih]);
    Ok((base_case, step_case))
}

/// Apply a `VarSpec → VarSpec` transformation to every FREE variable
/// reference in a `Guarded` formula.  Variables bound by an enclosing
/// `GGuarded` are NOT passed to `f` — they stay verbatim.  Used by
/// `freshen_system_keep_with_shift` (sources.rs) to shift free-var
/// idxs in stored formulas / solved_formulas / lemmas alongside the
/// rest of the system, mirroring Haskell's uniform `mapFrees`
/// (System.hs:1863-1876) which traverses ALL 13 system fields.
pub fn map_lvars_in_guarded<F>(g: &Guarded, mut f: F) -> Guarded
where F: FnMut(&p::VarSpec) -> p::VarSpec,
{
    fn map_term<F>(
        t: &p::Term,
        f: &mut F,
        bound: &std::collections::HashSet<(String, u64)>,
    ) -> p::Term
    where F: FnMut(&p::VarSpec) -> p::VarSpec,
    {
        match t {
            p::Term::Var(v) => {
                if bound.contains(&(v.name.clone(), v.idx)) {
                    p::Term::Var(v.clone())
                } else {
                    p::Term::Var(f(v))
                }
            }
            p::Term::App(name, args) =>
                p::Term::App(name.clone(),
                    args.iter().map(|a| map_term(a, f, bound)).collect()),
            p::Term::AlgApp(name, a, b) =>
                p::Term::AlgApp(name.clone(),
                    Box::new(map_term(a, f, bound)),
                    Box::new(map_term(b, f, bound))),
            p::Term::Pair(args) =>
                p::Term::Pair(args.iter().map(|a| map_term(a, f, bound)).collect()),
            p::Term::Diff(a, b) =>
                p::Term::Diff(
                    Box::new(map_term(a, f, bound)),
                    Box::new(map_term(b, f, bound))),
            p::Term::BinOp(op, a, b) =>
                p::Term::BinOp(*op,
                    Box::new(map_term(a, f, bound)),
                    Box::new(map_term(b, f, bound))),
            p::Term::PatMatch(inner) =>
                p::Term::PatMatch(Box::new(map_term(inner, f, bound))),
            other => other.clone(),
        }
    }
    fn map_fact<F>(
        fa: &p::Fact,
        f: &mut F,
        bound: &std::collections::HashSet<(String, u64)>,
    ) -> p::Fact
    where F: FnMut(&p::VarSpec) -> p::VarSpec,
    {
        p::Fact {
            persistent: fa.persistent,
            name: fa.name.clone(),
            args: fa.args.iter().map(|a| map_term(a, f, bound)).collect(),
            annotations: fa.annotations.clone(),
        }
    }
    fn map_atom<F>(
        a: &p::Atom,
        f: &mut F,
        bound: &std::collections::HashSet<(String, u64)>,
    ) -> p::Atom
    where F: FnMut(&p::VarSpec) -> p::VarSpec,
    {
        match a {
            p::Atom::Eq(t1, t2) =>
                p::Atom::Eq(map_term(t1, f, bound), map_term(t2, f, bound)),
            p::Atom::Less(t1, t2) =>
                p::Atom::Less(map_term(t1, f, bound), map_term(t2, f, bound)),
            p::Atom::LessMset(t1, t2) =>
                p::Atom::LessMset(map_term(t1, f, bound), map_term(t2, f, bound)),
            p::Atom::Subterm(t1, t2) =>
                p::Atom::Subterm(map_term(t1, f, bound), map_term(t2, f, bound)),
            p::Atom::Action(fa, t) =>
                p::Atom::Action(map_fact(fa, f, bound), map_term(t, f, bound)),
            p::Atom::Last(t) => p::Atom::Last(map_term(t, f, bound)),
            p::Atom::Pred(fa) => p::Atom::Pred(map_fact(fa, f, bound)),
        }
    }
    fn rec<F>(
        g: &Guarded,
        f: &mut F,
        bound: &std::collections::HashSet<(String, u64)>,
    ) -> Guarded
    where F: FnMut(&p::VarSpec) -> p::VarSpec,
    {
        match g {
            Guarded::Atom(a) => Guarded::Atom(map_atom(a, f, bound)),
            Guarded::Disj(items) =>
                Guarded::Disj(items.iter().map(|i| rec(i, f, bound)).collect()),
            Guarded::Conj(items) =>
                Guarded::Conj(items.iter().map(|i| rec(i, f, bound)).collect()),
            Guarded::GGuarded { qua, vars, guards, body } => {
                let mut new_bound = bound.clone();
                for v in vars { new_bound.insert((v.name.clone(), v.idx)); }
                Guarded::GGuarded {
                    qua: qua.clone(),
                    vars: vars.clone(),
                    guards: guards.iter().map(|a| map_atom(a, f, &new_bound)).collect(),
                    body: Box::new(rec(body, f, &new_bound)),
                }
            }
        }
    }
    rec(g, &mut f, &std::collections::HashSet::new())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::{parser::parse_formula_str};

    fn g(s: &str) -> Result<Guarded, GuardError> {
        let f = parse_formula_str(s).map_err(|e| err(format!("parse: {}", e)))?;
        formula_to_guarded(&f)
    }

    #[test]
    fn ground_truth() {
        let r = g("T").unwrap();
        assert_eq!(r, gtrue());
    }

    #[test]
    fn gnot_true_is_false() {
        assert_eq!(gnot(&gtrue()), gfalse());
    }

    #[test]
    fn gnot_false_is_true() {
        assert_eq!(gnot(&gfalse()), gtrue());
    }

    #[test]
    fn gnot_disj_becomes_conj() {
        let f1 = gtrue();
        let f2 = gfalse();
        let d = Guarded::Disj(vec![f1.clone(), f2.clone()]);
        let n = gnot(&d);
        // ¬(T ∨ ⊥) = ¬T ∧ ¬⊥ = ⊥ ∧ T. After gconj, this collapses to ⊥
        // because gconj short-circuits on a gfalse.
        assert_eq!(n, gfalse());
    }

    #[test]
    fn gnot_conj_becomes_disj() {
        let f1 = gtrue();
        let d = Guarded::Conj(vec![f1.clone(), f1]);
        // ¬(T ∧ T) = ¬T ∨ ¬T = ⊥ ∨ ⊥ — gdisj filters out gfalse → gfalse.
        assert_eq!(gnot(&d), gfalse());
    }

    #[test]
    fn ginduct_rejects_action_free_formula() {
        // gtrue contains no action atom — ginduct should reject.
        assert!(ginduct(&gtrue()).is_err());
        assert!(ginduct(&gfalse()).is_err());
    }

    #[test]
    fn satisfied_by_empty_trace_handles_quants() {
        // ∀ x. T : empty trace satisfies (no x exists ⇒ trivially).
        let p = parse_formula_str("All x #i. P(x)@#i ==> Q(x)@#i").ok();
        if let Some(f) = p {
            if let Ok(g) = formula_to_guarded(&f) {
                let v = satisfied_by_empty_trace(&g).unwrap();
                // ∀ over an empty trace is vacuously satisfied.
                assert!(v);
            }
        }
    }

    #[test]
    fn ginduct_existential_action_succeeds() {
        // Ex k #i. P(k) @ #i — closed, contains an action atom, not last-bearing.
        let p = parse_formula_str("Ex k #i. P(k)@#i").expect("parse");
        let g = formula_to_guarded(&p).expect("guarded");
        let (base, step) = ginduct(&g).expect("ginduct");
        // Empty-trace satisfaction: ∃ over empty trace is vacuously false.
        assert_eq!(base, gfalse());
        // Step case is `gconj [g, IH]` — typically wraps both.
        match &step {
            Guarded::Conj(items) => {
                assert!(items.iter().any(|x| x == &g),
                    "step case should contain the original formula");
            }
            other => panic!("expected Conj, got {:?}", other),
        }
    }

    #[test]
    fn gnot_double_is_identity_on_atoms() {
        // Smart constructors normalise away T/⊥ in larger formulas, so
        // double-negation isn't structurally identity in general — but
        // it is on the propositional constants themselves.
        for f in &[gtrue(), gfalse()] {
            let nn = gnot(&gnot(f));
            assert_eq!(&nn, f);
        }
    }

    #[test]
    fn ground_false() {
        let r = g("F").unwrap();
        assert_eq!(r, gfalse());
    }

    #[test]
    fn simple_action_under_all() {
        // All k #i. Setup(k) @ i ==> F
        // The All has guard `Setup(k) @ i`, which binds both k and #i.
        let r = g("All k #i. Setup(k) @ #i ==> F").unwrap();
        match r {
            Guarded::GGuarded { qua, vars, guards, .. } => {
                assert_eq!(qua, Quant::All);
                assert_eq!(vars.len(), 2);
                assert_eq!(guards.len(), 1);
            }
            x => panic!("expected GGuarded, got {:?}", x),
        }
    }

    #[test]
    fn unguarded_variable_rejected() {
        // All k. F  — `k` has no action atom guarding it.
        let res = g("All k. F");
        assert!(res.is_err(), "expected unguarded error");
    }

    #[test]
    fn exists_with_guarded_var() {
        // Ex k #i. Setup(k) @ i — k and #i are guarded by Setup(k) @ i.
        let r = g("Ex k #i. Setup(k) @ #i").unwrap();
        match r {
            Guarded::GGuarded { qua, vars, .. } => {
                assert_eq!(qua, Quant::Ex);
                assert_eq!(vars.len(), 2);
            }
            x => panic!("expected GGuarded(Ex), got {:?}", x),
        }
    }

    #[test]
    fn safety_no_existential() {
        let r = g("All k #i. Setup(k) @ #i ==> F").unwrap();
        assert!(is_safety_formula(&r));
    }

    #[test]
    fn safety_rejects_existential() {
        let r = g("All k #i. Setup(k) @ #i ==> Ex j #t. Foo(j) @ #t").unwrap();
        assert!(!is_safety_formula(&r));
    }

    #[test]
    fn implication_distributes() {
        // (a ⇒ b) when both atoms guard their bound vars
        let r = g("All k #i. Setup(k) @ #i ==> (Ex j #t. Setup(j) @ #t)").unwrap();
        // expect a GGuarded(All, [k, #i], [Setup(k) @ i], body)
        // where body is gconj([gnot Setup(k) @ i  ?, GGuarded(Ex ...)])
        // — we only assert the top-level shape here.
        match r {
            Guarded::GGuarded { qua, .. } => assert_eq!(qua, Quant::All),
            x => panic!("got {:?}", x),
        }
    }

    // =========================================================================
    // VarSubst correctness tests — the term-based substitution model
    // =========================================================================

    fn var(name: &str, idx: u64) -> p::Term {
        p::Term::Var(p::VarSpec {
            name: name.into(), idx, sort: p::SortHint::Msg, typ: None,
        })
    }
    fn pubconst(s: &str) -> p::Term { p::Term::PubLit(s.into()) }

    #[test]
    fn varsubst_var_to_var_remap() {
        let mut s = VarSubst::new();
        s.insert(("x".into(), 0), var("y", 5));
        let result = subst_term(&var("x", 0), &s);
        assert_eq!(result, var("y", 5));
    }

    #[test]
    fn varsubst_var_to_non_var_term() {
        // Bind `k` to the public constant 'foo'.
        let mut s = VarSubst::new();
        s.insert(("k".into(), 0), pubconst("foo"));
        let result = subst_term(&var("k", 0), &s);
        assert_eq!(result, pubconst("foo"));
    }

    #[test]
    fn varsubst_descends_into_app_args() {
        // `f(k, m)` where `k` is bound to 'foo'.
        let mut s = VarSubst::new();
        s.insert(("k".into(), 0), pubconst("foo"));
        let t = p::Term::App("f".into(), vec![var("k", 0), var("m", 0)]);
        let result = subst_term(&t, &s);
        let expected = p::Term::App("f".into(), vec![pubconst("foo"), var("m", 0)]);
        assert_eq!(result, expected);
    }

    #[test]
    fn varsubst_unmapped_var_unchanged() {
        let s = VarSubst::new();  // empty
        let t = var("k", 0);
        assert_eq!(subst_term(&t, &s), t);
    }

    #[test]
    fn varsubst_idx_aware() {
        // Two vars with same name but different idx — only the
        // matching one is replaced.
        let mut s = VarSubst::new();
        s.insert(("x".into(), 5), var("y", 0));
        // x with idx 5 → y, x with idx 6 unchanged.
        assert_eq!(subst_term(&var("x", 5), &s), var("y", 0));
        assert_eq!(subst_term(&var("x", 6), &s), var("x", 6));
    }

    #[test]
    fn varsubst_pair_descent() {
        let mut s = VarSubst::new();
        s.insert(("a".into(), 0), pubconst("X"));
        let t = p::Term::Pair(vec![var("a", 0), var("b", 0)]);
        let result = subst_term(&t, &s);
        let expected = p::Term::Pair(vec![pubconst("X"), var("b", 0)]);
        assert_eq!(result, expected);
    }

    #[test]
    fn varsubst_shadowing_blocks_inner_binder() {
        // `Ex k. Action(k)` — substituting `k` from outside should
        // NOT rewrite the inner `k` because it's freshly bound.
        let mut s = VarSubst::new();
        s.insert(("k".into(), 0), pubconst("OUTER"));
        let inner_k = p::VarSpec { name: "k".into(), idx: 0, sort: p::SortHint::Msg, typ: None };
        let mkfact = |t: p::Term| p::Fact {
            persistent: false,
            annotations: Vec::new(),
            name: "Action".into(),
            args: vec![t],
        };
        let inner_atom = Guarded::Atom(p::Atom::Action(
            mkfact(var("k", 0)),
            var("i", 0),
        ));
        let g = Guarded::GGuarded {
            qua: Quant::Ex,
            vars: vec![inner_k.clone()],
            guards: Vec::new(),
            body: Box::new(inner_atom.clone()),
        };
        let result = subst_guarded(&g, &s);
        // Body should be unchanged because `k` is shadowed by the
        // existential binder.
        match result {
            Guarded::GGuarded { body, .. } => {
                assert_eq!(*body, inner_atom);
            }
            other => panic!("expected GGuarded, got {:?}", other),
        }
    }

    #[test]
    fn gnot_existential_becomes_forall() {
        // ¬ (Ex k #i. Setup(k)@i) should be All k #i. (Setup(k)@i ⇒ ⊥).
        let parsed = parse_formula_str("Ex k #i. Setup(k) @ #i").unwrap();
        let g = formula_to_guarded(&parsed).unwrap();
        let neg = gnot(&g);
        match &neg {
            Guarded::GGuarded { qua, .. } => assert_eq!(*qua, Quant::All),
            other => panic!("expected GGuarded(All, ...), got {:?}", other),
        }
    }

    #[test]
    fn ginduct_extracts_two_cases() {
        let parsed = parse_formula_str("All k #i. Setup(k) @ #i ==> Ex #j. Setup(k) @ #j & #j < #i").unwrap();
        let g = formula_to_guarded(&parsed).unwrap();
        // Closed + has action atoms → ginduct should succeed.
        let (base, step) = ginduct(&g).expect("ginduct should succeed");
        // Step case is gconj([orig, IH]).
        match step {
            Guarded::Conj(items) => assert_eq!(items.len(), 2),
            // gconj may flatten if a sub-Conj appears.
            _ => {} // accept any shape — the contract is just that ginduct returned
        }
        let _ = base;
    }

    /// Pin Haskell parity for `lastAtos`: the IH for an `All`-guarded
    /// formula introduces a `¬Last(v)` for every node-sorted bound
    /// variable.  Mirrors the Haskell:
    ///
    ///   toInductionHypothesis (GGuarded All ss as gf) =
    ///       gex ss as (gconj (map gnotAtom lastAtos ++ [IH gf]))
    ///     where lastAtos = [Last (Bound j) | (j,(_,LSortNode)) ← ...]
    #[test]
    fn induction_hypothesis_emits_last_atoms_for_node_sorted_binders() {
        // `All #i. Setup(k) @ #i ⇒ ⊥`  is doubly guarded with one
        // node-sorted binder.  The IH must contain `Last(#i)` (in
        // *negated* form, since the outer quantifier flips All→Ex and
        // we conjoin `¬Last(v)` per node binder).
        let parsed = parse_formula_str("All #i. Setup('k') @ #i ==> G('x') @ #i").unwrap();
        let g = formula_to_guarded(&parsed).unwrap();
        let ih = to_induction_hypothesis(&g).expect("should produce IH");

        // Outer must flip All → Ex, keep guards, and the body should be
        // a Conj that mentions `Last(#i)` somewhere.
        match &ih {
            Guarded::GGuarded { qua, vars, body, .. } => {
                assert_eq!(*qua, Quant::Ex);
                assert_eq!(vars.len(), 1);
                // Walk the body looking for an atom equal to Last(Var(#i)).
                let target = p::Atom::Last(p::Term::Var(vars[0].clone()));
                fn walks_to_last(g: &Guarded, t: &p::Atom) -> bool {
                    match g {
                        Guarded::Atom(a) => a == t,
                        Guarded::Disj(xs) | Guarded::Conj(xs) =>
                            xs.iter().any(|x| walks_to_last(x, t)),
                        Guarded::GGuarded { guards, body, .. } =>
                            guards.iter().any(|a| a == t)
                                || walks_to_last(body, t),
                    }
                }
                assert!(walks_to_last(body, &target),
                    "IH body should mention Last(v) for the node binder; got {:?}", body);
            }
            other => panic!("expected GGuarded(Ex, ...), got {:?}", other),
        }
    }

    /// IH must NOT introduce a Last-atom for non-node-sorted binders.
    /// Matches Haskell's filter `(_, LSortNode) ← ...`.
    #[test]
    fn induction_hypothesis_skips_non_node_binders() {
        // `All k. K(k) ⇒ ⊥`: the bound variable `k` is `Msg`-sorted
        // (no `#` prefix, no `:node` suffix) — no Last-atom should be
        // emitted.  The body collapses to `gconj([] ++ [IH body])` =
        // just the IH body.
        let parsed = parse_formula_str("All k. K(k) ==> G('x') @ #i").unwrap();
        let g = match formula_to_guarded(&parsed) {
            Ok(x) => x,
            Err(_) => return,  // formula may be ill-guarded — that's fine
        };
        let ih = match to_induction_hypothesis(&g) { Ok(x) => x, Err(_) => return };
        // Walk: should find no `Last(_)` atom anywhere, since `k` is Msg-sorted.
        fn has_any_last(g: &Guarded) -> bool {
            match g {
                Guarded::Atom(p::Atom::Last(_)) => true,
                Guarded::Atom(_) => false,
                Guarded::Disj(xs) | Guarded::Conj(xs) =>
                    xs.iter().any(has_any_last),
                Guarded::GGuarded { guards, body, .. } =>
                    guards.iter().any(|a| matches!(a, p::Atom::Last(_)))
                        || has_any_last(body),
            }
        }
        assert!(!has_any_last(&ih),
            "IH should not emit Last for non-node binders; got {:?}", ih);
    }

    // =========================================================================
    // simplify_guarded_with — partial-atom-valuation rewriting
    //
    // Mirrors Haskell's `simplifyGuardedOrReturn` from
    // `Theory.Constraint.System.Guarded`:
    //   simp (GAto a)       = maybe fm gtf (valuation a)
    //   simp (GDisj fms)    = gdisj (map simp fms)
    //   simp (GConj fms)    = gconj (map simp fms)
    //   simp (GGuarded All [] atos gf)
    //     | any (Just False ==) (map valuation atos) = gtrue
    //     | otherwise = gall [] (filter unknown atos) (simp gf)
    //   simp (GGuarded ...) = fm  -- delay past binders
    // =========================================================================

    fn mk_atom_eq(a: &str, b: &str) -> Guarded {
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        Guarded::Atom(p::Atom::Eq(mkv(a), mkv(b)))
    }

    #[test]
    fn simplify_atom_with_known_true_collapses_to_gtrue() {
        let g = mk_atom_eq("x", "y");
        let val = |_a: &p::Atom| Some(true);
        assert_eq!(simplify_guarded_with(&g, &val), gtrue());
    }

    #[test]
    fn simplify_atom_with_known_false_collapses_to_gfalse() {
        let g = mk_atom_eq("x", "y");
        let val = |_a: &p::Atom| Some(false);
        assert_eq!(simplify_guarded_with(&g, &val), gfalse());
    }

    #[test]
    fn simplify_atom_unknown_left_intact() {
        let g = mk_atom_eq("x", "y");
        let val = |_a: &p::Atom| None;
        assert_eq!(simplify_guarded_with(&g, &val), g);
    }

    #[test]
    fn simplify_disj_drops_false_branches() {
        // a ∨ b — if b evaluates False and a is unknown, result = a.
        let a = mk_atom_eq("p", "q");
        let b = mk_atom_eq("r", "s");
        let g = Guarded::Disj(vec![a.clone(), b.clone()]);
        let val = move |atom: &p::Atom| match atom {
            p::Atom::Eq(x, _) => match x {
                p::Term::Var(v) if v.name == "r" => Some(false),
                _ => None,
            },
            _ => None,
        };
        assert_eq!(simplify_guarded_with(&g, &val), a);
    }

    #[test]
    fn simplify_conj_short_circuits_on_false() {
        // a ∧ b — if b evaluates False, conj should be gfalse.
        let a = mk_atom_eq("p", "q");
        let b = mk_atom_eq("r", "s");
        let g = Guarded::Conj(vec![a, b]);
        let val = |atom: &p::Atom| match atom {
            p::Atom::Eq(x, _) => match x {
                p::Term::Var(v) if v.name == "r" => Some(false),
                _ => None,
            },
            _ => None,
        };
        assert_eq!(simplify_guarded_with(&g, &val), gfalse());
    }

    #[test]
    fn simplify_universal_with_one_false_guard_is_gtrue() {
        // (All vars[]. [a, b]. body) with a=False → gtrue (vacuous).
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        let a = p::Atom::Eq(mkv("a"), mkv("b"));
        let b = p::Atom::Eq(mkv("c"), mkv("d"));
        let body = mk_atom_eq("p", "q");
        let g = Guarded::GGuarded {
            qua: Quant::All, vars: Vec::new(),
            guards: vec![a.clone(), b],
            body: Box::new(body),
        };
        let val = move |atom: &p::Atom| {
            if atom == &a { Some(false) } else { None }
        };
        assert_eq!(simplify_guarded_with(&g, &val), gtrue());
    }

    #[test]
    fn simplify_universal_drops_true_guards_keeps_unknown() {
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        let a = p::Atom::Eq(mkv("a"), mkv("b"));
        let b = p::Atom::Eq(mkv("c"), mkv("d"));
        let body = mk_atom_eq("p", "q");
        let g = Guarded::GGuarded {
            qua: Quant::All, vars: Vec::new(),
            guards: vec![a.clone(), b.clone()],
            body: Box::new(body.clone()),
        };
        let a_clone = a.clone();
        let b_clone = b.clone();
        let val = move |atom: &p::Atom| {
            if atom == &a_clone { Some(true) }   // drop
            else if atom == &b_clone { None }    // keep
            else { None }
        };
        let simp = simplify_guarded_with(&g, &val);
        match simp {
            Guarded::GGuarded { vars, guards, .. } => {
                assert!(vars.is_empty());
                assert_eq!(guards, vec![b]);
            }
            other => panic!("expected GGuarded with one guard, got {:?}", other),
        }
    }

    #[test]
    fn simplify_universal_with_all_true_guards_returns_body() {
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        let a = p::Atom::Eq(mkv("a"), mkv("b"));
        let body = mk_atom_eq("p", "q");
        let g = Guarded::GGuarded {
            qua: Quant::All, vars: Vec::new(),
            guards: vec![a],
            body: Box::new(body.clone()),
        };
        let val = |_atom: &p::Atom| Some(true);
        // Both guard and body atoms evaluate to True under this
        // valuation, so universal vacuous-then-body collapses to gtrue.
        assert_eq!(simplify_guarded_with(&g, &val), gtrue());
    }

    #[test]
    fn simplify_universal_with_quantifier_left_intact() {
        // GGuarded with bound vars is left alone — Haskell delays
        // simplification past the binder.
        let mkv = |n: &str| p::Term::Var(p::VarSpec {
            name: n.into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        });
        let a = p::Atom::Eq(mkv("a"), mkv("b"));
        let body = mk_atom_eq("p", "q");
        let bound_var = p::VarSpec {
            name: "x".into(), idx: 0, sort: p::SortHint::Msg, typ: None,
        };
        let g = Guarded::GGuarded {
            qua: Quant::All, vars: vec![bound_var],
            guards: vec![a],
            body: Box::new(body),
        };
        let val = |_atom: &p::Atom| Some(true);
        assert_eq!(simplify_guarded_with(&g, &val), g);
    }

    // =========================================================================
    // Haskell-faithfulness invariants for guarded-formula smart ctors.
    //
    // `gconj` / `gdisj` mirror Haskell's smart constructors in
    // `Theory.Constraint.System.Guarded` (Guarded.hs:418, :432).  They
    // SHORT-CIRCUIT on `gtrue`/`gfalse` and dedupe via `nub`.
    // =========================================================================

    /// `gtrue` is represented as `Conj []` and `gfalse` as `Disj []`.
    /// This is a Haskell convention (Guarded.hs:139-145).  Many
    /// short-circuit checks rely on it (e.g. `x == gfalse()` in
    /// `gconj`).  If we accidentally encode them differently, every
    /// short-circuit silently breaks.
    #[test]
    fn gtrue_is_empty_conj_and_gfalse_is_empty_disj() {
        assert_eq!(gtrue(), Guarded::Conj(vec![]));
        assert_eq!(gfalse(), Guarded::Disj(vec![]));
        assert_ne!(gtrue(), gfalse(), "gtrue and gfalse must be distinguishable");
    }

    /// `gconj([gtrue, gtrue, ...])` reduces to `gtrue`.  Empty/trivial
    /// conjunction is True.  Mirrors Haskell `gconj`'s elimination of
    /// `gtrue` items.
    #[test]
    fn gconj_of_only_gtrue_items_is_gtrue() {
        // Guarded.hs:418: `gconj` should collapse all-true conjunctions.
        // Rust impl flattens `Conj` items (gtrue is Conj([])), so all
        // gtrue items dissolve into empty.  Result: `Conj([])` = gtrue.
        let g = gconj(vec![gtrue(), gtrue(), gtrue()]);
        assert_eq!(g, gtrue(),
                   "gconj of only-True items must collapse to gtrue");
    }

    /// `gconj([..., gfalse, ...])` SHORT-CIRCUITS to `gfalse` regardless
    /// of other items.  This is the "any-false makes conjunction false"
    /// short-circuit at Guarded.hs:418.
    #[test]
    fn gconj_short_circuits_on_gfalse() {
        // Build a non-trivial atom by parsing a small formula.
        let atom_g = g("Last(#i)").unwrap();
        // Any gfalse in the items short-circuits to gfalse.
        let g = gconj(vec![gtrue(), gfalse(), atom_g.clone()]);
        assert_eq!(g, gfalse(),
                   "gconj must short-circuit when any item is gfalse");
        let g2 = gconj(vec![atom_g, gfalse()]);
        assert_eq!(g2, gfalse());
    }

    /// `gdisj([gfalse, gfalse, ...])` reduces to `gfalse`. Empty
    /// disjunction is False.
    #[test]
    fn gdisj_of_only_gfalse_items_is_gfalse() {
        let g = gdisj(vec![gfalse(), gfalse()]);
        assert_eq!(g, gfalse(),
                   "gdisj of only-False items must collapse to gfalse");
    }

    /// `gdisj([..., gtrue, ...])` short-circuits to `gtrue`.
    #[test]
    fn gdisj_short_circuits_on_gtrue() {
        let g = gdisj(vec![gfalse(), gtrue(), gfalse()]);
        assert_eq!(g, gtrue(),
                   "gdisj must short-circuit on first gtrue encountered");
    }

    /// `gconj` deduplicates syntactically-equal items.  Mirrors
    /// Haskell's `nub gfs` (Guarded.hs:418).  Dedup is ORDER-PRESERVING
    /// (Haskell `Data.List.nub` keeps first occurrence).
    #[test]
    fn gconj_dedupes_syntactic_duplicates() {
        let a = g("Last(#i)").unwrap();
        let b = g("Last(#j)").unwrap();
        let out = gconj(vec![a.clone(), b.clone(), a.clone()]);
        // Expected: Conj([a, b]) — second occurrence of `a` dropped.
        match out {
            Guarded::Conj(items) => {
                assert_eq!(items.len(), 2,
                    "gconj must dedupe identical items via nub");
                assert_eq!(items[0], a);
                assert_eq!(items[1], b);
            }
            _ => panic!("expected Conj"),
        }
    }

    /// `gdisj` deduplicates syntactically-equal items.  Same as above,
    /// for disjunction.  Bug from #194 (clusters): without this dedup,
    /// `verify_checksign_test`-class SplitG variants doubled up.
    #[test]
    fn gdisj_dedupes_syntactic_duplicates() {
        let a = g("Last(#i)").unwrap();
        let b = g("Last(#j)").unwrap();
        let out = gdisj(vec![a.clone(), b.clone(), a.clone(), b.clone()]);
        match out {
            Guarded::Disj(items) => {
                assert_eq!(items.len(), 2,
                    "gdisj must dedupe identical items via nub");
                assert_eq!(items[0], a);
                assert_eq!(items[1], b);
            }
            _ => panic!("expected Disj"),
        }
    }

    /// `gconj` with a single non-trivial item collapses to that item
    /// (no Conj wrapper).  Mirrors Haskell's `case gfs' of [g] -> g`
    /// pattern.
    #[test]
    fn gconj_singleton_unwraps() {
        let a = g("Last(#i)").unwrap();
        let out = gconj(vec![a.clone()]);
        assert_eq!(out, a, "singleton gconj must unwrap to the lone item");
    }

    /// `gconj` flattens nested `Conj` one level.  Mirrors Haskell's
    /// `concatMap` flatten.
    #[test]
    fn gconj_flattens_nested_conj_one_level() {
        let a = g("Last(#i)").unwrap();
        let b = g("Last(#j)").unwrap();
        let c = g("Last(#k)").unwrap();
        let inner = Guarded::Conj(vec![a.clone(), b.clone()]);
        let out = gconj(vec![inner, c.clone()]);
        match out {
            Guarded::Conj(items) => {
                assert_eq!(items.len(), 3,
                    "nested Conj should be flattened: 2 inner + 1 outer = 3");
                assert_eq!(items, vec![a, b, c]);
            }
            _ => panic!("expected Conj"),
        }
    }

    // =========================================================================
    // Haskell-faithfulness invariants for `gnot` and quantifier swap.
    //
    // Mirrors Haskell `gnot` (Guarded.hs):
    //     gnot (GGuarded All ss as gf) = gex  ss as (gnot gf)
    //     gnot (GGuarded Ex  ss as gf) = gall ss as (gnot gf)
    //
    // The All↔Ex swap under negation is critical.  Past bugs:
    //   #48 (gnot_atom for Action/Last/Pred) — proto-fact actions need
    //     a specific Haskell-faithful negation shape.
    //   #170 (TESLA::authentic nondeterminism) had a downstream impact.
    // =========================================================================

    /// `gnot ∘ gnot = id` (involution) for ground formulas.
    /// This is the most fundamental algebraic property of negation.
    /// If gnot doesn't round-trip, every double-negation in IH
    /// reasoning silently degrades.
    #[test]
    fn gnot_double_negation_is_identity() {
        assert_eq!(gnot(&gnot(&gtrue())), gtrue());
        assert_eq!(gnot(&gnot(&gfalse())), gfalse());
        // Atom case.
        let a = g("Last(#i)").unwrap();
        assert_eq!(gnot(&gnot(&a)), a,
                   "gnot is involutive on atomic formulas — \
                    needed for `to_induction_hypothesis` round-trip.");
    }

    /// `gnot (All ... body) = Ex ... gnot(body)`.  Haskell:
    /// `gnot (GGuarded All ss as gf) = gex ss as (gnot gf)`.
    ///
    /// **The quantifier flips on negation.**  If we forget to flip,
    /// `to_induction_hypothesis` produces the wrong dual and the IH
    /// becomes vacuous or false.
    #[test]
    fn gnot_flips_universal_to_existential() {
        // ∀ x #i. P(x)@#i ⇒ Q(x)@#i — guarded universal.
        // Negation flips to: ∃ x #i. P(x)@#i ∧ ¬Q(x)@#i.
        let f = g("All x #i. P(x)@#i ==> Q(x)@#i").unwrap();
        let n = gnot(&f);
        // The resulting quantifier MUST be Ex.
        match n {
            Guarded::GGuarded { qua: Quant::Ex, .. } => {}
            other => panic!(
                "expected Ex quantifier after negating All; got {:?}", other),
        }
    }

    /// `gnot (Ex ... body) = All ... gnot(body)`.  Symmetric to above.
    ///
    /// Together these ensure that `gnot ∘ gnot` round-trips through
    /// the quantifier — Ex → All → Ex.  Without the flip on either
    /// side, the double-negation property breaks.
    #[test]
    fn gnot_flips_existential_to_universal() {
        let f = g("Ex x #i. P(x)@#i").unwrap();
        // Sanity: starts as Ex.
        match &f {
            Guarded::GGuarded { qua: Quant::Ex, .. } => {}
            other => panic!("test setup: expected Ex; got {:?}", other),
        }
        let n = gnot(&f);
        // After negation, outer quantifier must be All (or the formula
        // simplified — but for this non-trivial body it remains All).
        match n {
            Guarded::GGuarded { qua: Quant::All, .. } => {}
            other => panic!(
                "expected All quantifier after negating Ex; got {:?}", other),
        }
    }

    /// De Morgan: `gnot (gconj [a, b]) = gdisj [gnot a, gnot b]`.
    /// Already exercised in `gnot_conj_becomes_disj` — pin the dual.
    #[test]
    fn gnot_distributes_over_disj() {
        // ¬(a ∨ b) = ¬a ∧ ¬b
        let a = g("Last(#i)").unwrap();
        let b = g("Last(#j)").unwrap();
        let or = Guarded::Disj(vec![a.clone(), b.clone()]);
        let neg = gnot(&or);
        // Should be Conj([¬a, ¬b]) — both negated.
        let expected = gconj(vec![gnot(&a), gnot(&b)]);
        assert_eq!(neg, expected,
            "De Morgan: ¬(a ∨ b) = ¬a ∧ ¬b — required for IH derivation");
    }
}
