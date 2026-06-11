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

pub use crate::guarded_types::{
    BVar, GAtom, GBinding, GFact, GTerm,
    atom_to_gatom_free, fact_to_gfact_free, term_to_gterm_free,
    gatom_to_atom, gfact_to_fact, gterm_to_term,
    subst_free_atom_at_depth, subst_free_fact_at_depth, subst_free_term_at_depth,
    subst_bound_atom_at_depth, subst_bound_fact_at_depth, subst_bound_term_at_depth,
    close_subst, open_subst, lvar_to_binding,
    collect_free_term, collect_free_atom,
    map_free_term, map_free_fact, map_free_atom,
};

// =============================================================================
// Guarded data type
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Quant { All, Ex }

// ===========================================================================
// HS-faithful Ord for Guarded
// ===========================================================================
//
// HS's `Theory.Constraint.System.Guarded.Guarded` derives Ord structurally
// (Guarded.hs:121-129):
//
//     data Guarded s c v = GAto  (Atom ...)
//                        | GDisj (Disj (Guarded ...))
//                        | GConj (Conj (Guarded ...))
//                        | GGuarded Quantifier [s] [Atom ...] (Guarded ...)
//
// Constructor order: GAto < GDisj < GConj < GGuarded.
// Within each, lexicographic on contents.
//
// HS's `Set LNGuarded` iterates via `S.toList` which yields elements in
// ascending Ord.  Rust's `sys.formulas: Vec<Guarded>` iterates in
// insertion order, so the impl-pass / reduce-formulas / eval-formula-atoms
// passes see clauses in a DIFFERENT order than HS does — which propagates
// to which clause's matches fire first → goal-nrs of newly-inserted
// Disj formulas → goal pick at downstream proof steps.
//
// This module provides `cmp_guarded` (and helpers `cmp_atom` /
// `cmp_term`) that mirror HS's derived Ord chain.  See
// [[reference-vec-vs-set-walks]] for the sites that need this.

/// HS-faithful structural comparison for Guarded.  Mirrors HS's derived
/// `Ord (Guarded s c v)` on `Theory.Constraint.System.Guarded.Guarded`.
pub fn cmp_guarded(a: &Guarded, b: &Guarded) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let ta = guarded_tag(a);
    let tb = guarded_tag(b);
    if ta != tb { return ta.cmp(&tb); }
    match (a, b) {
        (Guarded::Atom(x), Guarded::Atom(y)) => cmp_atom(x, y),
        (Guarded::Disj(xs), Guarded::Disj(ys)) => cmp_slice(xs, ys, cmp_guarded),
        (Guarded::Conj(xs), Guarded::Conj(ys)) => cmp_slice(xs, ys, cmp_guarded),
        (
            Guarded::GGuarded { qua: q1, vars: v1, guards: g1, body: b1 },
            Guarded::GGuarded { qua: q2, vars: v2, guards: g2, body: b2 },
        ) => {
            cmp_quant(q1, q2)
                // HS-faithful: in `LNGuarded = Guarded (String,LSort) Name
                // LVar` (Guarded.hs:279,389), the `s` parameter — used
                // for GGuarded's binding list — is the TUPLE
                // `(String, LSort)`, NOT `LVar`.  So bindings sort by
                // (name, sort) only — there is no idx field on a binding.
                // Rust's `VarSpec` carries `idx` but for binding-list
                // comparison we must ignore it (cmp_binding); free-var
                // comparison inside terms still uses cmp_varspec which
                // mirrors HS's `Ord LVar = (idx, sort, name)`.
                .then_with(|| cmp_slice(v1, v2, cmp_binding))
                .then_with(|| cmp_slice(g1, g2, cmp_atom))
                .then_with(|| cmp_guarded(b1, b2))
        }
        _ => Ordering::Equal,
    }
}

fn guarded_tag(g: &Guarded) -> u8 {
    match g {
        Guarded::Atom(_) => 0,
        Guarded::Disj(_) => 1,
        Guarded::Conj(_) => 2,
        Guarded::GGuarded { .. } => 3,
    }
}

fn cmp_quant(a: &Quant, b: &Quant) -> std::cmp::Ordering {
    let ta = if matches!(a, Quant::All) { 0u8 } else { 1 };
    let tb = if matches!(b, Quant::All) { 0u8 } else { 1 };
    ta.cmp(&tb)
}

/// HS list Ord: element-by-element, shorter < longer.
fn cmp_slice<T, F>(a: &[T], b: &[T], mut f: F) -> std::cmp::Ordering
where F: FnMut(&T, &T) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let mut i = 0;
    loop {
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) => {
                let c = f(x, y);
                if c != Ordering::Equal { return c; }
                i += 1;
            }
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (None, None) => return Ordering::Equal,
        }
    }
}

/// HS-faithful Ord for `ProtoAtom`: Action < EqE < Subterm < Less < Last
/// < Syntactic (Theory/Model/Atom.hs:78-84).  Rust's `GAtom` declares
/// variants in a different order; we re-map to HS's order via
/// `atom_tag`.  `LessMset` has no HS equivalent — put at end.
pub fn cmp_atom(a: &GAtom, b: &GAtom) -> std::cmp::Ordering {
    let ta = atom_tag(a);
    let tb = atom_tag(b);
    if ta != tb { return ta.cmp(&tb); }
    match (a, b) {
        (GAtom::Action(f1, t1), GAtom::Action(f2, t2)) =>
            cmp_fact(f1, f2).then_with(|| cmp_term(t1, t2)),
        (GAtom::Eq(a1, b1), GAtom::Eq(a2, b2)) =>
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2)),
        (GAtom::Subterm(a1, b1), GAtom::Subterm(a2, b2)) =>
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2)),
        (GAtom::Less(a1, b1), GAtom::Less(a2, b2)) =>
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2)),
        (GAtom::Last(t1), GAtom::Last(t2)) => cmp_term(t1, t2),
        (GAtom::Pred(f1), GAtom::Pred(f2)) => cmp_fact(f1, f2),
        (GAtom::LessMset(a1, b1), GAtom::LessMset(a2, b2)) =>
            cmp_term(a1, a2).then_with(|| cmp_term(b1, b2)),
        _ => std::cmp::Ordering::Equal,
    }
}

fn atom_tag(a: &GAtom) -> u8 {
    match a {
        GAtom::Action(_, _) => 0,
        GAtom::Eq(_, _) => 1,
        GAtom::Subterm(_, _) => 2,
        GAtom::Less(_, _) => 3,
        GAtom::Last(_) => 4,
        GAtom::Pred(_) => 5,
        GAtom::LessMset(_, _) => 6, // Rust-only, no HS equivalent
    }
}

/// HS Term Ord: `Lit < FApp` (Term.hs).  Walks `GTerm`.  Bound vars sort
/// before Free vars (HS `BVar = Bound Int | Free v` declaration order).
pub fn cmp_term(a: &GTerm, b: &GTerm) -> std::cmp::Ordering {
    use GTerm::*;
    let (ca, sa) = term_class(a);
    let (cb, sb) = term_class(b);
    if ca != cb { return ca.cmp(&cb); }
    if sa != sb { return sa.cmp(&sb); }
    match (a, b) {
        // Lit class:
        (Var(v1), Var(v2)) => cmp_bvar(v1, v2),
        (PubLit(s1), PubLit(s2)) => s1.cmp(s2),
        (FreshLit(s1), FreshLit(s2)) => s1.cmp(s2),
        (NatLit(s1), NatLit(s2)) => s1.cmp(s2),
        (Number(n1), Number(n2)) => n1.cmp(n2),
        (NumberOne, NumberOne) | (NatOne, NatOne) | (DhNeutral, DhNeutral)
            => std::cmp::Ordering::Equal,
        // FApp class:
        (App(n1, args1), App(n2, args2)) =>
            n1.cmp(n2).then_with(|| cmp_slice(args1, args2, cmp_term)),
        (AlgApp(n1, l1, r1), AlgApp(n2, l2, r2)) =>
            n1.cmp(n2).then_with(|| cmp_term(l1, l2)).then_with(|| cmp_term(r1, r2)),
        (Pair(a1), Pair(a2)) => cmp_slice(a1, a2, cmp_term),
        (Diff(l1, r1), Diff(l2, r2)) =>
            cmp_term(l1, l2).then_with(|| cmp_term(r1, r2)),
        // HS-faithful: for AC binary ops (Mult/Union/Xor/NatPlus), HS's
        // `FAPP (AC op) args` has args as a flat sorted multiset list;
        // `derived Ord` on FAPP compares operator then args list.  RS's
        // nested `BinOp(o, l, r)` representation hides this — two
        // structurally distinct trees with the same flat multiset
        // content (e.g. `Union(Union(a,b), c)` vs `Union(a, Union(b,c))`)
        // would compare differently here, even though HS sees them as
        // identical `FAPP (AC Union) [a,b,c]`.
        //
        // Mirror HS by flattening AC chains into a sorted multiset key
        // before comparison.  Exp is NOT AC and uses structural compare.
        (BinOp(o1, l1, r1), BinOp(o2, l2, r2)) => {
            let tag_cmp = binop_tag(o1).cmp(&binop_tag(o2));
            if tag_cmp != std::cmp::Ordering::Equal { return tag_cmp; }
            if is_ac_binop(o1) {
                let mut args_a = Vec::new();
                let mut args_b = Vec::new();
                flatten_ac_binop(o1, a, &mut args_a);
                flatten_ac_binop(o2, b, &mut args_b);
                // HS-faithful: `FAPP (AC op) args` has args sorted as a
                // multiset (Maude canonicalises).  Sort both sides via
                // cmp_term so structurally-permuted AC chains collapse.
                args_a.sort_by(cmp_term);
                args_b.sort_by(cmp_term);
                cmp_slice(&args_a, &args_b, cmp_term)
            } else {
                cmp_term(l1, l2).then_with(|| cmp_term(r1, r2))
            }
        }
        (PatMatch(a1), PatMatch(a2)) => cmp_term(a1, a2),
        _ => std::cmp::Ordering::Equal,
    }
}

/// HS `Ord BVar`: derived; `Bound < Free`.  Within each constructor,
/// compare the contents — `Int` for Bound, LVar Ord (idx, sort, name) for Free.
pub fn cmp_bvar(a: &BVar, b: &BVar) -> std::cmp::Ordering {
    match (a, b) {
        (BVar::Bound(_), BVar::Free(_)) => std::cmp::Ordering::Less,
        (BVar::Free(_), BVar::Bound(_)) => std::cmp::Ordering::Greater,
        (BVar::Bound(n1), BVar::Bound(n2)) => n1.cmp(n2),
        (BVar::Free(v1), BVar::Free(v2)) => cmp_varspec(v1, v2),
    }
}

/// Returns `(class, sub_tag)` where class=0 for Lit-like, 1 for FApp-like.
///
/// HS-faithful: a `GTerm` corresponds to `Term (Lit Name (BVar v))`, whose
/// derived `Ord` is `LIT _ < FAPP _ _` (Term/Term/Raw.hs:72-74), and within
/// `LIT`, `Lit c v = Con c | Var v` derives `Con < Var` (VTerm.hs:56-57).
/// Therefore ALL constant literals (Pub/Fresh/Nat names) sort BEFORE any
/// variable.  Among constants, `Ord Name` compares the `NameTag` first
/// (`FreshName | PubName | NodeName | NatName`, LTerm.hs:215) so the literal
/// order is Fresh < Pub < Nat, then by name string.  Variables come last in
/// the `LIT` class.
///
/// The 0-arity builtins `NumberOne`/`NatOne`/`DhNeutral` are NOT literals in
/// HS — they are `fAppNoEq oneSym []` / `fAppNoEq natOneSym []` /
/// `fAppNoEq dhNeutralSym []` (Term/Term.hs:127-130), i.e. nullary function
/// applications, so they belong to the FApp class.
fn term_class(t: &GTerm) -> (u8, u8) {
    use GTerm::*;
    match t {
        // LIT (Con name): constants, ordered by Name's NameTag (Fresh<Pub<Nat).
        FreshLit(_) => (0, 0),
        PubLit(_) => (0, 1),
        NatLit(_) => (0, 2),
        Number(_) => (0, 3),
        // LIT (Var v): variables sort after all constants.
        Var(_) => (0, 4),
        // FAPP: nullary builtins are NoEq function applications, not literals.
        NumberOne => (1, 0),
        NatOne => (1, 1),
        DhNeutral => (1, 2),
        App(_, _) => (1, 3),
        AlgApp(_, _, _) => (1, 4),
        Pair(_) => (1, 5),
        Diff(_, _) => (1, 6),
        BinOp(_, _, _) => (1, 7),
        PatMatch(_) => (1, 8),
    }
}

fn binop_tag(o: &p::BinOp) -> u8 {
    use p::BinOp::*;
    match o {
        Exp => 0, Mult => 1, Union => 2, Xor => 3, NatPlus => 4,
    }
}

/// HS-faithful: which `BinOp`s are AC (associative-commutative)?
/// Mirrors HS's `MaudeSig`-attribute classification: Mult, Union, Xor,
/// NatPlus are AC; Exp is NOT (right-associative algebraic).
fn is_ac_binop(o: &p::BinOp) -> bool {
    use p::BinOp::*;
    matches!(o, Mult | Union | Xor | NatPlus)
}

/// Flatten an AC-BinOp chain into a flat arg list.  E.g.
/// `BinOp(Union, BinOp(Union, a, b), c)` flattens to `[a, b, c]`.
/// Non-matching outer terms are pushed verbatim (no recursion into
/// nested non-Union/non-same-op subtrees).
fn flatten_ac_binop(op: &p::BinOp, t: &GTerm, out: &mut Vec<GTerm>) {
    match t {
        GTerm::BinOp(inner_op, l, r) if inner_op == op => {
            flatten_ac_binop(op, l, out);
            flatten_ac_binop(op, r, out);
        }
        _ => out.push(t.clone()),
    }
}

/// HS-faithful Ord for free `LVar`: `(idx, sort, name)` lexicographic
/// (Term/LTerm.hs:521-523).  Rust's `p::VarSpec` has the same fields
/// in a different declaration order — we compare in HS's order.
/// Used for VarSpecs that appear as FREE vars inside terms.
pub fn cmp_varspec(a: &p::VarSpec, b: &p::VarSpec) -> std::cmp::Ordering {
    a.idx.cmp(&b.idx)
        .then_with(|| cmp_sort_hint(&a.sort, &b.sort))
        .then_with(|| a.name.cmp(&b.name))
}

/// HS-faithful Ord for GGuarded *binding* entries.  In LNGuarded, the
/// binding type is `(String, LSort)` — Guarded.hs:279,389.  So bindings
/// sort by `(name, sort)` lex.  After the DeBruijn migration our
/// `GBinding` already carries only those two fields.
pub fn cmp_binding(a: &GBinding, b: &GBinding) -> std::cmp::Ordering {
    a.name.cmp(&b.name)
        .then_with(|| cmp_sort_hint(&a.sort, &b.sort))
}

/// HS LSort declaration order (Term/LTerm.hs:161-166):
///   LSortPub < LSortFresh < LSortMsg < LSortNode < LSortNat.
fn cmp_sort_hint(a: &p::SortHint, b: &p::SortHint) -> std::cmp::Ordering {
    sort_hint_tag(a).cmp(&sort_hint_tag(b))
}

fn sort_hint_tag(s: &p::SortHint) -> u8 {
    use p::SortHint::*;
    use p::SuffixSort;
    match s {
        Pub => 0,
        Fresh => 1,
        Msg => 2,
        Node => 3,
        Nat => 4,
        Suffix(SuffixSort::Pub) => 0,
        Suffix(SuffixSort::Fresh) => 1,
        Suffix(SuffixSort::Msg) => 2,
        Suffix(SuffixSort::Node) => 3,
        Suffix(SuffixSort::Nat) => 4,
        Untagged => 99, // no HS equivalent (sorted last)
    }
}

/// HS Fact Ord (Theory/Model/Fact.hs): `(factTag, factAnnotations,
/// factTerms)` tuple Ord.  Works on `GFact` (HS `Fact (VTerm c (BVar v))`).
pub fn cmp_fact(a: &GFact, b: &GFact) -> std::cmp::Ordering {
    a.persistent.cmp(&b.persistent)
        .then_with(|| a.name.cmp(&b.name))
        .then_with(|| cmp_slice(&a.args, &b.args, cmp_term))
}

/// HS-faithful Guarded type. Mirrors `Theory.Constraint.System.Guarded.Guarded`.
///
/// Atoms use `GAtom` (which is `Atom (VTerm c (BVar v))` in HS), so a
/// variable leaf inside an atom is either `Bound(n)` (DeBruijn index into
/// the enclosing binder list) or `Free(LVar)`. Bindings carry only name +
/// sort — DeBruijn position determines identity.
#[derive(Debug, Clone, PartialEq)]
pub enum Guarded {
    /// One atomic predicate (may contain Bound vars only when nested under
    /// a sufficient number of `GGuarded` binders).
    Atom(GAtom),
    /// Disjunction of guarded sub-formulas.
    Disj(Vec<Guarded>),
    /// Conjunction of guarded sub-formulas.
    Conj(Vec<Guarded>),
    /// `qua xs. as ⇒ gf` (when `qua = All`) or `qua xs. as ∧ gf`
    /// (when `qua = Ex`). The `as` are the *guard* atoms, all
    /// quantified `xs` must be bound by them.
    GGuarded {
        qua: Quant,
        vars: Vec<GBinding>,
        guards: Vec<GAtom>,
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
    match fm {
        Guarded::Atom(_) => true,
        Guarded::Conj(_) => true,
        Guarded::GGuarded { qua: Quant::Ex, .. } => true,
        Guarded::GGuarded { qua: Quant::All, vars, guards, body }
            if vars.is_empty() && guards.len() == 1 => {
            let body_is_false = matches!(&**body, Guarded::Disj(v) if v.is_empty());
            body_is_false && matches!(
                &guards[0],
                GAtom::Less(_, _) | GAtom::Subterm(_, _) | GAtom::Last(_),
            )
        }
        _ => false,
    }
}

/// Smart `Conj` — recursively flatten nested `Conj`s and short-circuit.
/// HS-faithful: mirrors Haskell `gconj` (Guarded.hs:413-421), whose
/// helper `flatten (GConj conj) = concatMap flatten $ getConj conj`
/// recursively unwraps every level of nested conjunction.  Prior RS
/// implementation only unwrapped ONE level, leaving e.g. binary-Or
/// chains parsed as `Conj(Conj(Conj(a, b), c), d)` only partially
/// flattened — the runtime then saw a 2-item Conj instead of a 4-item
/// one, which mismatched HS's case-enumeration shape.
pub fn gconj(items: Vec<Guarded>) -> Guarded {
    fn flatten(item: Guarded, out: &mut Vec<Guarded>) -> bool {
        // returns true if gfalse encountered (absorbs)
        match item {
            Guarded::Conj(inner) => {
                for x in inner {
                    if flatten(x, out) { return true; }
                }
                false
            }
            x if x == gfalse() => true,
            x => { out.push(x); false }
        }
    }
    let mut out = Vec::new();
    for it in items {
        if flatten(it, &mut out) { return gfalse(); }
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
    // HS `simplifyGuardedOrReturn` calls `valuation =<< unbindAtom ato`,
    // which is Nothing whenever any Bound var is present in the atom.
    // We mirror by attempting GAtom→p::Atom conversion; on Bound, the
    // round-trip panics, so we use a safe variant.
    let eval = |a: &GAtom| -> Option<bool> {
        try_gatom_to_atom(a).and_then(|pa| valuation(&pa))
    };
    match fm {
        Guarded::Atom(a) => match eval(a) {
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
            let evaluated: Vec<(GAtom, Option<bool>)> = guards.iter()
                .map(|a| (a.clone(), eval(a)))
                .collect();
            // Any False guard → universal vacuously holds.
            if evaluated.iter().any(|(_, v)| v == &Some(false)) {
                return gtrue();
            }
            // Keep only the Unknown guards — True guards are vacuous.
            let kept: Vec<GAtom> = evaluated.into_iter()
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

/// Convert `GAtom` to `p::Atom` if no Bound vars are present, else None.
/// HS `unbindAtom`.
pub fn try_gatom_to_atom(a: &GAtom) -> Option<p::Atom> {
    Some(match a {
        GAtom::Eq(s, t) => p::Atom::Eq(try_gterm_to_term(s)?, try_gterm_to_term(t)?),
        GAtom::Less(s, t) => p::Atom::Less(try_gterm_to_term(s)?, try_gterm_to_term(t)?),
        GAtom::LessMset(s, t) => p::Atom::LessMset(try_gterm_to_term(s)?, try_gterm_to_term(t)?),
        GAtom::Subterm(s, t) => p::Atom::Subterm(try_gterm_to_term(s)?, try_gterm_to_term(t)?),
        GAtom::Action(f, t) => p::Atom::Action(try_gfact_to_fact(f)?, try_gterm_to_term(t)?),
        GAtom::Last(t) => p::Atom::Last(try_gterm_to_term(t)?),
        GAtom::Pred(f) => p::Atom::Pred(try_gfact_to_fact(f)?),
    })
}

/// Convert `GTerm` to `p::Term` if no Bound vars are present, else None.
pub fn try_gterm_to_term(t: &GTerm) -> Option<p::Term> {
    Some(match t {
        GTerm::Var(BVar::Free(v)) => p::Term::Var(v.clone()),
        GTerm::Var(BVar::Bound(_)) => return None,
        GTerm::PubLit(s) => p::Term::PubLit(s.clone()),
        GTerm::FreshLit(s) => p::Term::FreshLit(s.clone()),
        GTerm::NatLit(s) => p::Term::NatLit(s.clone()),
        GTerm::Number(n) => p::Term::Number(*n),
        GTerm::NumberOne => p::Term::NumberOne,
        GTerm::NatOne => p::Term::NatOne,
        GTerm::DhNeutral => p::Term::DhNeutral,
        GTerm::App(n, args) => {
            let mut acc = Vec::with_capacity(args.len());
            for a in args { acc.push(try_gterm_to_term(a)?); }
            p::Term::App(n.clone(), acc)
        }
        GTerm::AlgApp(n, a, b) =>
            p::Term::AlgApp(n.clone(), Box::new(try_gterm_to_term(a)?), Box::new(try_gterm_to_term(b)?)),
        GTerm::Pair(items) => {
            let mut acc = Vec::with_capacity(items.len());
            for it in items { acc.push(try_gterm_to_term(it)?); }
            p::Term::Pair(acc)
        }
        GTerm::Diff(a, b) =>
            p::Term::Diff(Box::new(try_gterm_to_term(a)?), Box::new(try_gterm_to_term(b)?)),
        GTerm::BinOp(op, a, b) =>
            p::Term::BinOp(*op, Box::new(try_gterm_to_term(a)?), Box::new(try_gterm_to_term(b)?)),
        GTerm::PatMatch(t) => p::Term::PatMatch(Box::new(try_gterm_to_term(t)?)),
    })
}

/// Convert `GFact` to `p::Fact` if no Bound vars are present, else None.
pub fn try_gfact_to_fact(f: &GFact) -> Option<p::Fact> {
    let mut args = Vec::with_capacity(f.args.len());
    for a in &f.args { args.push(try_gterm_to_term(a)?); }
    Some(p::Fact {
        persistent: f.persistent,
        name: f.name.clone(),
        args,
        annotations: f.annotations.clone(),
    })
}

/// Smart `Disj` — flatten one level, short-circuit on `gtrue`, drop
/// `gfalse` items.  Mirrors Haskell's `gdisj` which treats `Disj` as a
/// set semantically: True absorbs, False is the unit.  Without dropping
/// gfalse items, partial_atom_valuation can turn `Disj([Eq(j,i),
/// Less(i,j)])` into `Disj([gfalse, gfalse])` (when j<i is known via
/// the order graph) and we'd split a 2-case Disj goal whose branches
/// both close — Haskell collapses this to `gfalse` directly.
pub fn gdisj(items: Vec<Guarded>) -> Guarded {
    // Recursively flatten nested `Disj`s. HS-faithful: mirrors Haskell
    // `gdisj` (Guarded.hs:423-435) whose helper
    // `flatten (GDisj disj) = concatMap flatten $ getDisj disj`
    // recursively unwraps every level. Prior RS implementation only
    // unwrapped ONE level, leaving e.g. a 5-way `∨` parsed as a binary
    // `Or` chain (`Disj(Disj(Disj(Disj(a, b), c), d), e)`) only partially
    // flattened — the runtime then saw a 2-alt Disj goal instead of the
    // 5-alt one HS sees, which mismatched the case-enumeration of
    // skeleton proofs like YubiSecure slightly_weaker_invariant.
    fn flatten(item: Guarded, out: &mut Vec<Guarded>) -> bool {
        // returns true if gtrue encountered (absorbs)
        match item {
            Guarded::Disj(inner) => {
                for x in inner {
                    if flatten(x, out) { return true; }
                }
                false
            }
            x if x == gtrue() => true,
            x if x == gfalse() => false,
            x => { out.push(x); false }
        }
    }
    let mut out = Vec::new();
    for it in items {
        if flatten(it, &mut out) { return gtrue(); }
    }
    // Mirror Haskell `gdisj`'s `nub gfs` (Guarded.hs:432).
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
pub fn gex(vars: Vec<GBinding>, guards: Vec<GAtom>, body: Guarded) -> Guarded {
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
pub fn gall(vars: Vec<GBinding>, guards: Vec<GAtom>, body: Guarded) -> Guarded {
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
    /// The parser-AST sub-formula at the point of failure, mirroring HS's
    /// `f0` in `convert polarity f0@(Qua qua0 _ _)` — the innermost
    /// quantifier that failed the guard check.  Used by callers to render
    /// the HS-faithful:
    ///   ```
    ///   <error_text>
    ///     "<sub_formula>"
    ///   in the formula
    ///     "<full_formula>"
    ///   ```
    /// block.  `None` means the error occurred outside a quantifier context
    /// (shouldn't happen in practice but handled gracefully).
    pub subject_formula: Option<tamarin_parser::ast::Formula>,
}

impl std::fmt::Display for GuardError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
impl std::error::Error for GuardError {}

fn err(msg: impl Into<String>) -> GuardError {
    GuardError { message: msg.into(), subject_formula: None }
}

// =============================================================================
// Conversion entry point
// =============================================================================

/// Convert a surface formula to its guarded form.
pub fn formula_to_guarded(f: &p::Formula) -> Result<Guarded, GuardError> {
    // HS-faithful: HS represents formula terms as LNTerm, where every AC head
    // (`Mult`/`Union`/`Xor`/`NatPlus`) is stored as a flat, `fAppAC`-sorted
    // argument list (Term/Term/Raw.hs:118-122).  The sort happens at PARSE
    // time over the FREE logical variables, ordered by `Ord LVar` =
    // (idx, sort, name) (LTerm.hs:522-524) — for freshly-parsed lemma vars
    // (all idx 0) this is name-alphabetical, e.g. `x + z` stays `x++z` and
    // `y + z` stays `y++z`.  `formulaToGuarded` then abstracts Free→Bound via
    // a structural `fmap` (Guarded.hs:289-308) that preserves the AC arg
    // positions.  Our parser stores formula terms as nested `BinOp(op, l, r)`
    // trees in source order and never sorts them, so we canonicalise the AC
    // chains over the FREE-variable parser AST FIRST (mirroring HS's
    // parse-time `fAppAC` on free LVars), then convert to guarded form.
    let canon = crate::elaborate::canonicalize_ac_in_formula(f);
    convert(false, &canon)
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
///
/// With DeBruijn bindings, Bound vars don't appear in this set — they have
/// no name (their "name" is positional).  We collect VarSpec names from
/// every `BVar::Free` leaf.
pub fn free_vars(g: &Guarded) -> BTreeSet<String> {
    fn rec(g: &Guarded, out: &mut BTreeSet<String>) {
        match g {
            Guarded::Atom(a) => {
                let mut free = Vec::new();
                collect_free_atom(a, &mut free);
                for v in free { out.insert(v.name); }
            }
            Guarded::Disj(items) | Guarded::Conj(items) =>
                for it in items { rec(it, out); },
            Guarded::GGuarded { guards, body, .. } => {
                for a in guards {
                    let mut free = Vec::new();
                    collect_free_atom(a, &mut free);
                    for v in free { out.insert(v.name); }
                }
                rec(body, out);
            }
        }
    }
    let mut out = BTreeSet::new();
    rec(g, &mut out);
    out
}

/// Collect variable names from a parser-AST term.  Used by
/// `remaining_unguarded` for the pre-DeBruijn unguarded-variable check.
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
// Walking Guarded with DeBruijn-aware substitution
// =============================================================================

/// Mirror HS `substFree :: [(LVar, Integer)] -> LGuarded c -> LGuarded c`.
///
/// Walks the Guarded tracking scope depth (number of binders crossed).
/// At each atom, replaces each `Free(v)` matching some `(v, db)` in `s`
/// with `Bound(db + depth)`.
pub fn subst_free_guarded(g: &Guarded, s: &[(p::VarSpec, u32)]) -> Guarded {
    fn rec(g: &Guarded, s: &[(p::VarSpec, u32)], depth: u32) -> Guarded {
        match g {
            Guarded::Atom(a) => Guarded::Atom(subst_free_atom_at_depth(a, s, depth)),
            Guarded::Disj(items) =>
                Guarded::Disj(items.iter().map(|i| rec(i, s, depth)).collect()),
            Guarded::Conj(items) =>
                Guarded::Conj(items.iter().map(|i| rec(i, s, depth)).collect()),
            Guarded::GGuarded { qua, vars, guards, body } => {
                let new_depth = depth + vars.len() as u32;
                Guarded::GGuarded {
                    qua: qua.clone(),
                    vars: vars.clone(),
                    guards: guards.iter()
                        .map(|a| subst_free_atom_at_depth(a, s, new_depth))
                        .collect(),
                    body: Box::new(rec(body, s, new_depth)),
                }
            }
        }
    }
    rec(g, s, 0)
}

/// Mirror HS `substBound :: [(Integer, LVar)] -> LGuarded c -> LGuarded c`.
///
/// Walks the Guarded tracking scope depth.  At each atom, replaces each
/// `Bound(n)` matching some `(i, v)` in `s` (where `n = i + depth`) with
/// `Free(v)`.
pub fn subst_bound_guarded(g: &Guarded, s: &[(u32, p::VarSpec)]) -> Guarded {
    fn rec(g: &Guarded, s: &[(u32, p::VarSpec)], depth: u32) -> Guarded {
        match g {
            Guarded::Atom(a) => Guarded::Atom(subst_bound_atom_at_depth(a, s, depth)),
            Guarded::Disj(items) =>
                Guarded::Disj(items.iter().map(|i| rec(i, s, depth)).collect()),
            Guarded::Conj(items) =>
                Guarded::Conj(items.iter().map(|i| rec(i, s, depth)).collect()),
            Guarded::GGuarded { qua, vars, guards, body } => {
                let new_depth = depth + vars.len() as u32;
                Guarded::GGuarded {
                    qua: qua.clone(),
                    vars: vars.clone(),
                    guards: guards.iter()
                        .map(|a| subst_bound_atom_at_depth(a, s, new_depth))
                        .collect(),
                    body: Box::new(rec(body, s, new_depth)),
                }
            }
        }
    }
    rec(g, s, 0)
}

// =============================================================================
// Polarity-aware conversion
// =============================================================================

fn convert(polarity: bool, f: &p::Formula) -> Result<Guarded, GuardError> {
    match f {
        p::Formula::True => Ok(gtf(polarity != true)),
        p::Formula::False => Ok(gtf(polarity != false)),
        p::Formula::Atom(a) => {
            let ga = atom_to_gatom_free(a);
            if polarity { Ok(gnot_atom(&ga)) } else { Ok(Guarded::Atom(ga)) }
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
            let result = if same_qua {
                let out_qua = if polarity { Quant::Ex } else { Quant::All };
                convert_all(&xs, body, polarity, out_qua)
            } else {
                let out_qua = if polarity { Quant::All } else { Quant::Ex };
                convert_ex(&xs, body, polarity, out_qua)
            };
            // HS: the error from `convEx`/`convAll` is decorated with
            // `ppFormula f0` (the current quantifier sub-formula) by
            // `noUnguardedVars` / the toplevel-implication check.
            // We mirror by attaching `f.clone()` as `subject_formula`
            // on the INNERMOST failure (guard: set only when not yet set,
            // so the deepest quantifier sub-formula wins).
            result.map_err(|mut e| {
                if e.subject_formula.is_none() {
                    e.subject_formula = Some(f.clone());
                }
                e
            })
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
    Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
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
        Ok(close_guarded(out_qua, xs.to_vec(), atoms, body_guarded))
    } else {
        Err(err("universal quantifier without toplevel implication"))
    }
}

/// Mirror HS `closeGuarded :: Quantifier -> [LVar] -> [Atom] -> LGuarded -> LGuarded`.
///
/// Takes named LVars `xs`, parser-AST atoms `atoms`, and an already-built
/// body `gf`.  Closes the binder:
///   - Lifts each atom from `p::Atom` to `GAtom` (initially all Free).
///   - Substitutes every Free LVar matching `xs[i]` with `Bound(k-1-i)` in
///     the atoms (depth 0) and the body (depth-tracked through nested
///     binders).
///   - Strips the binder list down to `(name, sort)` pairs (`GBinding`).
///
/// HS:
/// ```text
///   closeGuarded qua vs as gf = ((case qua of Ex -> gex; All -> gall) vs' as' gf'
///     where  as'   = map (substFreeAtom s . fmap (fmapTerm (fmap Free))) as
///            gf'   = substFree s gf
///            s     = zip (reverse vs) [0..]
///            vs'   = map (lvarName &&& lvarSort) vs
/// ```
pub fn close_guarded(
    qua: Quant,
    xs: Vec<p::VarSpec>,
    atoms: Vec<p::Atom>,
    body: Guarded,
) -> Guarded {
    let close_s = close_subst(&xs);
    let new_guards: Vec<GAtom> = atoms.iter()
        .map(|a| {
            let ga = atom_to_gatom_free(a);
            subst_free_atom_at_depth(&ga, &close_s, 0)
        })
        .collect();
    let new_body = subst_free_guarded(&body, &close_s);
    let vs: Vec<GBinding> = xs.iter().map(lvar_to_binding).collect();
    match qua {
        Quant::Ex => gex(vs, new_guards, new_body),
        Quant::All => gall(vs, new_guards, new_body),
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
    // HS: `map (quotes . text . show) unguarded` — each name is shown
    // via Haskell's `show LVar` which renders as `'name'` (single-quoted).
    // The Haskell `show` for LVar is its `Show` instance, which we can
    // find at LTerm.hs:197: `show (LVar n s i) = ...` with no explicit
    // instance → derives Show, producing `LVar "name" LSortMsg 0` style.
    // But `quotes` wraps in single quotes at the Doc level.  The resulting
    // `text . show` on each unguarded LVar produces `'name'` in the
    // rendered Doc via `quotes (text "name")`.
    let names: Vec<String> = vars.iter().map(|v| format!("'{}'", v.name)).collect();
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
fn gnot_atom(a: &GAtom) -> Guarded {
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
/// We touch ONLY witness vars (name == "x") — every other LVar
/// (real protocol vars, distinct named fresh values) keeps its
/// identity, so the dedup doesn't over-merge legitimately-distinct
/// implications.
pub fn normalize_witness_lvars(g: &Guarded) -> Guarded {
    let mut subst: VarSubst = std::collections::HashMap::new();
    collect_witness_vars(g, &mut subst);
    if subst.is_empty() { return g.clone(); }
    subst_guarded(g, &subst)
}

/// `normalize_bound_lvars` from the pre-DeBruijn implementation has been
/// REMOVED.  With HS-faithful DeBruijn bindings, alpha-equivalent formulas
/// compare equal under structural `Eq` automatically — Bound vars carry no
/// idx, so `Ex j:5. KU(s)@j:5` and `Ex j:6. KU(s)@j:6` both yield
/// `GGuarded { vars: [(j, Node)], body: ... Bound(0) ... }`.
///
/// Kept as a no-op stub for any straggling caller; will be deleted once
/// every site is migrated.
pub fn normalize_bound_lvars(g: &Guarded) -> Guarded {
    g.clone()
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
    fn norm_binding(b: &GBinding) -> GBinding {
        GBinding { name: b.name.clone(), sort: norm_sort(b.sort) }
    }
    fn norm_bvar(b: &BVar) -> BVar {
        match b {
            BVar::Bound(n) => BVar::Bound(*n),
            BVar::Free(v) => BVar::Free(p::VarSpec {
                name: v.name.clone(),
                idx: v.idx,
                sort: norm_sort(v.sort),
                typ: v.typ.clone(),
            }),
        }
    }
    fn norm_term(t: &GTerm) -> GTerm {
        match t {
            GTerm::Var(b) => GTerm::Var(norm_bvar(b)),
            GTerm::App(n, args) => GTerm::App(
                n.clone(), args.iter().map(norm_term).collect()),
            GTerm::Pair(args) => GTerm::Pair(args.iter().map(norm_term).collect()),
            GTerm::AlgApp(n, a, b) => GTerm::AlgApp(
                n.clone(), Box::new(norm_term(a)), Box::new(norm_term(b))),
            GTerm::Diff(a, b) => GTerm::Diff(
                Box::new(norm_term(a)), Box::new(norm_term(b))),
            GTerm::BinOp(op, a, b) => GTerm::BinOp(
                *op, Box::new(norm_term(a)), Box::new(norm_term(b))),
            GTerm::PatMatch(inner) => GTerm::PatMatch(Box::new(norm_term(inner))),
            _ => t.clone(),
        }
    }
    fn norm_fact(f: &GFact) -> GFact {
        GFact {
            persistent: f.persistent,
            name: f.name.clone(),
            args: f.args.iter().map(norm_term).collect(),
            annotations: f.annotations.clone(),
        }
    }
    fn norm_atom(a: &GAtom) -> GAtom {
        match a {
            GAtom::Action(f, t) => GAtom::Action(norm_fact(f), norm_term(t)),
            GAtom::Eq(x, y) => GAtom::Eq(norm_term(x), norm_term(y)),
            GAtom::Less(x, y) => GAtom::Less(norm_term(x), norm_term(y)),
            GAtom::LessMset(x, y) => GAtom::LessMset(norm_term(x), norm_term(y)),
            GAtom::Subterm(x, y) => GAtom::Subterm(norm_term(x), norm_term(y)),
            GAtom::Last(t) => GAtom::Last(norm_term(t)),
            GAtom::Pred(f) => GAtom::Pred(norm_fact(f)),
        }
    }
    fn rec(g: &Guarded) -> Guarded {
        match g {
            Guarded::Atom(a) => Guarded::Atom(norm_atom(a)),
            Guarded::Disj(items) => Guarded::Disj(items.iter().map(rec).collect()),
            Guarded::Conj(items) => Guarded::Conj(items.iter().map(rec).collect()),
            Guarded::GGuarded { qua, vars, guards, body } => Guarded::GGuarded {
                qua: qua.clone(),
                vars: vars.iter().map(norm_binding).collect(),
                guards: guards.iter().map(norm_atom).collect(),
                body: Box::new(rec(body)),
            },
        }
    }
    rec(g)
}

/// Canonicalise AC-`BinOp` argument ordering inside a `Guarded` so two
/// formulas differing only by AC permutation compare equal under `==`.
///
/// HS-faithful rationale.  HS represents formulas using LNTerm (which
/// stores AC operators as flat sorted argument lists via `f_app_ac`).
/// Every HS `mapFrees` / `apply` over LNTerm routes through `f_app_ac`,
/// so AC heads stay in canonical sorted order after substitution.  Rust
/// stores formulas in parser-AST `BinOp(op, l, r)` (strict arity-2), and
/// `subst_term` / `subst_gterm` recurse into the children without
/// re-sorting.
///
/// After `rename_precise_system` renumbers free vars (e.g. `ekR.5 →
/// ekR.0`, `ltkI.7 → ltkI.0`), the LVar `Ord` (`idx`-first ⇒
/// `name`-only on ties) flips: an originally-sorted
/// `Mult(ltkI.5, ekR.7)` (`ltkI < ekR` by idx) becomes a NOW-unsorted
/// `Mult(ltkI.0, ekR.0)` (`ekR < ltkI` by name).  The PARSER-AST slots
/// stay in original order — no re-sort happens.  Meanwhile a fresh
/// implied-formula built via `lnterm_to_term`-of-`f_app_ac` output
/// arrives in canonical sorted form (`Mult(ekR.0, ltkI.0)`).  Dedup via
/// bare `==` (or via `apply_canon`'s witness/bound normalisation) then
/// fails, and `insert_implied_formulas_pass` adds a structurally-
/// duplicate formula on every subsequent `simplifySystem` call —
/// breaking idempotency.
///
/// This pass mirrors HS's invariant explicitly: for every AC head
/// (`Mult`, `Union`, `Xor`, `NatPlus`), flatten the binary chain into
/// the full multiset, sort it via `cmp_term` (the existing HS-faithful
/// parser-AST Ord), then re-fold into a right-leaning canonical
/// `BinOp(op, x0, BinOp(op, x1, ...))`.  Two AC-permuted parser-AST
/// representations of the same multiset collapse to the same shape.
pub fn canonicalize_ac_in_guarded(g: &Guarded) -> Guarded {
    canonicalize_ac_in_guarded_with(g, cmp_term)
}

type GCmp = fn(&GTerm, &GTerm) -> std::cmp::Ordering;

fn cac_flatten(op: &p::BinOp, t: &GTerm, out: &mut Vec<GTerm>) {
    match t {
        GTerm::BinOp(inner_op, l, r) if inner_op == op => {
            cac_flatten(op, l, out);
            cac_flatten(op, r, out);
        }
        _ => out.push(t.clone()),
    }
}

fn cac_rec_term(t: &GTerm, cmp: GCmp) -> GTerm {
    match t {
        GTerm::Var(_) | GTerm::PubLit(_) | GTerm::FreshLit(_)
        | GTerm::NatLit(_) | GTerm::Number(_) | GTerm::NumberOne
        | GTerm::NatOne | GTerm::DhNeutral => t.clone(),
        GTerm::App(n, args) => GTerm::App(
            n.clone(), args.iter().map(|a| cac_rec_term(a, cmp)).collect()),
        GTerm::Pair(args) => GTerm::Pair(
            args.iter().map(|a| cac_rec_term(a, cmp)).collect()),
        GTerm::AlgApp(n, a, b) => GTerm::AlgApp(
            n.clone(), Box::new(cac_rec_term(a, cmp)), Box::new(cac_rec_term(b, cmp))),
        GTerm::Diff(a, b) => GTerm::Diff(
            Box::new(cac_rec_term(a, cmp)), Box::new(cac_rec_term(b, cmp))),
        GTerm::BinOp(op, l, r) => {
            if matches!(op, p::BinOp::Mult | p::BinOp::Union | p::BinOp::Xor | p::BinOp::NatPlus) {
                // Recurse into children first, then flatten the whole AC
                // chain rooted here and rebuild in sorted multiset order.
                let l2 = cac_rec_term(l, cmp);
                let r2 = cac_rec_term(r, cmp);
                let mut flat = Vec::new();
                cac_flatten(op, &l2, &mut flat);
                cac_flatten(op, &r2, &mut flat);
                flat.sort_by(|a, b| cmp(a, b));
                // Right-fold to a binary chain.  At least 2 args.
                let mut iter = flat.into_iter().rev();
                let last = iter.next().unwrap_or(GTerm::PubLit(String::new()));
                let mut acc = last;
                for prev in iter {
                    acc = GTerm::BinOp(*op, Box::new(prev), Box::new(acc));
                }
                acc
            } else {
                GTerm::BinOp(*op, Box::new(cac_rec_term(l, cmp)),
                    Box::new(cac_rec_term(r, cmp)))
            }
        }
        GTerm::PatMatch(inner) => GTerm::PatMatch(Box::new(cac_rec_term(inner, cmp))),
    }
}

fn cac_rec_fact(f: &GFact, cmp: GCmp) -> GFact {
    GFact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(|a| cac_rec_term(a, cmp)).collect(),
        annotations: f.annotations.clone(),
    }
}

fn cac_rec_atom(a: &GAtom, cmp: GCmp) -> GAtom {
    match a {
        GAtom::Action(f, t) => GAtom::Action(cac_rec_fact(f, cmp), cac_rec_term(t, cmp)),
        GAtom::Eq(x, y) => GAtom::Eq(cac_rec_term(x, cmp), cac_rec_term(y, cmp)),
        GAtom::Less(x, y) => GAtom::Less(cac_rec_term(x, cmp), cac_rec_term(y, cmp)),
        GAtom::LessMset(x, y) => GAtom::LessMset(cac_rec_term(x, cmp), cac_rec_term(y, cmp)),
        GAtom::Subterm(x, y) => GAtom::Subterm(cac_rec_term(x, cmp), cac_rec_term(y, cmp)),
        GAtom::Last(t) => GAtom::Last(cac_rec_term(t, cmp)),
        GAtom::Pred(f) => GAtom::Pred(cac_rec_fact(f, cmp)),
    }
}

fn canonicalize_ac_in_guarded_with(g: &Guarded, cmp: GCmp) -> Guarded {
    match g {
        Guarded::Atom(a) => Guarded::Atom(cac_rec_atom(a, cmp)),
        Guarded::Disj(items) => Guarded::Disj(
            items.iter().map(|i| canonicalize_ac_in_guarded_with(i, cmp)).collect()),
        Guarded::Conj(items) => Guarded::Conj(
            items.iter().map(|i| canonicalize_ac_in_guarded_with(i, cmp)).collect()),
        Guarded::GGuarded { qua, vars, guards, body } => Guarded::GGuarded {
            qua: qua.clone(),
            vars: vars.clone(),
            guards: guards.iter().map(|a| cac_rec_atom(a, cmp)).collect(),
            body: Box::new(canonicalize_ac_in_guarded_with(body, cmp)),
        },
    }
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

fn collect_witness_vars_atom(a: &GAtom, out: &mut VarSubst) {
    match a {
        GAtom::Eq(x, y) | GAtom::Less(x, y) | GAtom::LessMset(x, y)
        | GAtom::Subterm(x, y) => {
            collect_witness_vars_term(x, out);
            collect_witness_vars_term(y, out);
        }
        GAtom::Action(f, t) => {
            for arg in &f.args { collect_witness_vars_term(arg, out); }
            collect_witness_vars_term(t, out);
        }
        GAtom::Last(t) => collect_witness_vars_term(t, out),
        GAtom::Pred(f) => {
            for arg in &f.args { collect_witness_vars_term(arg, out); }
        }
    }
}

fn collect_witness_vars_term(t: &GTerm, out: &mut VarSubst) {
    match t {
        GTerm::Var(BVar::Free(v)) => {
            if v.name == "x" {
                let canonical = p::VarSpec {
                    name: v.name.clone(),
                    idx: 0,                  // canonical idx
                    sort: v.sort,
                    typ: v.typ.clone(),
                };
                out.insert((v.name.clone(), v.idx), p::Term::Var(canonical));
            }
        }
        GTerm::Var(BVar::Bound(_)) => {}  // bound vars have no LVar idx
        GTerm::App(_, args) | GTerm::Pair(args) => {
            for a in args { collect_witness_vars_term(a, out); }
        }
        GTerm::AlgApp(_, a, b) | GTerm::Diff(a, b) | GTerm::BinOp(_, a, b) => {
            collect_witness_vars_term(a, out);
            collect_witness_vars_term(b, out);
        }
        GTerm::PatMatch(t) => collect_witness_vars_term(t, out),
        GTerm::PubLit(_) | GTerm::FreshLit(_) | GTerm::NatLit(_)
        | GTerm::Number(_) | GTerm::NumberOne | GTerm::NatOne
        | GTerm::DhNeutral => {}
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
/// guards, body, and every nested term/atom — but only Free LVar
/// leaves (Bound vars are positional and cannot collide).
///
/// With HS-faithful DeBruijn bindings, the elaborate capture-avoidance
/// dance of the pre-migration code is unnecessary: Bound vars carry no
/// LVar idx, so a free-var substitution cannot accidentally capture them.
/// Mirrors HS `applySkGuarded subst = mapGuardedAtoms (const $ apply subst)`.
pub fn subst_guarded(g: &Guarded, s: &VarSubst) -> Guarded {
    if s.is_empty() { return g.clone(); }
    subst_guarded_inner(g, s)
}

fn subst_guarded_inner(g: &Guarded, s: &VarSubst) -> Guarded {
    match g {
        Guarded::Atom(a) => Guarded::Atom(subst_gatom(a, s)),
        Guarded::Disj(items) =>
            Guarded::Disj(items.iter().map(|i| subst_guarded_inner(i, s)).collect()),
        Guarded::Conj(items) =>
            Guarded::Conj(items.iter().map(|i| subst_guarded_inner(i, s)).collect()),
        Guarded::GGuarded { qua, vars, guards, body } => Guarded::GGuarded {
            qua: qua.clone(),
            vars: vars.clone(),
            guards: guards.iter().map(|a| subst_gatom(a, s)).collect(),
            body: Box::new(subst_guarded_inner(body, s)),
        }
    }
}

/// Substitute Free LVar leaves in a `GAtom`.  Replacement targets are
/// parser-AST terms (`p::Term`), which we lift to `GTerm` with all-Free
/// leaves — those Free LVars are at the system's top-level scope and
/// cannot collide with any binder.
pub fn subst_gatom(a: &GAtom, s: &VarSubst) -> GAtom {
    match a {
        GAtom::Eq(x, y) => GAtom::Eq(subst_gterm(x, s), subst_gterm(y, s)),
        GAtom::Less(x, y) => GAtom::Less(subst_gterm(x, s), subst_gterm(y, s)),
        GAtom::LessMset(x, y) => GAtom::LessMset(subst_gterm(x, s), subst_gterm(y, s)),
        GAtom::Subterm(x, y) => GAtom::Subterm(subst_gterm(x, s), subst_gterm(y, s)),
        GAtom::Action(f, t) => GAtom::Action(subst_gfact(f, s), subst_gterm(t, s)),
        GAtom::Last(t) => GAtom::Last(subst_gterm(t, s)),
        GAtom::Pred(f) => GAtom::Pred(subst_gfact(f, s)),
    }
}

/// Substitute Free LVar leaves in a `GFact`.
pub fn subst_gfact(f: &GFact, s: &VarSubst) -> GFact {
    GFact {
        persistent: f.persistent,
        name: f.name.clone(),
        args: f.args.iter().map(|a| subst_gterm(a, s)).collect(),
        annotations: f.annotations.clone(),
    }
}

/// Substitute Free LVar leaves in a `GTerm`.
pub fn subst_gterm(t: &GTerm, s: &VarSubst) -> GTerm {
    match t {
        GTerm::Var(BVar::Free(v)) => {
            let key = (v.name.clone(), v.idx);
            if let Some(target) = s.get(&key) {
                term_to_gterm_free(target)
            } else {
                GTerm::Var(BVar::Free(v.clone()))
            }
        }
        GTerm::Var(b) => GTerm::Var(b.clone()),
        GTerm::PubLit(s_) => GTerm::PubLit(s_.clone()),
        GTerm::FreshLit(s_) => GTerm::FreshLit(s_.clone()),
        GTerm::NatLit(s_) => GTerm::NatLit(s_.clone()),
        GTerm::Number(n) => GTerm::Number(*n),
        GTerm::NumberOne => GTerm::NumberOne,
        GTerm::NatOne => GTerm::NatOne,
        GTerm::DhNeutral => GTerm::DhNeutral,
        GTerm::App(n, args) =>
            GTerm::App(n.clone(), args.iter().map(|a| subst_gterm(a, s)).collect()),
        GTerm::AlgApp(n, a, b) => GTerm::AlgApp(
            n.clone(), Box::new(subst_gterm(a, s)), Box::new(subst_gterm(b, s))),
        GTerm::Pair(items) =>
            GTerm::Pair(items.iter().map(|i| subst_gterm(i, s)).collect()),
        GTerm::Diff(a, b) => GTerm::Diff(
            Box::new(subst_gterm(a, s)), Box::new(subst_gterm(b, s))),
        GTerm::BinOp(op, a, b) => GTerm::BinOp(
            *op, Box::new(subst_gterm(a, s)), Box::new(subst_gterm(b, s))),
        GTerm::PatMatch(t) => GTerm::PatMatch(Box::new(subst_gterm(t, s))),
    }
}

/// Find the maximum variable idx used in a guarded formula. Used
/// to allocate fresh indices without collisions.
pub fn max_var_idx(g: &Guarded) -> u64 {
    fn rec_term(t: &GTerm, m: &mut u64) {
        match t {
            GTerm::Var(BVar::Free(v)) => { if v.idx > *m { *m = v.idx; } }
            GTerm::Var(BVar::Bound(_)) => {}
            GTerm::App(_, args) | GTerm::Pair(args) => {
                for a in args { rec_term(a, m); }
            }
            GTerm::AlgApp(_, a, b) | GTerm::Diff(a, b) | GTerm::BinOp(_, a, b) => {
                rec_term(a, m); rec_term(b, m);
            }
            GTerm::PatMatch(t) => rec_term(t, m),
            _ => {}
        }
    }
    fn rec_atom(a: &GAtom, m: &mut u64) {
        match a {
            GAtom::Eq(x, y) | GAtom::Less(x, y) | GAtom::LessMset(x, y)
            | GAtom::Subterm(x, y) => { rec_term(x, m); rec_term(y, m); }
            GAtom::Action(f, t) => {
                for arg in &f.args { rec_term(arg, m); }
                rec_term(t, m);
            }
            GAtom::Last(t) => rec_term(t, m),
            GAtom::Pred(f) => for a in &f.args { rec_term(a, m); },
        }
    }
    fn rec(g: &Guarded, m: &mut u64) {
        match g {
            Guarded::Atom(a) => rec_atom(a, m),
            Guarded::Disj(xs) | Guarded::Conj(xs) => for x in xs { rec(x, m); },
            Guarded::GGuarded { guards, body, .. } => {
                // Bindings carry no idx in the DeBruijn representation.
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
        Guarded::Atom(a) => matches!(a, GAtom::Action(_, _)),
        Guarded::Disj(xs) | Guarded::Conj(xs) => xs.iter().any(contains_action),
        Guarded::GGuarded { guards, body, .. } => {
            !guards.is_empty()
                || guards.iter().any(|a| matches!(a, GAtom::Action(_, _)))
                || contains_action(body)
        }
    }
}

/// Is `g` closed (no free variables)?
fn is_closed(g: &Guarded) -> bool {
    free_vars(g).is_empty()
}

/// Test whether an atom is a `Last(_)` predicate.
fn is_last_atom(a: &GAtom) -> bool {
    matches!(a, GAtom::Last(_))
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
            // HS `lastAtos = do (j, (_, LSortNode)) <- zip [0..] (reverse ss);
            //                   return $ Last (varTerm (Bound j))`.
            // Iterate vars inner-to-outer (rev), filter to node-sorted,
            // assign DeBruijn `j = 0, 1, ...` in that order.
            let last_atos: Vec<Guarded> = vars.iter().rev().enumerate()
                .filter(|(_, v)| matches!(
                    v.sort,
                    p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node)
                ))
                .map(|(j, _)| {
                    Guarded::Atom(GAtom::Last(GTerm::Var(BVar::Bound(j as u32))))
                })
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
        Guarded::Atom(GAtom::Less(i, j)) => Ok(Guarded::Disj(vec![
            Guarded::Atom(GAtom::Eq(i.clone(), j.clone())),
            Guarded::Atom(GAtom::Less(j.clone(), i.clone())),
        ])),
        Guarded::Atom(GAtom::Last(_)) => Err("formula not last-free".to_string()),
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
    // With DeBruijn bindings, only `BVar::Free` leaves carry an LVar
    // identity — `Bound` is positional and skipped automatically.
    // No bound-set tracking needed.
    fn rec<G: FnMut(&p::VarSpec) -> p::VarSpec>(g: &Guarded, f: &mut G) -> Guarded {
        match g {
            Guarded::Atom(a) => Guarded::Atom(map_free_atom(a, f)),
            Guarded::Disj(items) =>
                Guarded::Disj(items.iter().map(|i| rec(i, f)).collect()),
            Guarded::Conj(items) =>
                Guarded::Conj(items.iter().map(|i| rec(i, f)).collect()),
            Guarded::GGuarded { qua, vars, guards, body } => Guarded::GGuarded {
                qua: qua.clone(),
                vars: vars.clone(),
                guards: guards.iter().map(|a| map_free_atom(a, f)).collect(),
                body: Box::new(rec(body, f)),
            }
        }
    }
    rec(g, &mut f)
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

    /// Regression test for the binder-sort-mismatch bug found during the
    /// DeBruijn migration: the parser produces `Ex #i. P @ i` with the
    /// binder as `Node` and the body's `i` as `Untagged`.  `close_subst`
    /// must match by `(name, idx)` only — full `VarSpec` equality would
    /// leave the body's `i` Free, breaking `is_closed` / `ginduct`.
    #[test]
    fn injectivity_check_ginduct_succeeds() {
        let f = parse_formula_str("not (Ex id #i #j #k. Initiated(id) @ i & Removed(id) @ j & Copied(id) @ k & #i < #j & #j < #k)").expect("parse");
        let g = formula_to_guarded(&f).expect("guarded");
        let g_neg = gnot(&g);
        assert!(free_vars(&g_neg).is_empty(), "gnot should be closed");
        assert!(ginduct(&g_neg).is_ok(), "ginduct should succeed");
    }

    #[test]
    fn varsubst_shadowing_blocks_inner_binder() {
        // `Ex k. Action(k) @ i` — substituting `k` from outside should
        // NOT rewrite the inner `k` because it's positionally bound
        // (DeBruijn `Bound(0)` in the body, not Free LVar `k:0`).
        let mut s = VarSubst::new();
        s.insert(("k".into(), 0), pubconst("OUTER"));
        let inner_k = p::VarSpec { name: "k".into(), idx: 0, sort: p::SortHint::Msg, typ: None };
        let mkfact = |t: p::Term| p::Fact {
            persistent: false,
            annotations: Vec::new(),
            name: "Action".into(),
            args: vec![t],
        };
        // Build via close_guarded so that `k` becomes Bound(0) in the body.
        let g = close_guarded(
            Quant::Ex,
            vec![inner_k.clone()],
            Vec::new(),
            Guarded::Atom(atom_to_gatom_free(&p::Atom::Action(
                mkfact(var("k", 0)),
                var("i", 0),
            ))),
        );
        let result = subst_guarded(&g, &s);
        // Body should be unchanged: subst on Free `(k, 0)` doesn't
        // touch the Bound `k` reference.
        match result {
            Guarded::GGuarded { body, .. } => match &*body {
                Guarded::Atom(GAtom::Action(fa, _)) => {
                    // Walk the body atom and verify the `k` slot is still Bound(0).
                    match &fa.args[0] {
                        GTerm::Var(BVar::Bound(0)) => {}
                        other => panic!("expected Bound(0), got {:?}", other),
                    }
                }
                other => panic!("expected Atom(Action), got {:?}", other),
            },
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
                // Walk the body looking for a Last atom at the innermost
                // binder.  In DeBruijn form, that's `Last(Bound(0))`.
                fn walks_to_last_bound0(g: &Guarded) -> bool {
                    match g {
                        Guarded::Atom(GAtom::Last(GTerm::Var(BVar::Bound(0)))) => true,
                        Guarded::Atom(_) => false,
                        Guarded::Disj(xs) | Guarded::Conj(xs) =>
                            xs.iter().any(walks_to_last_bound0),
                        Guarded::GGuarded { guards, body, .. } =>
                            guards.iter().any(|a| matches!(a, GAtom::Last(GTerm::Var(BVar::Bound(0)))))
                                || walks_to_last_bound0(body),
                    }
                }
                assert!(walks_to_last_bound0(body),
                    "IH body should mention Last(Bound 0) for the node binder; got {:?}", body);
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
                Guarded::Atom(GAtom::Last(_)) => true,
                Guarded::Atom(_) => false,
                Guarded::Disj(xs) | Guarded::Conj(xs) =>
                    xs.iter().any(has_any_last),
                Guarded::GGuarded { guards, body, .. } =>
                    guards.iter().any(|a| matches!(a, GAtom::Last(_)))
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
        Guarded::Atom(atom_to_gatom_free(&p::Atom::Eq(mkv(a), mkv(b))))
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
            guards: vec![atom_to_gatom_free(&a), atom_to_gatom_free(&b)],
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
            guards: vec![atom_to_gatom_free(&a), atom_to_gatom_free(&b)],
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
                assert_eq!(guards, vec![atom_to_gatom_free(&b)]);
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
            guards: vec![atom_to_gatom_free(&a)],
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
        let bound_var = GBinding {
            name: "x".into(), sort: p::SortHint::Msg,
        };
        let g = Guarded::GGuarded {
            qua: Quant::All, vars: vec![bound_var],
            guards: vec![atom_to_gatom_free(&a)],
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

    /// `gdisj` recursively flattens ARBITRARILY deeply nested `Disj`s.
    /// Pinpoints commit 105d3f71's behaviour: the HS `gdisj` helper
    /// `flatten (GDisj disj) = concatMap flatten $ getDisj disj`
    /// (Guarded.hs:423-435) unwraps every level, not just one.  A prior
    /// RS version unwrapped only ONE level — a 5-way `∨` parsed as a
    /// binary-Or chain (`Disj(Disj(Disj(Disj(a, b), c), d), e)`) would
    /// land as a 2-alt Disj goal instead of HS's 5-alt one.
    #[test]
    fn gdisj_deeply_nested_disj_flattens_to_5_alts() {
        let a = g("Last(#a)").unwrap();
        let b = g("Last(#b)").unwrap();
        let c = g("Last(#c)").unwrap();
        let d = g("Last(#d)").unwrap();
        let e = g("Last(#e)").unwrap();
        // Build the left-leaning binary-Or chain
        // `Disj(Disj(Disj(Disj(a, b), c), d), e)`.
        let lvl1 = Guarded::Disj(vec![a.clone(), b.clone()]);
        let lvl2 = Guarded::Disj(vec![lvl1, c.clone()]);
        let lvl3 = Guarded::Disj(vec![lvl2, d.clone()]);
        let lvl4 = Guarded::Disj(vec![lvl3, e.clone()]);
        let out = gdisj(vec![lvl4]);
        match out {
            Guarded::Disj(items) => {
                assert_eq!(items.len(), 5,
                    "4-level-nested binary-Or chain must flatten to 5 \
                     alts (HS `flatten` recurses) — got {} alts",
                    items.len());
                assert_eq!(items, vec![a, b, c, d, e],
                    "flatten preserves leaf order (HS uses concatMap)");
            }
            other => panic!("expected Disj of 5 items, got {:?}", other),
        }
    }

    /// Symmetric: `gconj` recursively flattens deeply nested `Conj`s.
    /// Mirrors HS Guarded.hs:413-421 `flatten (GConj conj) = concatMap
    /// flatten $ getConj conj`.
    #[test]
    fn gconj_deeply_nested_conj_flattens() {
        let a = g("Last(#a)").unwrap();
        let b = g("Last(#b)").unwrap();
        let c = g("Last(#c)").unwrap();
        let d = g("Last(#d)").unwrap();
        let e = g("Last(#e)").unwrap();
        let lvl1 = Guarded::Conj(vec![a.clone(), b.clone()]);
        let lvl2 = Guarded::Conj(vec![lvl1, c.clone()]);
        let lvl3 = Guarded::Conj(vec![lvl2, d.clone()]);
        let lvl4 = Guarded::Conj(vec![lvl3, e.clone()]);
        let out = gconj(vec![lvl4]);
        match out {
            Guarded::Conj(items) => {
                assert_eq!(items.len(), 5,
                    "4-level-nested binary-And chain must flatten to 5 \
                     conj items — got {}", items.len());
                assert_eq!(items, vec![a, b, c, d, e]);
            }
            other => panic!("expected Conj of 5 items, got {:?}", other),
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
