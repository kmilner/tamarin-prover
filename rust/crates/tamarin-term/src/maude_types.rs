//! Port of `Term.Maude.Types`.
//!
//! Converts between our `LNTerm` (logical-named term over `LVar`/`Name`)
//! and an `MTerm` (term over `MaudeLit`) used as the wire format with the
//! Maude subprocess.

use std::collections::BTreeMap;

use crate::lterm::{LNTerm, LSort, LVar, Name, NameTag};
use crate::term::Term;
use crate::vterm::Lit;

/// One literal in a Maude term — either an interned variable, a fresh
/// variable produced by Maude in a substitution, or an interned constant.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MaudeLit {
    MaudeVar(u64, LSort),
    FreshVar(u64, LSort),
    MaudeConst(u64, LSort),
}

/// An "MTerm" — a `Term` over `MaudeLit`.
pub type MTerm = Term<MaudeLit>;

/// A Maude substitution — list of `((sort, idx), term)` pairs.
pub type MSubst = Vec<((LSort, u64), MTerm)>;

// =============================================================================
// Conversion context
// =============================================================================

/// Two-way binding map between our `LNTerm` literals and `MaudeLit`s. We
/// generate fresh integer ids the first time we see a literal, and remember
/// the assignment so subsequent uses of the same literal share an id (so
/// Maude can recognise variable equality).
#[derive(Debug, Default, Clone)]
pub struct ConvCtx {
    /// Forward: `Lit<Name, LVar> -> MaudeLit`.
    forward: BTreeMap<Lit<Name, LVar>, MaudeLit>,
    /// Inverse map (built when we want to translate back).
    inverse: BTreeMap<MaudeLit, Lit<Name, LVar>>,
    /// Counters per sort for variables.
    var_counters: BTreeMap<LSort, u64>,
    /// Counters per sort for constants.
    const_counters: BTreeMap<LSort, u64>,
}

impl ConvCtx {
    pub fn new() -> Self { Self::default() }

    pub fn fresh_var(&mut self, sort: LSort) -> u64 {
        let n = self.var_counters.entry(sort).or_insert(0);
        let id = *n;
        *n += 1;
        id
    }
    pub fn fresh_const(&mut self, sort: LSort) -> u64 {
        let n = self.const_counters.entry(sort).or_insert(0);
        let id = *n;
        *n += 1;
        id
    }

    pub fn bindings(&self) -> &BTreeMap<MaudeLit, Lit<Name, LVar>> {
        &self.inverse
    }

    /// Replace the inverse map. Used when handing the bindings back to the
    /// reverse-conversion to share the same id ↔ literal correspondence.
    pub fn set_bindings(&mut self, b: BTreeMap<MaudeLit, Lit<Name, LVar>>) {
        self.inverse = b;
    }
}

// =============================================================================
// Sort lookup for constants
// =============================================================================

/// `sortOfName` — the sort of a `Name` literal.
pub fn sort_of_name(n: &Name) -> LSort {
    match n.tag {
        NameTag::Fresh => LSort::Fresh,
        NameTag::Pub => LSort::Pub,
        NameTag::Nat => LSort::Nat,
        NameTag::Node => LSort::Node,
    }
}

// =============================================================================
// LNTerm -> MTerm (forward)
// =============================================================================

/// Convert an `LNTerm` to an `MTerm`. Allocates fresh ids in `ctx` for
/// any new literals encountered.
pub fn lterm_to_mterm_global(t: &LNTerm, ctx: &mut ConvCtx) -> MTerm {
    match t {
        Term::Lit(lit) => Term::Lit(import_lit(lit, ctx)),
        Term::App(sym, args) => {
            let new_args: Vec<MTerm> = args.iter().map(|a| lterm_to_mterm_global(a, ctx)).collect();
            Term::App(sym.clone(), new_args.into())
        }
    }
}

fn import_lit(l: &Lit<Name, LVar>, ctx: &mut ConvCtx) -> MaudeLit {
    if let Some(m) = ctx.forward.get(l) {
        return m.clone();
    }
    let m = match l {
        Lit::Var(lv) => {
            let id = ctx.fresh_var(lv.sort);
            MaudeLit::MaudeVar(id, lv.sort)
        }
        Lit::Con(n) => {
            let s = sort_of_name(n);
            let id = ctx.fresh_const(s);
            MaudeLit::MaudeConst(id, s)
        }
    };
    ctx.forward.insert(l.clone(), m.clone());
    ctx.inverse.insert(m.clone(), l.clone());
    m
}

// =============================================================================
// MTerm -> LNTerm (backward)
// =============================================================================

/// Convert an `MTerm` back to an `LNTerm` using the inverse bindings stored
/// in `ctx`. Variables introduced by Maude (`FreshVar`) get fresh `LVar`s
/// with names from `name_hint`. `MaudeConst`s must already be in the
/// bindings; otherwise we panic, mirroring the Haskell behaviour.
pub fn mterm_to_lnterm(
    t: &MTerm,
    ctx: &mut ConvCtx,
    name_hint: &str,
    next_idx: &mut u64,
) -> LNTerm {
    match t {
        Term::Lit(ml) => {
            // First, see if it's already in our inverse map — that means
            // it's one of the variables/constants we sent to Maude.
            if let Some(orig) = ctx.inverse.get(ml).cloned() {
                return Term::Lit(orig);
            }
            // Sort-tolerant fallback: Maude can return a var with the
            // same idx but a widened sort (e.g. our `~k1:Fresh:6` may
            // come back as `~k1:Msg:6`). Recover the canonical original
            // LVar so subst lookups downstream don't see two distinct
            // (name, sort, idx) instances for the same logical variable.
            if let MaudeLit::MaudeVar(idx, sort) = ml {
                if let Some(orig) = lookup_canonical_var_lit(ctx, *sort, *idx) {
                    return Term::Lit(orig);
                }
            }
            // Otherwise it must be a Maude-introduced fresh variable.
            match ml {
                MaudeLit::FreshVar(_, sort) | MaudeLit::MaudeVar(_, sort) => {
                    let lv = LVar::new(name_hint.to_string(), *sort, *next_idx);
                    *next_idx += 1;
                    let lit = Lit::Var(lv);
                    ctx.inverse.insert(ml.clone(), lit.clone());
                    Term::Lit(lit)
                }
                MaudeLit::MaudeConst(_, _) => {
                    panic!("mterm_to_lnterm: unknown constant {:?}", ml);
                }
            }
        }
        Term::App(sym, args) => {
            let new_args: Vec<LNTerm> = args
                .iter()
                .map(|a| mterm_to_lnterm(a, ctx, name_hint, next_idx))
                .collect();
            // Application via the smart constructors so AC/C normalisation
            // is preserved.  Mirrors HS `mTermToLNTerm`'s
            //   `go (FApp o as) = fApp o <$> mapM (go . viewTerm) as`
            // (Term/Maude/Types.hs:88): `fApp` dispatches to `fAppAC`
            // (flatten+sort) for AC symbols AND `fAppC` (sort) for C
            // symbols (`em`/EMap).  Crucially the sort happens AFTER the
            // child args have been back-converted from `MaudeVar`s to the
            // canonical `LVar`s, so `em`'s two args are ordered by the FULL
            // `LVar` order (idx-first), not by the transient Maude-side
            // ordering.  Routing only `FunSym::Ac` through the smart
            // constructor (and building `FunSym::C(EMap)` directly) left
            // `em` args in Maude's back-conversion order, producing
            // `em(XB.10, x.9)` where HS prints the sorted `em(x.9, XB.10)`.
            crate::term::f_app(sym.clone(), new_args)
        }
    }
}

// =============================================================================
// Substitution conversion helpers (vfresh / vfree variants)
// =============================================================================

/// Information needed to translate a Maude substitution back to an LNSubst.
/// The Haskell uses `BindT` to share the variable map. We thread `ConvCtx`
/// explicitly.
pub fn substitute_lookup_var(
    ctx: &ConvCtx,
    sort: LSort,
    idx: u64,
) -> Option<LVar> {
    // Strict lookup first.
    if let Some(lv) = ctx.inverse.get(&MaudeLit::MaudeVar(idx, sort))
        .and_then(|l| if let Lit::Var(lv) = l { Some(lv.clone()) } else { None })
    {
        return Some(lv);
    }
    // Sort-tolerant fallback: Maude sometimes widens a variable's sort
    // when constructing response terms (e.g. our `~k1:Fresh:6` may be
    // referenced as `~k1:Msg:6` in the returned substitution). Look up
    // by (idx, ANY sort) so we recover the original LVar identity.
    // Without this, `mterm_to_lnterm` creates a fresh LVar with Maude's
    // reported (widened) sort, producing a (name, sort, idx) collision
    // with the original — breaking subst lookups downstream. This is
    // the root cause of TESLA's Sender0a chain artifact.
    for sort_candidate in &[LSort::Pub, LSort::Fresh, LSort::Nat, LSort::Msg, LSort::Node] {
        if *sort_candidate == sort { continue; }
        if let Some(lv) = ctx.inverse.get(&MaudeLit::MaudeVar(idx, *sort_candidate))
            .and_then(|l| if let Lit::Var(lv) = l { Some(lv.clone()) } else { None })
        {
            return Some(lv);
        }
    }
    None
}

/// Like `substitute_lookup_var` but for term-reconstruction: returns
/// the matched literal (not just the LVar) so that callers in
/// `mterm_to_lnterm` can reuse the canonical original LVar instead of
/// fabricating a sort-mismatched fresh one.
pub fn lookup_canonical_var_lit(
    ctx: &ConvCtx,
    sort: LSort,
    idx: u64,
) -> Option<Lit<Name, LVar>> {
    if let Some(l) = ctx.inverse.get(&MaudeLit::MaudeVar(idx, sort)).cloned() {
        return Some(l);
    }
    for sort_candidate in &[LSort::Pub, LSort::Fresh, LSort::Nat, LSort::Msg, LSort::Node] {
        if *sort_candidate == sort { continue; }
        if let Some(l) = ctx.inverse.get(&MaudeLit::MaudeVar(idx, *sort_candidate)).cloned() {
            return Some(l);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vterm::var_term;

    #[test]
    fn round_trip_var() {
        let v = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = var_term(v.clone());
        let _ = t;
        // Direct construction with the lit literal so we don't need to
        // construct an LNTerm from an LVar via var_term (which expects
        // a variable type matching the LNTerm var type).
        let lit_v = Lit::Var(v);
        let t2: LNTerm = Term::Lit(lit_v.clone());
        let mut ctx = ConvCtx::new();
        let mt = lterm_to_mterm_global(&t2, &mut ctx);
        let mut next = 0;
        let back = mterm_to_lnterm(&mt, &mut ctx, "x", &mut next);
        assert_eq!(t2, back);
    }

    /// Regression for #330: `mterm_to_lnterm` must sort `em` (C/EMap) args
    /// by the FINAL `LVar` order, not leave them in Maude's back-conversion
    /// order.  An MTerm `em(<id for x.10>, <id for x.9>)` whose args map
    /// back to `x.10` and `x.9` must come back as `em(x.9, x.10)` (idx-first
    /// `LVar` order), matching HS `mTermToLNTerm`'s `fApp o`/`fAppC EMap`.
    #[test]
    fn emap_args_sorted_by_final_lvar_order() {
        use crate::function_symbols::{CSym, FunSym};
        // Build the MaudeVar ids in the REVERSE-of-sorted order: id 0 binds
        // to the larger var (x.10), id 1 to the smaller (x.9).  So the raw
        // MTerm `em(x0, x1)` is em(x.10, x.9) — unsorted.
        let x10 = LVar::new("x", LSort::Msg, 10);
        let x9 = LVar::new("x", LSort::Msg, 9);
        let mut ctx = ConvCtx::new();
        let m0 = MaudeLit::MaudeVar(0, LSort::Msg);
        let m1 = MaudeLit::MaudeVar(1, LSort::Msg);
        ctx.inverse.insert(m0.clone(), Lit::Var(x10.clone()));
        ctx.inverse.insert(m1.clone(), Lit::Var(x9.clone()));

        let mt: MTerm = Term::App(
            FunSym::C(CSym::EMap),
            vec![Term::Lit(m0), Term::Lit(m1)].into(),
        );
        let mut next = 100;
        let back = mterm_to_lnterm(&mt, &mut ctx, "x", &mut next);

        // Expected: em(x.9, x.10) — args sorted idx-first.
        let expected: LNTerm = crate::term::f_app_c(
            CSym::EMap,
            vec![
                Term::Lit(Lit::Var(x9)),
                Term::Lit(Lit::Var(x10)),
            ],
        );
        assert_eq!(back, expected);
        // And concretely: first arg is x.9, not x.10.
        if let Term::App(_, args) = &back {
            assert_eq!(
                args[0],
                Term::Lit(Lit::Var(LVar::new("x", LSort::Msg, 9)))
            );
        } else {
            panic!("expected an App");
        }
    }
}
