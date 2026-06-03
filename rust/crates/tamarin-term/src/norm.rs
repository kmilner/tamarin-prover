//! Port of `Term.Rewriting.Norm` — normalisation and normal-form
//! checks via the Maude bridge.
//!
//! Tamarin uses two strategies:
//! 1. **Maude-backed normalisation** (`norm`) — simply asks Maude to
//!    `reduce` the term modulo the theory.
//! 2. **Haskell-side normal-form check** (`nf_via_haskell`) — a
//!    structural walk that returns `false` early when an obviously-
//!    reducible top construct is detected, avoiding a Maude callout
//!    for negative cases.
//!
//! For the Rust port we expose the Maude-backed `norm` directly and
//! a structural `nf` check that returns `Some(true)` / `Some(false)`
//! when the answer is decidable from syntax alone, or `None` to
//! defer to Maude.

use std::collections::BTreeSet;

use crate::function_symbols::{AcSym, FunSym, NoEqSym};
use crate::lterm::LNTerm;
use crate::maude_proc::{MaudeError, MaudeHandle};
use crate::maude_sig::MaudeSig;
use crate::term::Term;

/// `norm` — normalise a term modulo the configured theory by passing
/// it to Maude's `reduce` operator.
pub fn norm(maude: &MaudeHandle, t: &LNTerm) -> Result<LNTerm, MaudeError> {
    // Variable / constant literals are already normal — skip the
    // Maude round-trip for them.
    if matches!(t, Term::Lit(_)) { return Ok(t.clone()); }
    maude.reduce(t)
}

/// `nf_via_maude` — normal-form check by computing the normal form
/// and comparing.
pub fn nf_via_maude(maude: &MaudeHandle, t: &LNTerm) -> Result<bool, MaudeError> {
    let n = norm(maude, t)?;
    Ok(&n == t)
}

/// `normSubstVFresh'` — normalise every range term of a `LNSubstVFresh`
/// via Maude.
///
/// HS canonical (`lib/term/src/Term/Rewriting/Norm.hs:158-159`):
/// ```haskell
/// normSubstVFresh' :: LNSubstVFresh -> WithMaude LNSubstVFresh
/// normSubstVFresh' s = reader $ \hnd ->
///     mapRangeVFresh (\t -> norm' t `runReader` hnd) s
/// ```
///
/// Behaviour: walk the substitution, replacing each range term with
/// `norm hnd t` (falling back to the original term on Maude error —
/// matches the lenient call sites already in the port).
pub fn norm_subst_vfresh(
    maude: &MaudeHandle,
    s: &crate::subst_vfresh::LNSubstVFresh,
) -> crate::subst_vfresh::LNSubstVFresh {
    s.map_range(|t| match norm(maude, &t) {
        Ok(n) => n,
        Err(_) => t,
    })
}

/// Cheap structural NF check. Returns `Some(false)` for terms that
/// are clearly reducible (e.g. `inv(inv(_))`, `(t1 ^ t2) ^ t3`,
/// `1 ^ _`, `t * 1`, ...). Returns `Some(true)` if the term is
/// guaranteed normal (literals, applications under irreducible
/// symbols only). Returns `None` for cases the structural check
/// can't decide on its own.
pub fn nf_structural(msig: &MaudeSig, t: &LNTerm) -> Option<bool> {
    let irreducible: BTreeSet<&FunSym> = msig.irreducible_fun_syms.iter().collect();
    fn go(t: &LNTerm, irreducible: &BTreeSet<&FunSym>) -> Option<bool> {
        match t {
            Term::Lit(_) => Some(true),
            Term::App(sym, args) => {
                // Top-level reducible patterns we can recognise without
                // looking at sort information.
                if let Some(b) = obvious_reduction(t) {
                    return Some(!b); // obvious_reduction true → reducible → nf=false
                }
                if irreducible.contains(sym) || matches!(sym, FunSym::List | FunSym::C(_)) {
                    let mut all_known = true;
                    for a in args {
                        match go(a, irreducible) {
                            Some(false) => return Some(false),
                            Some(true) => {}
                            None => all_known = false,
                        }
                    }
                    return if all_known { Some(true) } else { None };
                }
                // Unknown reducibility: defer.
                None
            }
        }
    }
    go(t, &irreducible)
}

/// Recognise top-level shapes that are immediately reducible by the
/// built-in rewrite rules. Returns `true` if the term IS reducible.
fn obvious_reduction(t: &LNTerm) -> Option<bool> {
    use crate::function_symbols::INV_SYM_STRING;
    if let Term::App(FunSym::NoEq(s), args) = t {
        // inv(inv(_)) — reducible.
        if s.name == INV_SYM_STRING {
            if let Some(Term::App(FunSym::NoEq(s2), inner)) = args.first() {
                if s2.name == INV_SYM_STRING && inner.len() == 1 {
                    return Some(true);
                }
            }
        }
    }
    // (t1 ^ t2) ^ t3 — reducible by exp-down.
    if let Term::App(FunSym::NoEq(s), args) = t {
        const EXP: &[u8] = b"exp";
        if s.name == EXP && args.len() == 2 {
            // base is itself an exp?
            if let Some(Term::App(FunSym::NoEq(s2), _)) = args.first() {
                if s2.name == EXP { return Some(true); }
            }
            // exponent is `1`?
            if let Some(rhs) = args.get(1) {
                if is_one_constant(rhs) { return Some(true); }
            }
        }
    }
    // mult ts containing 1 / containing nested mult — reducible.
    if let Term::App(FunSym::Ac(AcSym::Mult), args) = t {
        if args.iter().any(is_one_constant) { return Some(true); }
        if args.iter().any(|a| matches!(a, Term::App(FunSym::Ac(AcSym::Mult), _))) {
            return Some(true);
        }
    }
    // xor with `zero` — reducible.
    if let Term::App(FunSym::Ac(AcSym::Xor), args) = t {
        if args.iter().any(is_zero_constant) { return Some(true); }
    }
    None
}

fn is_one_constant(t: &LNTerm) -> bool {
    if let Term::App(FunSym::NoEq(s), args) = t {
        s.name == crate::function_symbols::ONE_SYM_STRING && args.is_empty()
    } else { false }
}

fn is_zero_constant(t: &LNTerm) -> bool {
    if let Term::App(FunSym::NoEq(s), args) = t {
        s.name == crate::function_symbols::ZERO_SYM_STRING && args.is_empty()
    } else { false }
}

/// Subterms that *might* not be in normal form. Used by
/// wellformedness / contradiction checks to limit the number of
/// Maude callouts.
pub fn maybe_not_nf_subterms(msig: &MaudeSig, t: &LNTerm) -> Vec<LNTerm> {
    let mut out = Vec::new();
    let irreducible: BTreeSet<&FunSym> = msig.irreducible_fun_syms.iter().collect();
    fn go(t: &LNTerm, irreducible: &BTreeSet<&FunSym>, out: &mut Vec<LNTerm>) {
        match t {
            Term::Lit(_) => {}
            Term::App(sym, args) => {
                if irreducible.contains(sym) {
                    for a in args { go(a, irreducible, out); }
                } else {
                    out.push(t.clone());
                }
            }
        }
    }
    go(t, &irreducible, &mut out);
    out
}

/// Suppress unused warnings.
#[allow(dead_code)]
fn _suppress(_: NoEqSym) {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::{LNTerm, LSort, LVar};
    use crate::maude_sig::pair_maude_sig;
    use crate::vterm::Lit;

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        let candidates = [
            "/home/linuxbrew/.linuxbrew/bin/maude",
            "/usr/local/bin/maude",
            "maude",
        ];
        for c in &candidates {
            if std::path::Path::new(c).exists() { return Some((*c).to_string()); }
        }
        None
    }

    #[test]
    fn norm_var_skips_maude() {
        let path = match maude_path() { Some(p) => p, None => return };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let v = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = Term::Lit(Lit::Var(v));
        let n = norm(&h, &t).unwrap();
        assert_eq!(t, n);
    }

    #[test]
    fn nf_structural_lit_is_nf() {
        let sig = pair_maude_sig();
        let v = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = Term::Lit(Lit::Var(v));
        assert_eq!(nf_structural(&sig, &t), Some(true));
    }

    #[test]
    fn maybe_not_nf_subterms_lit_empty() {
        let sig = pair_maude_sig();
        let v = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = Term::Lit(Lit::Var(v));
        assert!(maybe_not_nf_subterms(&sig, &t).is_empty());
    }
}
