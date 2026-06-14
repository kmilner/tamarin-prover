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

use crate::function_symbols::{AcSym, FunSig, FunSym};
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
    let irreducible = &msig.irreducible_fun_syms;
    fn go(t: &LNTerm, irreducible: &FunSig) -> Option<bool> {
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
                    for a in args.iter() {
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
    go(t, irreducible)
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

/// `nfViaHaskell` — pure structural normal-form check.  Mirrors HS
/// `Term/Rewriting/Norm.hs:54-127` (`nfViaHaskell`).  Returns `true`
/// iff `t` is in normal form according to the structural rules of the
/// signature, **independent of any AC canonicalisation that Maude
/// might apply**.  This is critical: a term like `mult(tid, x)` and
/// `mult(x, tid)` are *both* in normal form by HS's structural check
/// — neither contains `one`, `DH_neutral`, nested products, or invalid
/// patterns — even though Maude's `reduce` would canonicalise them to
/// the same AC form.  Using `maude.reduce(t) == t` as the NF predicate
/// (the previous Rust behaviour) wrongly flagged AC-reordered terms as
/// "creates non-normal", over-filtering `simpMinimize` arms in
/// `substCreatesNonNormalTerms` and causing wrong-verified outcomes on
/// DH protocols (JKL_TS2_2004{,_KI_wPFS} key-secrecy lemmas).
///
/// HS-faithful pattern set (`nfViaHaskell` lines 60-99):
///   - irreducible top: walk subterms
///   - reducible exponent / inverse / mult / xor / pmult / emap
///     patterns: return `false`
///   - subterm-rule LHS matches: return `false`
///   - else: walk subterms
pub fn nf_via_haskell(msig: &MaudeSig, t: &LNTerm) -> bool {
    go_nf(t, msig, &msig.irreducible_fun_syms)
}

fn go_nf(t: &LNTerm, msig: &MaudeSig, irreducible: &FunSig) -> bool {
    use crate::function_symbols::{
        AcSym, DH_NEUTRAL_SYM_STRING, EXP_SYM_STRING, INV_SYM_STRING, ONE_SYM_STRING,
        ZERO_SYM_STRING,
    };
    match t {
        Term::Lit(_) => true,
        Term::App(sym, args) => {
            // 1. Irreducible NoEq top: walk subterms.
            // HS-faithful: HS's `nfViaHaskell` (Norm.hs:62) checks
            // `FAppNoEq o ts | (NoEq o) \`S.member\` irreducible` — the
            // irreducible-set check is gated by `FAppNoEq` (i.e. NoEq
            // function symbols only).  AC symbols like Mult are kept in
            // `irreducible_fun_syms` for OTHER consumers (Sources.hs:177
            // `maybeNonNormalTerms` uses `S.member` on the FUN set to
            // decide which subterms to NOT include), but Norm.hs's NF
            // check uses pattern matching on `FAppNoEq` which only
            // matches NoEq symbols.  Without this gate, RS treated
            // `Mult(tid, ekI, ekR, inv(tid))` as NF (skipped section 5's
            // invalidMult check entirely), under-filtering
            // simpMinimize and admitting AC variants HS rejects.
            // FList also counts as irreducible (HS: `FList ts -> all go ts`).
            if matches!(sym, FunSym::NoEq(_)) && irreducible.contains(sym) {
                return args.iter().all(|a| go_nf(a, msig, irreducible));
            }
            if matches!(sym, FunSym::List) {
                return args.iter().all(|a| go_nf(a, msig, irreducible));
            }
            // 2. Nullary constants in NF (One, DHNeutral, Zero, NatOne).
            if let FunSym::NoEq(s) = sym {
                if args.is_empty()
                    && (s.name == ONE_SYM_STRING
                        || s.name == DH_NEUTRAL_SYM_STRING
                        || s.name == ZERO_SYM_STRING
                        || s.name == crate::function_symbols::NAT_ONE_SYM_STRING)
                {
                    return true;
                }
            }
            // 3. Subterm-rule LHS match → reducible.  HS uses
            //    `solveMatchLNTerm (t `matchWith` lhs)` (Norm.hs:104-110).
            //    All builtin subterm rules (pair / senc / sdec / aenc /
            //    adec / sign / verify / ...) have AC-free LHS, so the
            //    no-AC matcher is sufficient.  See subterm_rule.rs and
            //    builtin.rs.
            for rule in &msig.st_rules {
                if rule_applies(t, &rule.lhs, &rule.rhs.term) {
                    return false;
                }
            }
            // 4. Reducible exponent / inverse / mult / xor patterns.
            if let FunSym::NoEq(s) = sym {
                if s.name == EXP_SYM_STRING && args.len() == 2 {
                    // (a ^ b) ^ c → reducible
                    if let Term::App(FunSym::NoEq(s2), _) = &args[0] {
                        if s2.name == EXP_SYM_STRING { return false; }
                    }
                    // a ^ 1 → reducible
                    if is_nullary(&args[1], ONE_SYM_STRING) { return false; }
                    // DH_neutral ^ b → reducible
                    if is_nullary(&args[0], DH_NEUTRAL_SYM_STRING) { return false; }
                    // else walk subterms
                    return go_nf(&args[0], msig, irreducible)
                        && go_nf(&args[1], msig, irreducible);
                }
                if s.name == INV_SYM_STRING && args.len() == 1 {
                    // inv(inv(_)) → reducible
                    if let Term::App(FunSym::NoEq(s2), _) = &args[0] {
                        if s2.name == INV_SYM_STRING { return false; }
                    }
                    // inv(mult(...)) where any factor is inverse → reducible
                    if let Term::App(FunSym::Ac(AcSym::Mult), inner_args) = &args[0] {
                        if inner_args.iter().any(is_inverse) { return false; }
                    }
                    // inv(one) → reducible
                    if is_nullary(&args[0], ONE_SYM_STRING) { return false; }
                    return go_nf(&args[0], msig, irreducible);
                }
                if s.name == crate::function_symbols::PMULT_SYM_STRING && args.len() == 2 {
                    // pmult(_, pmult(_,_)) → reducible
                    if let Term::App(FunSym::NoEq(s2), _) = &args[1] {
                        if s2.name == crate::function_symbols::PMULT_SYM_STRING { return false; }
                    }
                    // pmult(one, _) → reducible
                    if is_nullary(&args[0], ONE_SYM_STRING) { return false; }
                    return go_nf(&args[0], msig, irreducible)
                        && go_nf(&args[1], msig, irreducible);
                }
            }
            // 5. AC-headed reducible patterns.
            if let FunSym::Ac(ac) = sym {
                match ac {
                    AcSym::Mult => {
                        // contains one / DH_neutral, nested mult, or invalidMult → reducible
                        if args.iter().any(|a| is_nullary(a, ONE_SYM_STRING)) { return false; }
                        if args.iter().any(|a| is_nullary(a, DH_NEUTRAL_SYM_STRING)) { return false; }
                        if args.iter().any(is_product) { return false; }
                        if invalid_mult(args) { return false; }
                        return args.iter().all(|a| go_nf(a, msig, irreducible));
                    }
                    AcSym::Xor => {
                        if args.iter().any(|a| is_nullary(a, ZERO_SYM_STRING)) { return false; }
                        if args.iter().any(is_xor) { return false; }
                        if invalid_xor(args) { return false; }
                        return args.iter().all(|a| go_nf(a, msig, irreducible));
                    }
                    AcSym::Union | AcSym::NatPlus => {
                        return args.iter().all(|a| go_nf(a, msig, irreducible));
                    }
                }
            }
            // 6. C-headed (FEMap) reducible patterns.
            if let FunSym::C(_) = sym {
                // em(_, pmult(_,_)) or em(pmult(_,_), _) → reducible
                if args.len() == 2 {
                    if let Term::App(FunSym::NoEq(s2), _) = &args[0] {
                        if s2.name == crate::function_symbols::PMULT_SYM_STRING { return false; }
                    }
                    if let Term::App(FunSym::NoEq(s2), _) = &args[1] {
                        if s2.name == crate::function_symbols::PMULT_SYM_STRING { return false; }
                    }
                }
                return args.iter().all(|a| go_nf(a, msig, irreducible));
            }
            // 7. Default fallthrough: walk subterms (HS:
            //    `FAppNoEq _ ts -> all go ts`, `FAppC _ ts -> all go ts`).
            args.iter().all(|a| go_nf(a, msig, irreducible))
        }
    }
}

fn is_nullary(t: &LNTerm, name: &[u8]) -> bool {
    if let Term::App(FunSym::NoEq(s), args) = t {
        s.name == name && args.is_empty()
    } else { false }
}

fn is_inverse(t: &LNTerm) -> bool {
    use crate::function_symbols::INV_SYM_STRING;
    if let Term::App(FunSym::NoEq(s), _) = t { s.name == INV_SYM_STRING } else { false }
}

fn is_product(t: &LNTerm) -> bool {
    matches!(t, Term::App(FunSym::Ac(AcSym::Mult), _))
}

fn is_xor(t: &LNTerm) -> bool {
    matches!(t, Term::App(FunSym::Ac(AcSym::Xor), _))
}

/// `invalidMult` — HS `Norm.hs:112-118`.  Detects mult patterns that
/// are not in NF due to inverse cancellation.
fn invalid_mult(ts: &[LNTerm]) -> bool {
    use crate::function_symbols::AcSym;
    // Partition into (inverses, non-inverses).
    let (inverses, factors): (Vec<&LNTerm>, Vec<&LNTerm>) =
        ts.iter().partition(|t| is_inverse(t));
    match inverses.len() {
        0 => false,
        1 => {
            // Single inverse: peel its inner.
            let inv_arg = match inverses[0] {
                Term::App(_, a) if !a.is_empty() => &a[0],
                _ => return false,
            };
            // Case: inv(mult(ifactors)) — check ifactors vs factors overlap
            if let Term::App(FunSym::Ac(AcSym::Mult), ifactors) = inv_arg {
                let ifactors_refs: Vec<&LNTerm> = ifactors.iter().collect();
                // (ifactors \\ factors /= ifactors) ||
                // (factors  \\ ifactors /= factors)
                // i.e. the multiset-difference removes something on either side.
                return multiset_diff_changes(&ifactors_refs, &factors)
                    || multiset_diff_changes(&factors, &ifactors_refs);
            }
            // Case: inv(t) — invalid if t `elem` factors.
            factors.iter().any(|f| **f == *inv_arg)
        }
        _ => true, // 2+ inverses → invalid
    }
}

/// Returns true iff multiset-difference `xs \\ ys` differs from `xs`,
/// i.e. at least one element of `xs` is also in `ys`.  Mirrors Haskell
/// `(\\)` (Data.List) on the underlying multisets.
fn multiset_diff_changes(xs: &[&LNTerm], ys: &[&LNTerm]) -> bool {
    let mut consumed: Vec<bool> = vec![false; ys.len()];
    let mut removed_any = false;
    for x in xs {
        for (i, y) in ys.iter().enumerate() {
            if !consumed[i] && **x == **y {
                consumed[i] = true;
                removed_any = true;
                break;
            }
        }
    }
    removed_any
}

/// `invalidXor` — HS `Norm.hs:120-123`.  True iff `ts` contains
/// duplicates.
fn invalid_xor(ts: &[LNTerm]) -> bool {
    // O(n^2) is fine here — typical xor arities are tiny.
    for i in 0..ts.len() {
        for j in (i + 1)..ts.len() {
            if ts[i] == ts[j] { return true; }
        }
    }
    false
}

/// `struleApplicable` — HS `Norm.hs:104-110`.  Returns true iff the
/// rule's LHS matches `t` AND the rule actually rewrites `t` to
/// something different (when the RHS is a constant).
fn rule_applies(t: &LNTerm, lhs: &LNTerm, rhs: &LNTerm) -> bool {
    use crate::rewriting::Match;
    let problem = Match::match_with(t.clone(), lhs.clone());
    let matched = crate::unification::solve_match_lterm_no_ac(
        &|n| crate::lterm::sort_of_name(n),
        problem,
    );
    // HS: StRhs [] s -> not (t == s) ; StRhs _ _ -> True
    // The `StRhs [] s` case (RHS is a closed constant — no LHS-positions)
    // can be detected by checking `frees(rhs).is_empty() && positions_in_lhs == 0`,
    // but the StRhs struct in RS stores `positions` separately.  For the
    // builtin rules used in tamarin, RHS is always either a variable that
    // appears in LHS (e.g. `fst(pair(x,y)) → x`) or a constant.  When it
    // appears in LHS, rule_applies returning True iff matched.is_some()
    // is safe (the rewrite always changes `t` because the LHS structure
    // is decomposed).  When RHS is a constant, returning True iff
    // matched.is_some() && t != rhs preserves HS's behaviour.
    match matched {
        None => false,
        Some(_) => {
            if crate::lterm::frees(rhs).is_empty() {
                t != rhs
            } else {
                true
            }
        }
    }
}

/// Subterms that *might* not be in normal form. Used by
/// wellformedness / contradiction checks to limit the number of
/// Maude callouts.
pub fn maybe_not_nf_subterms(msig: &MaudeSig, t: &LNTerm) -> Vec<LNTerm> {
    let mut out = Vec::new();
    let irreducible = &msig.irreducible_fun_syms;
    fn go(t: &LNTerm, irreducible: &FunSig, out: &mut Vec<LNTerm>) {
        match t {
            Term::Lit(_) => {}
            Term::App(sym, args) => {
                if irreducible.contains(sym) {
                    for a in args.iter() { go(a, irreducible, out); }
                } else {
                    out.push(t.clone());
                }
            }
        }
    }
    go(t, irreducible, &mut out);
    out
}

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
    #[allow(non_snake_case)]
    fn nf_via_haskell_detects_inverse_cancellation() {
        let path = match maude_path() { Some(p) => p, None => return };
        let mut sig = crate::maude_sig::pair_maude_sig();
        sig.enable_dh = true;
        sig = sig.refresh();
        let h = MaudeHandle::start(&path, sig.clone()).unwrap();
        let tid = LVar::new("tid", LSort::Fresh, 0);
        let ekI = LVar::new("ekI", LSort::Fresh, 0);
        let ekR = LVar::new("ekR", LSort::Fresh, 0);
        let tid_term: LNTerm = Term::Lit(Lit::Var(tid.clone()));
        let ekI_term: LNTerm = Term::Lit(Lit::Var(ekI));
        let ekR_term: LNTerm = Term::Lit(Lit::Var(ekR));
        let inv_tid: LNTerm = Term::App(
            FunSym::NoEq(crate::function_symbols::inv_sym()),
            vec![tid_term.clone()].into(),
        );
        let mult: LNTerm = Term::App(
            FunSym::Ac(AcSym::Mult),
            vec![tid_term, ekI_term, ekR_term, inv_tid].into(),
        );
        // Test: mult(tid, ekI, ekR, inv(tid)) should NOT be in NF
        // (invalid_mult fires because tid appears as a factor and inside inv).
        assert!(!nf_via_haskell(&h.maude_sig(), &mult),
            "mult(tid, ekI, ekR, inv(tid)) should be non-NF");
    }

    #[test]
    fn maybe_not_nf_subterms_lit_empty() {
        let sig = pair_maude_sig();
        let v = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = Term::Lit(Lit::Var(v));
        assert!(maybe_not_nf_subterms(&sig, &t).is_empty());
    }
}
