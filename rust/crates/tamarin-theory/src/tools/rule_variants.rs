//! Port of `Theory.Tools.RuleVariants` — computes the AC-variants of
//! a protocol rule via the Maude bridge.
//!
//! The Haskell reference does an "abstract → narrow → substitute →
//! simplify" dance:
//!
//! 1. Walk the rule's facts and replace each complex (reducible)
//!    sub-term with a fresh variable, remembering the bindings.
//! 2. Pack the replaced terms into a single tuple and ask Maude for
//!    its variants — `MaudeHandle::variants(packed) -> Vec<MSubst>`.
//! 3. For each variant subst, compose with the abstraction-bindings
//!    subst and renormalise.
//! 4. Simplify via `simp_disjunction`.
//! 5. Wrap as a `ProtoRuleAC` with the surviving substitutions stored
//!    in its `variants` field.
//!
//! The full `abstrTerm` machinery (step 1 above) lives in
//! `abstract_rule_and_variants`, which is the HS-faithful production
//! path used by `run.rs` and the constraint solver's `context.rs`.
//! `variants_proto_rule` is a lighter helper that runs steps 2-5
//! directly on the rule's free variables (no abstraction); it is
//! retained for the callers that already have terms in a form Maude
//! can variant-narrow.

use tamarin_term::lterm::{LNTerm, LVar, Name};
use tamarin_term::maude_proc::{MaudeError, MaudeHandle};
use tamarin_term::subst::{apply_vterm, Subst};
use tamarin_term::subst_vfresh::LNSubstVFresh;
use tamarin_term::term::Term;

use crate::fact::Fact;
use crate::rule::{
    ProtoRuleAC, ProtoRuleACInfo, ProtoRuleE,
};

type LNSubst = Subst<Name, LVar>;

#[derive(Debug, Clone)]
pub enum VariantsError {
    Maude(String),
}

impl std::fmt::Display for VariantsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariantsError::Maude(s) => write!(f, "Maude error: {}", s),
        }
    }
}
impl std::error::Error for VariantsError {}
impl From<MaudeError> for VariantsError {
    fn from(e: MaudeError) -> Self { VariantsError::Maude(format!("{}", e)) }
}

/// `variantsProtoRule`: compute the AC-variants of a protocol rule.
/// Returns `Ok(None)` when Maude reports no non-trivial variants; the
/// caller can keep the rule as-is. Returns `Ok(Some(ac_rule))` with
/// the variant substitutions populated.
///
/// HS-faithful: mirrors `variantsProtoRule` (RuleVariants.hs:61-91):
///
/// ```haskell
/// x <- simpDisjunction hnd (const (const False)) (Disj substs)
/// case x of
///   (commonSubst, Nothing)         -> return $ makeRule abstrPsCsAs commonSubst trueDisj
///   (commonSubst, Just freshSubsts) -> return $ makeRule abstrPsCsAs commonSubst freshSubsts
/// ```
///
/// where `trueDisj = [emptySubstVFresh]` (RuleVariants.hs:120) and
/// `makeRule` (RuleVariants.hs:111-118) applies `commonSubst` to the
/// rule body and restricts the residual fresh substs to the new
/// frees.
pub fn variants_proto_rule(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> Result<Option<ProtoRuleAC>, VariantsError> {
    // Pack all rule terms into a single tuple so we get one
    // variants-call per rule.
    let Some(packed) = pack_rule_terms(rule) else {
        // No term arguments at all → no variants beyond the identity.
        return Ok(Some(make_proto_rule_ac(rule, &LNSubst::default(), vec![LNSubstVFresh::empty()])));
    };
    let raw = maude.variants(&packed)?;
    if raw.is_empty() {
        return Ok(None);
    }
    let substs: Vec<LNSubstVFresh> = raw.into_iter()
        .map(LNSubstVFresh::from_list)
        .collect();
    // HS-faithful `simpDisjunction hnd (const (const False)) (Disj substs)`
    // (RuleVariants.hs:82).  Routes through `simp1`'s full pipeline
    // including `simpSingleton` (EquationStore.hs:391, invoked at 361) — that pass
    // folds a singleton-variant disj into the free subst, which is
    // what HS's `commonSubst` carries.  Without this, the SplitG
    // residual retains entries that HS bakes into the rule body via
    // `makeRule`'s `apply commonSubst` (RuleVariants.hs:114-117) —
    // which is the root of the NAXOS_eCK_private Init_1-vs-Ltk_reveal
    // divergence.
    let (common_subst, residual) = crate::tools::equation_store::EquationStore::simp_disjunction_with_maude(
        substs, |_, _| false, maude);
    // HS `trueDisj = [emptySubstVFresh]` (RuleVariants.hs:120).
    let fresh_substs = residual.unwrap_or_else(|| vec![LNSubstVFresh::empty()]);
    Ok(Some(make_proto_rule_ac(rule, &common_subst, fresh_substs)))
}

/// Pack every term-argument of every fact in `rule` into a single
/// `list(...)` term so it can be passed to `MaudeHandle::variants`.
/// Returns `None` if the rule has no term arguments at all.
fn pack_rule_terms(rule: &ProtoRuleE) -> Option<LNTerm> {
    use tamarin_term::function_symbols::FunSym;
    let mut all = Vec::new();
    for f in &rule.premises   { all.extend(f.terms.iter().cloned()); }
    for f in &rule.actions    { all.extend(f.terms.iter().cloned()); }
    for f in &rule.conclusions { all.extend(f.terms.iter().cloned()); }
    if all.is_empty() { None }
    else { Some(Term::App(FunSym::List, all.into())) }
}

/// Build a `ProtoRuleAC` from a `ProtoRuleE` plus the precomputed
/// variants list.
///
/// HS `makeRule` (RuleVariants.hs:111-118) applies `commonSubst` (the
/// free part returned by `simpDisjunction`) to the rule body, then
/// restricts each fresh subst to the rule's surviving frees:
///
/// ```haskell
/// makeRule (ps, cs, as, nvs) subst freshSubsts0 =
///     Rule (ProtoRuleACInfo na attr (Disj freshSubsts) []) prems concs acts newvs
///   where prems = apply subst ps
///         concs = apply subst cs
///         acts  = apply subst as
///         newvs = apply subst nvs
///         freshSubsts = map (restrictVFresh (frees (prems, concs, acts, newvs))) freshSubsts0
/// ```
fn make_proto_rule_ac(
    rule: &ProtoRuleE,
    common_subst: &LNSubst,
    variants: Vec<LNSubstVFresh>,
) -> ProtoRuleAC {
    // Apply commonSubst to the rule body (HS apply subst {ps,cs,as,nvs}).
    let (premises, conclusions, actions, new_vars) = if common_subst.is_empty() {
        (
            rule.premises.clone(),
            rule.conclusions.clone(),
            rule.actions.clone(),
            rule.new_vars.clone(),
        )
    } else {
        let map_facts = |fs: &[Fact<LNTerm>]| -> Vec<Fact<LNTerm>> {
            fs.iter()
                .map(|f| f.clone().map(|t| apply_vterm(common_subst, t)))
                .collect()
        };
        (
            map_facts(&rule.premises),
            map_facts(&rule.conclusions),
            map_facts(&rule.actions),
            rule.new_vars.iter().map(|t| apply_vterm(common_subst, t.clone())).collect(),
        )
    };

    // Compute frees of the new rule body and restrict each variant
    // subst to those (HS: `map (restrictVFresh (frees (prems, concs, acts, newvs))) freshSubsts0`).
    use tamarin_term::lterm::HasFrees;
    let mut frees_set: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    for f in &premises {
        for t in &f.terms { t.for_each_free(&mut |v| { frees_set.insert(v.clone()); }); }
    }
    for f in &conclusions {
        for t in &f.terms { t.for_each_free(&mut |v| { frees_set.insert(v.clone()); }); }
    }
    for f in &actions {
        for t in &f.terms { t.for_each_free(&mut |v| { frees_set.insert(v.clone()); }); }
    }
    for t in &new_vars {
        t.for_each_free(&mut |v| { frees_set.insert(v.clone()); });
    }
    let frees_vec: Vec<LVar> = frees_set.into_iter().collect();
    let variants: Vec<LNSubstVFresh> = variants.into_iter()
        .map(|s| s.restrict(&frees_vec))
        .collect();

    let info = ProtoRuleACInfo {
        name: rule.info.name.clone(),
        attributes: rule.info.attributes.clone(),
        variants,
        loop_breakers: Vec::new(),
    };
    crate::rule::Rule {
        info,
        premises,
        conclusions,
        actions,
        new_vars,
    }
}

/// Like `expand_rule_variants`, but returns the raw variant substitutions
/// (the `Disj LNSubstVFresh` of `RuleACConstrs` in Haskell) — the
/// substitutions that should be installed as a SplitG goal via
/// `solve_rule_constraints`.
///
/// Haskell-faithful: keeps ALL variants Maude returns (including the
/// identity).  The identity variant corresponds to "destructor doesn't
/// reduce" — e.g. `adec(c, k)` stays as is when `c ≠ aenc(_, pk(k))`.
/// Filtering it out drops the no-narrowing case from the SplitG, so
/// downstream search misses the alternative where the term is irreducible.
///
/// Earlier versions of this function filtered out pure-renaming variants
/// ("matches `expand_rule_variants`' useful filter").  That was wrong:
/// `expand_rule_variants` produces the pre-applied variant *rules* (used
/// by the legacy `o.variants` path), where the identity rule duplicates
/// `o.rule` and is rightly skipped.  But the raw variant *substitutions*
/// (`Disj LNSubstVFresh` of Haskell's `RuleACConstrs`) need the identity
/// kept — it's what tells `solveRuleConstraints` to install a SplitG with
/// both narrowing and no-narrowing branches.
pub fn variant_substs_for_rule(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> Result<Vec<LNSubstVFresh>, VariantsError> {
    let ac = match variants_proto_rule(maude, rule)? {
        Some(ac) => ac,
        None => return Ok(Vec::new()),
    };
    Ok(ac.info.variants)
}

/// Port of Haskell `abstrRule` (RuleVariants.hs:93-109): walks every
/// fact-term in `rule` and replaces each reducible-headed sub-term
/// with a fresh `LVar`.  Returns the abstracted rule plus the
/// variant disjunction whose substs talk about the abstracted rule's
/// fresh vars (after composing Maude's variant substs over the
/// abstraction bindings).
///
/// The variant disjunction returned by Maude on the abstracted form
/// is composed with the abstraction substitution to produce the
/// final SplitG disjunction whose substs talk about the abstracted
/// rule's fresh vars (the z_i).
///
/// Returns `Ok(None)` when no reducible-headed sub-terms exist, in
/// which case `rule` is already canonical and needs no variants.
pub fn abstract_rule_and_variants(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> Result<Option<(ProtoRuleE, Vec<LNSubstVFresh>)>, VariantsError> {
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::lterm::HasFrees;
    let irreducible = maude.maude_sig().irreducible_fun_syms.clone();

    // Avoid clashes with the rule's existing free vars.  HS:
    // `convertRule \`evalFreshTAvoiding\` ru` — Fresh counter starts at
    // (max idx of rule's free vars) + 1.
    let avoid_max: u64 = {
        let m = std::cell::Cell::new(0u64);
        let visit = |v: &LVar| {
            if v.idx > m.get() { m.set(v.idx); }
        };
        for f in &rule.premises { f.terms.iter().for_each(|t| t.for_each_free(&mut |v| visit(v))); }
        for f in &rule.actions { f.terms.iter().for_each(|t| t.for_each_free(&mut |v| visit(v))); }
        for f in &rule.conclusions { f.terms.iter().for_each(|t| t.for_each_free(&mut |v| visit(v))); }
        for t in &rule.new_vars { t.for_each_free(&mut |v| visit(v)); }
        m.get()
    };
    // HS-faithful: `convertRule \`evalFreshTAvoiding\` ru`
    // (RuleVariants.hs:64) runs the variant computation in a Fresh monad
    // whose counter starts at `max(ru.idxs)+1` PER RULE.  Without this,
    // RS's global Maude counter keeps climbing across rules, so the
    // variant value vars (allocated via the Maude back-conversion's
    // `evalFreshAvoiding`) end up at much higher idxs than HS's — that's
    // the +12 offset between RS (~ltkS.19/20/21) and HS (~ltkS.7/8/9)
    // for Tutorial.spthy's Serv_1.
    //
    // `with_fresh_counter_from` clones the handle keeping the underlying
    // Maude PROCESS shared but with a fresh PER-CALL counter — exactly
    // HS's evalFreshTAvoiding semantics.
    let local_maude_owned = maude.with_fresh_counter_from(avoid_max);
    let maude: &MaudeHandle = &local_maude_owned;
    if std::env::var("TAM_DBG_FRESH_TRACE").is_ok() {
        eprintln!("[fresh-trace] rule={:?} avoid_max={} counter_at_entry={}",
            rule.info.name, avoid_max, maude.fresh_counter_peek());
    }

    fn name_hint(t: &LNTerm) -> String {
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Var(v)) => v.name.clone(),
            _ => "z".to_string(),
        }
    }

    // Memoization: original term → fresh LVar.  HS: `BindT` state over
    // `M.Map LNTerm LVar` (Bind.hs:54,76; RuleVariants.hs:93,106) ensures
    // each unique LNTerm gets ONE binding, reused on subsequent
    // encounters.  A `BTreeMap` mirrors HS's `M.Map` exactly: O(log n)
    // lookup AND an already term-`Ord`-sorted `M.toList` view (used below
    // as `sorted_bindings`), so no separate sort pass is needed.
    let mut bindings: std::collections::BTreeMap<LNTerm, LVar> =
        std::collections::BTreeMap::new();

    // HS-faithful `abstrTerm` (RuleVariants.hs:103-109).
    fn abstr_term(
        t: &LNTerm,
        irreducible: &std::collections::BTreeSet<FunSym>,
        bindings: &mut std::collections::BTreeMap<LNTerm, LVar>,
        maude: &MaudeHandle,
    ) -> LNTerm {
        // Irreducible head: recurse into args.
        if let Term::App(f, args) = t {
            if irreducible.contains(f) {
                return Term::App(
                    f.clone(),
                    args.iter().map(|a| abstr_term(a, irreducible, bindings, maude)).collect(),
                );
            }
        }
        // Catch-all: import binding (handles leaf vars AND reducible-head
        // App).  HS: `abstrTerm t = do at <- varTerm <$> importBinding ...`.
        if let Some(v) = bindings.get(t) {
            return Term::Lit(tamarin_term::vterm::Lit::Var(v.clone()));
        }
        let new_idx = maude.reserve_idxs(1);
        let v = LVar {
            name: name_hint(t),
            // HS-faithful `abstrTerm` (RuleVariants.hs:104):
            // `importBinding (\`LVar\` sortOfLNTerm t) t (getHint t)`.
            // `sort_of_lnterm` (lterm.rs:216) IS HS `sortOfLNTerm`:
            // Con -> sort_of_name (Fresh/Pub/Node/Nat by tag), Var ->
            // v.sort, NatPlus/NatOne -> Nat, _ -> Msg.
            sort: tamarin_term::lterm::sort_of_lnterm(t),
            idx: new_idx,
        };
        bindings.insert(t.clone(), v.clone());
        Term::Lit(tamarin_term::vterm::Lit::Var(v))
    }

    fn abstr_fact(
        f: &Fact<LNTerm>,
        irreducible: &std::collections::BTreeSet<FunSym>,
        bindings: &mut std::collections::BTreeMap<LNTerm, LVar>,
        maude: &MaudeHandle,
    ) -> Fact<LNTerm> {
        Fact {
            tag: f.tag.clone(),
            annotations: f.annotations.clone(),
            terms: f.terms.iter()
                .map(|t| abstr_term(t, irreducible, bindings, maude))
                .collect(),
        }
    }

    // HS-faithful: import ALL leaf vars FIRST (RuleVariants.hs:95
    // `mapM_ abstrTerm [varTerm v | v <- frees (prems0, concs0, acts0, nvs0)]`).
    // This populates the bindings map so leaf vars get RENAMED to fresh
    // idxs with name preserved (via getHint = lvarName for Var).  Without
    // this, abstractionSubst lacks leaf-var entries and downstream
    // composeVFresh leaves the original rule's free vars unrenamed, which
    // makes Maude's variant-witness allocation collide across variants.
    //
    // HS's `frees` (LTerm.hs:584-585) returns `sortednub . freesList` —
    // a SORT+DEDUP list, ordered by `Ord LVar = idx <> sort <> name`
    // (LTerm.hs:521-523).  Document-order iteration would assign fresh
    // idxs based on which fact mentions a variable first, which decides
    // the FIRST KEY of every Maude variant subst and hence the variants'
    // post-`S.fromList` sort order in HS's `simpDisjunction`.
    //
    // For wireguard's `Handshake_Init`, document order visits `pkR`
    // (premise `!F_StateInvariants(..., pkR, ...)`) before `~ekI`
    // (premise `Fr(~ekI)`), so `pkR` ends up at a smaller fresh idx
    // than `~ekI`; the variants then sort with `pkR` first → the
    // DH_neutral variant lands before the AC-decomposed one.  HS's
    // sorted `frees` puts `~ekI` (Fresh, idx 0, name "ekI") before
    // `pkR` (Msg, idx 0, name "pkR") via `Fresh < Msg` on the LSort
    // partial order, so `~ekI` gets the smaller fresh idx and the
    // AC-decomposed variant lands before DH_neutral — matching HS.
    //
    // HS-faithful `frees`: a BTreeSet sorts insertion by `Ord LVar`
    // and dedupes — exactly `sortednub` semantics.
    let mut leaf_set: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
    let mut visit = |v: &LVar| { leaf_set.insert(v.clone()); };
    for f in &rule.premises { f.terms.iter().for_each(|t| t.for_each_free(&mut visit)); }
    for f in &rule.actions { f.terms.iter().for_each(|t| t.for_each_free(&mut visit)); }
    for f in &rule.conclusions { f.terms.iter().for_each(|t| t.for_each_free(&mut visit)); }
    for t in &rule.new_vars { t.for_each_free(&mut visit); }
    for v in leaf_set {
        let leaf_term: LNTerm = Term::Lit(tamarin_term::vterm::Lit::Var(v));
        // The result is discarded; the side effect on `bindings` is
        // what matters.
        let _ = abstr_term(&leaf_term, &irreducible, &mut bindings, maude);
    }

    let prems: Vec<Fact<LNTerm>> = rule.premises.iter()
        .map(|f| abstr_fact(f, &irreducible, &mut bindings, maude)).collect();
    let concs: Vec<Fact<LNTerm>> = rule.conclusions.iter()
        .map(|f| abstr_fact(f, &irreducible, &mut bindings, maude)).collect();
    let acts: Vec<Fact<LNTerm>> = rule.actions.iter()
        .map(|f| abstr_fact(f, &irreducible, &mut bindings, maude)).collect();
    let nvs: Vec<LNTerm> = rule.new_vars.iter()
        .map(|t| abstr_term(t, &irreducible, &mut bindings, maude)).collect();

    // Count reducible-head abstractions: if zero, no useful variants.
    // (With leaf-rename, `bindings` always non-empty when rule has vars.)
    let has_reducible_abstraction = bindings.iter().any(|(t, _)| {
        matches!(t, Term::App(f, _) if !irreducible.contains(f))
    });
    if !has_reducible_abstraction {
        // HS's `variantsProtoRule` has NO such short-circuit: it abstracts
        // every free var and applies `renamePrecise` (RuleVariants.hs:64,
        // 78) even when the only variant is the identity.  For rules whose
        // vars are already in renamePrecise normal form (the common case)
        // the AC body equals the E body → `isTrivialProtoVariantAC` is True
        // → "has exactly the trivial AC variant", so the short-circuit is
        // faithful.  But when renamePrecise WOULD change a var — e.g. a rule
        // with two free vars sharing a name (`~ltk` and `ltk`), where it
        // disambiguates the second to `ltk.1` — the AC body differs from the
        // E body and HS prints the full `rule (modulo AC) ...` block.  Since
        // there are no reducible sub-terms, the sole variant IS the identity:
        // return `renamePrecise(rule)` with the trivial disjunction directly
        // (no Maude call).  This only diverges from the short-circuit for
        // rules renamePrecise actually rewrites (issue527's Register_pk).
        if rule_renames_under_precise(rule) {
            let (ac, substs) = rename_precise_rule_with_variants(
                rule.clone(), vec![LNSubstVFresh::empty()]);
            return Ok(Some((ac, substs)));
        }
        return Ok(None);
    }

    // Build the abstracted rule.
    let abstracted_rule = crate::rule::Rule::new(
        rule.info.clone(),
        prems,
        concs,
        acts,
    ).with_new_vars(nvs);

    // abstractionSubst (HS RuleVariants.hs:70-71):
    //   `eqsAbstr = map swap (M.toList bindings)` — list of (lvar, orig_term).
    //   `abstractionSubst = substFromList eqsAbstr` — FREE Subst.
    //
    // With leaf-rename, this includes BOTH leaf entries `(lv_renamed,
    // Var v_orig)` AND reducible entries `(z_i, complex_term)`.
    //
    // CRITICAL: HS's `bindings :: M.Map LNTerm LVar` is keyed by the
    // ORIGINAL term (`importBinding (\`LVar\` sortOfLNTerm t) t ...`,
    // RuleVariants.hs:104), and `M.toList bindings` therefore yields the
    // entries SORTED by the original term's `Ord` — NOT by insertion
    // order.  `abstractedTerms = map snd eqsAbstr` (RuleVariants.hs:69)
    // is consequently a term-`Ord`-sorted list, and it is exactly the
    // payload of the `get variants in MSG : list(cons(...))` Maude query
    // (`fAppList abstractedTerms`, RuleVariants.hs:72).  RS previously
    // walked `bindings` in INSERTION order (the order terms were first
    // visited), so the `list(...)` query had its arguments in a different
    // order than HS — which seeds Maude's persistent variable-name
    // interning table differently and flips the enumeration order of
    // AC-symmetric unifiers far downstream (the UM_three_pass
    // `CK_secure_UM3` `R_Complete_case_1↔case_2` arm swap at proof line
    // 1305).  Mirror `M.toList` by iterating the binding entries in
    // ORIGINAL-term key order.  Both `abstractionSubst` (substFromList —
    // itself a Map, so order-insensitive) and `abstractedTerms` (the
    // ordered query payload) read from this sorted view.  `bindings` is a
    // `BTreeMap`, so `.iter()` already yields entries in term-`Ord` key
    // order — exactly `M.toList`'s ordering, no explicit sort needed.
    let abstraction_pairs: Vec<(LVar, LNTerm)> = bindings.iter()
        .map(|(t, v)| (v.clone(), t.clone()))
        .collect();
    let abstraction_subst: LNSubst = Subst::from_list(abstraction_pairs.clone());

    // `abstractedTerms = map snd eqsAbstr` — the ORIGINAL terms.
    let abstracted_terms: Vec<LNTerm> = bindings.keys().cloned().collect();
    let packed = Term::App(FunSym::List, abstracted_terms.into());
    let raw_substs = maude.variants(&packed)?;
    if raw_substs.is_empty() {
        return Ok(None);
    }

    // HS-faithful `msubstToLSubstVFresh` (Maude/Types.hs:130) returns
    // `removeRenamings $ substFromListVFresh slist` — i.e. EVERY raw Maude
    // variant has its pure-rename entries dropped as part of the
    // back-conversion (Process.hs:273 `map (msubstToLSubstVFresh bindings)
    // <$> parseVariantsReply`).  So by the time HS's `variantSubsts`
    // (RuleVariants.hs:72) reach BOTH `isFreshRedundant vsubst`
    // (RuleVariants.hs:77) AND `composeVFresh vsubst abstractionSubst`
    // (RuleVariants.hs:75), each `vsubst` is already removeRenamings'd.
    //
    // RS's `maude.variants()` (maude_proc.rs:1418) does NOT apply
    // `remove_renamings` (unlike the unify path, maude_proc.rs:886-892), so
    // we clean each variant HERE — once, up front — to match HS.  This puts
    // the H20/`isFreshRedundant` filter (below) and the compose loop on the
    // SAME cleaned form HS uses.  `remove_renamings` filters entries WITHIN
    // each subst (never the list), preserving the Maude-determined variant
    // ordering that the per-variant Ord sort relies on.
    let raw_substs: Vec<Vec<(LVar, LNTerm)>> = raw_substs.into_iter()
        .map(|pairs| LNSubstVFresh::from_list(pairs).remove_renamings().to_list())
        .collect();

    // HS pipeline per variant (RuleVariants.hs:73-77):
    //   restrictVFresh (frees abstrPsCsAs) $
    //     removeRenamings $ normSubstVFresh' $
    //     composeVFresh vsubst abstractionSubst
    //
    // We use the new `compose_vfresh` helper (mirrors HS's full pipeline:
    // extendWithRenaming + freshToFreeAvoidingFast + compose + freeToFreshRaw).
    // Without this, two variants whose Maude-back-conversion shapes
    // happen to collide end up with structurally-identical range vars
    // and collapse at perform_split (split_case ordering bug).
    let abstr_frees: Vec<LVar> = {
        let mut s: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        for f in &abstracted_rule.premises {
            for t in &f.terms { t.for_each_free(&mut |v| { s.insert(v.clone()); }); }
        }
        for f in &abstracted_rule.actions {
            for t in &f.terms { t.for_each_free(&mut |v| { s.insert(v.clone()); }); }
        }
        for f in &abstracted_rule.conclusions {
            for t in &f.terms { t.for_each_free(&mut |v| { s.insert(v.clone()); }); }
        }
        for t in &abstracted_rule.new_vars {
            t.for_each_free(&mut |v| { s.insert(v.clone()); });
        }
        s.into_iter().collect()
    };

    if std::env::var("TAM_DBG_HS_COMPOSE").is_ok() {
        eprintln!("[hs-compose] rule={:?} #variants={}",
                  rule.info.name, raw_substs.len());
    }
    // TAM_DBG_FRESH_TRACE=1: diagnostic trace of the per-rule fresh counter
    // before/after the variant pipeline.  Used to triangulate which step
    // consumes how many idxs when comparing witness idxs against HS.
    // HS-faithful: filter variants via `isFreshRedundant` (RuleVariants.hs:128-134)
    // BEFORE composition. A variant is redundant if it forces a freshly
    // introduced term (from a Fresh-fact premise) to also appear in a
    // non-Fresh premise after substitution.  These variants represent
    // physically impossible bindings — they require a Fresh nonce to
    // appear simultaneously in two unrelated message positions.
    //
    // Without this filter, RS keeps redundant variants that HS drops,
    // causing the variant disj to retain heterogeneous outer ops across
    // substs (identity variant with `convertpcs(...)` vs reducing variant
    // with `sign(...)`). simp_abstract_fun can't lift heterogeneous ops,
    // so same-image pairs never emerge, simp_identify never fires, no
    // multi-key equivalence classes form, enforce_ku_action_uniqueness
    // never merges. This is the root cause of resolved1's 26-line diff.
    let raw_substs: Vec<_> = {
        let freshly_introduced: Vec<LNTerm> = rule.premises.iter()
            .filter(|f| matches!(f.tag, crate::fact::FactTag::Fresh))
            .filter_map(|f| f.terms.first().cloned())
            .collect();
        let premise_terms_for_filter: Vec<LNTerm> = rule.premises.iter()
            .filter(|f| !matches!(f.tag, crate::fact::FactTag::Fresh))
            .flat_map(|f| f.terms.iter().cloned())
            .collect();
        if freshly_introduced.is_empty() || premise_terms_for_filter.is_empty() {
            raw_substs
        } else {
            let mut frees = std::collections::BTreeSet::new();
            for t in &premise_terms_for_filter {
                t.for_each_free(&mut |v| { frees.insert(v.clone()); });
            }
            // HS-faithful: `freshToFreeAvoidingFast sFresh (frees premiseTerms)`
            // (RuleVariants.hs:131; defined Term/Substitution.hs:77) runs `rename` inside `evalFreshAvoiding
            // (frees premiseTerms)` — a LOCAL Fresh scope seeded at
            // `succ (max idx in frees premiseTerms)`.  Witnesses minted by
            // this filter do NOT advance the outer (per-rule) MonadFresh
            // counter (RuleVariants.hs:64 `convertRule \`evalFreshTAvoiding\` ru`)
            // because `evalFreshAvoiding` nests its OWN Fresh state.
            //
            // RS previously used `maude.fresh_idx()` per variant, which
            // advances the per-rule Maude counter by one per filter call.
            // For Handshake_Resp's 133 raw variants, that pushed the per-rule
            // counter from 27 (post-abstrTerm) to 160 BEFORE the simp pipeline
            // even started.  That high counter then propagated into every
            // downstream avoid_max computation: variant subst range vars
            // ended up at idxs ~2255 (RS) instead of ~393 (HS).
            //
            // Mirror HS by seeding LOCALLY from `frees premiseTerms` and
            // advancing only a local `counter`.  Maude's global counter
            // stays untouched by this filter.
            let frees_max: u64 = frees.iter().map(|v| v.idx).max().unwrap_or(0);
            let filter_base: u64 = frees_max.saturating_add(1);
            raw_substs.into_iter().filter(|pairs| {
                let s_fresh = LNSubstVFresh::from_list(pairs.clone());
                let mut counter = filter_base;
                let subst = s_fresh.fresh_to_free_avoiding(
                    |n| { let b = counter; counter += n; b },
                    &frees,
                );
                let premises: Vec<LNTerm> = premise_terms_for_filter.iter()
                    .map(|t| {
                        let applied = apply_vterm(&subst, t.clone());
                        maude.reduce(&applied).unwrap_or(applied)
                    })
                    .collect();
                let fresh_terms: Vec<LNTerm> = freshly_introduced.iter()
                    .map(|t| apply_vterm(&subst, t.clone()))
                    .collect();
                for ft in &fresh_terms {
                    for p in &premises {
                        if contains_subterm(ft, p) {
                            return false;
                        }
                    }
                }
                true
            }).collect()
        }
    };

    let composed_substs: Vec<LNSubstVFresh> = raw_substs.into_iter().map(|pairs| {
        // `pairs` are already removeRenamings'd (applied once up front,
        // mirroring HS's `msubstToLSubstVFresh`, Maude/Types.hs:130).  HS's
        // identity variant therefore arrives EMPTY here, so composeVFresh
        // operates on empty s1_0 and adds renamings for the abstraction
        // subst's range vars (the rule's leaves, all at idx 0 from parser)
        // — its uniform shift collapses them ALL to the SAME fresh idx.
        // THAT's how HS gets `{pkA.5, s.5}` (both at idx 5) for the
        // CHECKSIGN identity variant.
        let vsubst = LNSubstVFresh::from_list(pairs);
        // composeVFresh vsubst abstractionSubst
        let composed = tamarin_term::subst_vfresh::compose_vfresh(
            &vsubst, &abstraction_subst);
        // normSubstVFresh' — normalise each range term via Maude.
        let normalised_pairs: Vec<(LVar, LNTerm)> = composed.to_list()
            .into_iter()
            .map(|(k, t)| {
                let n = maude.reduce(&t).unwrap_or(t);
                (k, n)
            })
            .collect();
        let normalised = LNSubstVFresh::from_list(normalised_pairs);
        // removeRenamings (post-compose, HS RuleVariants.hs:74)
        let cleaned = normalised.remove_renamings();
        // restrictVFresh (frees abstrPsCsAs)
        cleaned.restrict(&abstr_frees)
    })
    // HS-faithful: `variantsProtoRule` (RuleVariants.hs:87-91) builds the
    // composed `substs` list with NO post-composition renaming filter — the
    // only filter is `not $ isFreshRedundant vsubst` on the RAW Maude variant
    // (applied above as the H20 pass).  Each composed entry is
    //   `restrictVFresh (frees abstrPsCsAs) $ removeRenamings $
    //      normSubstVFresh' $ composeVFresh vsubst abstractionSubst`
    // and is kept verbatim.  A previous `.filter(|s| !s.is_renaming())` here
    // (carried over from the pre-`compose_vfresh` manual path) dropped any
    // composed subst that restricted-down to a pure renaming — which is
    // EXACTLY HS's narrowing variant for a rule like foo_eligibility's `C_2`.
    //
    // `C_2`'s `commit(open(x,r),r)` abstracts to `commit(z,r)` with z=open(x,r).
    // Maude returns 2 variants: identity, and the narrowing `x ↦ commit(_,r)`
    // making `open(x,r) → z`.  After compose+removeRenamings+restrict the
    // narrowing variant becomes `{A↦A', r↦x.5, z↦x.6}` — a renaming once the
    // out-of-`abstrPsCsAs` `x ↦ commit(x.6,x.5)` entry is restricted away.  HS
    // KEEPS this renaming subst (its `frees abstrPsCsAs = {A.1,r.2,z.4}` and
    // restrictVFresh produces the same all-renaming subst, fed to
    // `simpDisjunction` unfiltered).  With it present, `simpDisjunction` sees a
    // genuine 2-way disjunction and does NOT fold `z ↦ open(x,r)` into
    // `commonSubst`, so the stored rule keeps the abstracted `commit(z,r)`.
    // Dropping it left RS with a single `{z ↦ open(x,r)}` subst, which
    // `simpSingleton` folded into the rule body, un-abstracting it back to
    // `commit(open(x,r),r)` — RS then renders "trivial AC variant" and the
    // exists-trace `exec` lemma can no longer narrow `open(x,r)` to reach
    // `case V_2` (the trace), so it was wrongly `falsified` (soundness bug).
    .collect();

    if composed_substs.is_empty() {
        return Ok(None);
    }

    // Haskell `simpDisjunction hnd (const (const False)) (Disj substs)`
    // splits into (commonSubst, freshSubsts).  commonSubst is the free
    // substitution part that's common to all variants — applied to the
    // abstracted rule.  freshSubsts is the residual SplitG disjunction.
    //
    // Without this split, action terms like `Verify(m)` get abstracted
    // to `Verify(z)` AND every variant binds `z := m` — so the SplitG
    // is just identity but the rule still carries `Verify(z)`, which
    // matches against ANY Verify(_) action goal causing wrong cases.
    //
    // After splitting, `commonSubst` carries `{z := m}` and the rule's
    // action becomes `Verify(m)` again; the SplitG only carries the
    // RESIDUAL disjuncts that differ between variants.
    // HS-faithful: variantsProtoRule (RuleVariants.hs:82) calls
    // `simpDisjunction hnd ...` with a Maude handle, which routes through
    // `simp1`'s FULL pipeline including `simpSingleton` (EquationStore.hs:391, invoked at 361).
    // That pass folds a single-variant disj into the free subst — so the
    // residual returned to `makeRule` is `Nothing` and the variant subst
    // content gets baked into the rule body via commonSubst.  RS's
    // `simp_disjunction` (no Maude handle) SKIPS simpSingleton; use the
    // `_with_maude` variant here to match HS.  Without it, e.g.
    // JKL_TS1_2004 Init_2 keeps `z.0 → 'g'^lkR; z.1 → 'g'^(lkI*lkR)` in
    // the residual instead of baking them into the rule's `!Sessk(...)`
    // conclusion — diverging Sessk_reveal source-case numbering downstream.
    if std::env::var("TAM_DBG_FRESH_TRACE").is_ok() {
        eprintln!("[fresh-trace] rule={:?} pre-simp_disj counter={} composed_substs={}",
            rule.info.name, maude.fresh_counter_peek(), composed_substs.len());
    }
    let (common_subst, residual) = crate::tools::equation_store::EquationStore::simp_disjunction_with_maude(
        composed_substs, |_, _| false, maude);
    if std::env::var("TAM_DBG_FRESH_TRACE").is_ok() {
        eprintln!("[fresh-trace] rule={:?} post-simp_disj counter={}",
            rule.info.name, maude.fresh_counter_peek());
    }

    // Apply common_subst to the abstracted rule's terms.
    let abstracted_rule = if common_subst.is_empty() {
        abstracted_rule
    } else {
        let map_facts = |fs: Vec<Fact<LNTerm>>| -> Vec<Fact<LNTerm>> {
            fs.into_iter().map(|f| f.map(|t| apply_vterm(&common_subst, t))).collect()
        };
        let prems = map_facts(abstracted_rule.premises);
        let concs = map_facts(abstracted_rule.conclusions);
        let acts = map_facts(abstracted_rule.actions);
        let nvs: Vec<LNTerm> = abstracted_rule.new_vars.into_iter()
            .map(|t| apply_vterm(&common_subst, t))
            .collect();
        crate::rule::Rule::new(rule.info.clone(), prems, concs, acts).with_new_vars(nvs)
    };

    // HS-faithful `variantsProtoRule` disjunction selection
    // (RuleVariants.hs:88-91):
    //   (commonSubst, Nothing)        -> makeRule abstrPsCsAs commonSubst trueDisj
    //   (commonSubst, Just freshSubsts) -> makeRule abstrPsCsAs commonSubst freshSubsts
    // where `trueDisj = [emptySubstVFresh]` (RuleVariants.hs:120).
    //
    // When `simpDisjunction` collapses the variant disjunction to a single
    // case (`residual == Nothing`), HS does NOT drop the variant disjunction
    // — it keeps `[emptySubstVFresh]`, the trivial-but-present SplitG.  That
    // disjunction is later added by `solveRuleConstraints`
    // (Reduction.hs:967-979) via `addRuleVariants` → `addDisj`, which bumps
    // `eqsNextSplitId` by 1 at EVERY `labelNodeId` for such a rule even though
    // `simp`'s `simpSingleton` immediately folds the singleton and
    // `removeSolvedSplitGoals` later deletes the orphaned SplitG (the
    // split-id counter bump persists).  RS previously used `Vec::new()` here,
    // dropping the trivial disjunction entirely → no `add_disj` → its
    // `eqsNextSplitId` ran one BEHIND HS for each rule whose variants collapse
    // to the identity (spdm121 `I_KE_Request`/`I_KE_RequestPK`: Maude returns
    // the single identity variant, `simp` collapses it to `residual=Nothing`).
    // That under-bump shifted every later `splitEqs(N)` render label by -1
    // (spdm121 `Attack_Responder_Requester_Mode_Switch`: HS `splitEqs(4)` vs
    // RS `splitEqs(3)`).
    //
    // Mirror HS exactly: `Nothing -> trueDisj`, `Just fs -> fs` (the
    // pre-simp `removeRenamings`/`isFreshRedundant` already ran on the
    // composed substs at the `composed_substs` build site, matching
    // RuleVariants.hs:87-91; no additional post-simp renaming/range filter,
    // which HS does not have).
    let final_substs: Vec<LNSubstVFresh> = match residual {
        // `simpDisjunction` returning `Just fs` with `fs` non-empty is HS's
        // `(commonSubst, Just freshSubsts)` arm.  A `Just []` cannot arise
        // from a satisfiable disjunction (an unsatisfiable one is carried as
        // `falseEqConstrConj`, not here); treat the degenerate empty case as
        // the collapse (trueDisj) so we never emit an empty SplitG disj.
        Some(rs) if !rs.is_empty() => rs,
        _ => vec![LNSubstVFresh::empty()],
    };

    // HS `variantsProtoRule` returns the abstracted rule whenever the
    // composed-substs list was non-empty (RuleVariants.hs:79-80 only `mzero`s
    // on an EMPTY composed list — handled earlier via `raw_substs.is_empty()`
    // and the composed-substs build).  With `final_substs` now always
    // non-empty (trueDisj at minimum), the abstracted form is always
    // produced, matching HS's `makeRule` for the collapse case.

    // HS-faithful `renamePrecise` wrap (RuleVariants.hs:64):
    //   `(`Precise.evalFresh` Precise.nothingUsed) . renamePrecise $ ...`
    //
    // Re-numbers all rule + variant subst LVars using PreciseFresh
    // (per-name counter starting from 0).  Without this, the rule's
    // vars keep the unique idxs assigned by abstrRule (via Maude's
    // global counter), which causes downstream `freshen_rule`'s
    // uniform shift to keep them at DIFFERENT idxs — but HS's
    // renamePrecise collapses ALL rule vars to PER-NAME idxs
    // (typically 0 since each name is unique in the rule).
    //
    // This makes BTreeMap key ordering in apply_eq_store match HS's
    // — all rule keys at idx 0 → sorted by name first → CHECKSIGN
    // variant sort order matches HS for test4/test5.
    //
    if std::env::var("TAM_DBG_VARIANT_OUT").is_ok() {
        eprintln!("[variant-out-pre] rule={:?} #final_substs={}", rule.info.name, final_substs.len());
        for (i, s) in final_substs.iter().enumerate() {
            let keys: Vec<String> = s.dom().map(|v| format!("{}.{}/{:?}", v.name, v.idx, v.sort)).collect();
            eprintln!("[variant-out-pre]   [{}] keys=[{}]", i, keys.join(","));
        }
    }
    let (abstracted_rule, final_substs) =
        rename_precise_rule_with_variants(abstracted_rule, final_substs);

    if std::env::var("TAM_DBG_VARIANT_OUT").is_ok() {
        eprintln!("[variant-out] rule={:?} #final_substs={}", rule.info.name, final_substs.len());
        for (i, s) in final_substs.iter().enumerate() {
            let keys: Vec<String> = s.dom().map(|v| format!("{}.{}/{:?}", v.name, v.idx, v.sort)).collect();
            eprintln!("[variant-out]   [{}] keys=[{}]", i, keys.join(","));
        }
    }

    Ok(Some((abstracted_rule, final_substs)))
}

/// Apply HS-style `renamePrecise` to a rule + its variant disjunction
/// substs.  Mirrors HS `Precise.evalFresh (renamePrecise x) Precise.nothingUsed`
/// applied to a `Rule ProtoRuleACInfo` (variants live INSIDE info).
///
/// HS traversal order (Rule.hs:279-292 `HasFrees (Rule i)`; Rule.hs:485-495
/// `HasFrees ProtoRuleACInfo`; SubstVFresh.hs:196-202 `HasFrees SubstVFresh`):
///
///   mapFrees (Rule i ps cs as nvs) =
///     Rule <$> mapFrees i  -- variants Disj walked here (KEYS-ONLY)
///          <*> mapFrees ps
///          <*> mapFrees cs
///          <*> mapFrees as
///          <*> mapFrees nvs
///
/// Crucially:
///   - HS's `HasFrees (SubstVFresh n LVar)` walks ONLY the domain (keys),
///     never the range (`foldFrees f = foldFrees f . M.keys . svMap`).
///   - HS's `mapFrees` for `SubstVFresh` likewise only RENAMES keys; the
///     range terms are passed through unchanged (`mapDomain (v, t) = (,t) <$>
///     mapFrees f v`).
///
/// Past RS bug: walking + renaming subst RANGE introduced extra names into
/// PreciseFreshState (contaminating per-name counters) and rewrote range
/// vars HS leaves alone — diverging the abstrTerm-vs-original variable
/// idxs that downstream `someRuleACInst`'s uniform shift produces, then
/// flipping AC-sorted variant-subst order, then rotating
/// performSplit-case numbering. Symptom on JKL_TS1_2004:
/// `Sessk_reveal_case_3` (RS) vs `Sessk_reveal_case_4` (HS).
/// Would HS's `renamePrecise` (per-name fresh indices, RuleVariants.hs:64)
/// rewrite any of this rule's free vars?  True iff some var's renamePrecise
/// index differs from its original — the realistic trigger being two free
/// vars sharing a name (e.g. `~ltk` and `ltk` → the second becomes `ltk.1`).
/// Walks vars in the SAME order as `rename_precise_rule_with_variants` (the
/// variant disjunction has no keys for the trivial-disjunction case, so it
/// reduces to prems, concs, acts, new_vars).
fn rule_renames_under_precise(rule: &ProtoRuleE) -> bool {
    use tamarin_term::lterm::HasFrees;
    use tamarin_utils::fresh::PreciseFreshState;
    use std::collections::HashMap;
    let mut vars: Vec<LVar> = Vec::new();
    {
        let mut collect = |v: &LVar| vars.push(v.clone());
        for f in &rule.premises { for t in &f.terms { t.for_each_free(&mut collect); } }
        for f in &rule.conclusions { for t in &f.terms { t.for_each_free(&mut collect); } }
        for f in &rule.actions { for t in &f.terms { t.for_each_free(&mut collect); } }
        for t in &rule.new_vars { t.for_each_free(&mut collect); }
    }
    let mut state = PreciseFreshState::nothing_used();
    let mut map: HashMap<LVar, LVar> = HashMap::new();
    for v in &vars {
        if map.contains_key(v) { continue; }
        let idx = state.fresh_ident(&v.name);
        if idx != v.idx { return true; }
        map.insert(v.clone(), LVar { name: v.name.clone(), sort: v.sort, idx });
    }
    false
}

fn rename_precise_rule_with_variants(
    rule: ProtoRuleE,
    substs: Vec<LNSubstVFresh>,
) -> (ProtoRuleE, Vec<LNSubstVFresh>) {
    use tamarin_term::lterm::HasFrees;
    use tamarin_utils::fresh::PreciseFreshState;
    use std::collections::HashMap;

    let mut state = PreciseFreshState::nothing_used();
    let mut map: HashMap<LVar, LVar> = HashMap::new();
    let import = |v: &LVar, st: &mut PreciseFreshState, m: &mut HashMap<LVar, LVar>| {
        if m.contains_key(v) { return; }
        let idx = st.fresh_ident(&v.name);
        let new_v = LVar { name: v.name.clone(), sort: v.sort, idx };
        m.insert(v.clone(), new_v);
    };

    // Phase 1: walk every free LVar in HS's `mapFrees (Rule ProtoRuleACInfo)`
    // order. ProtoRuleACInfo (Rule.hs:485-495) walks name|attr|variants|breakers;
    // name/attr/breakers are empty (RuleAttributes.hs:446-449, etc.), so
    // effectively variants Disj first (KEYS-ONLY per SubstVFresh.hs:196-202).
    // THEN prems, concs, acts, new_vars (Rule.hs:279-292).
    for s in &substs {
        for (k, _t) in s.to_list() {
            import(&k, &mut state, &mut map);
            // Range NOT walked: HS `HasFrees (SubstVFresh n LVar)` is
            // keys-only.  Walking the range here introduces extra names
            // and shifts per-name counters away from HS.
        }
    }
    for f in &rule.premises {
        for t in &f.terms { t.for_each_free(&mut |v| import(v, &mut state, &mut map)); }
    }
    for f in &rule.conclusions {
        for t in &f.terms { t.for_each_free(&mut |v| import(v, &mut state, &mut map)); }
    }
    for f in &rule.actions {
        for t in &f.terms { t.for_each_free(&mut |v| import(v, &mut state, &mut map)); }
    }
    for t in &rule.new_vars {
        t.for_each_free(&mut |v| import(v, &mut state, &mut map));
    }

    if map.is_empty() {
        return (rule, substs);
    }

    // Phase 2: apply the renaming map.
    let map_var = |v: &LVar| -> LVar {
        map.get(v).cloned().unwrap_or_else(|| v.clone())
    };
    let map_term = |t: LNTerm| -> LNTerm {
        t.map_free(&mut |v| map_var(&v))
    };

    let new_premises: Vec<Fact<LNTerm>> = rule.premises.into_iter().map(|f| {
        Fact {
            tag: f.tag,
            annotations: f.annotations,
            terms: f.terms.into_iter().map(map_term).collect(),
        }
    }).collect();
    let new_conclusions: Vec<Fact<LNTerm>> = rule.conclusions.into_iter().map(|f| {
        Fact {
            tag: f.tag,
            annotations: f.annotations,
            terms: f.terms.into_iter().map(map_term).collect(),
        }
    }).collect();
    let new_actions: Vec<Fact<LNTerm>> = rule.actions.into_iter().map(|f| {
        Fact {
            tag: f.tag,
            annotations: f.annotations,
            terms: f.terms.into_iter().map(map_term).collect(),
        }
    }).collect();
    let new_nvs: Vec<LNTerm> = rule.new_vars.into_iter().map(map_term).collect();
    let new_rule = crate::rule::Rule::new(
        rule.info,
        new_premises,
        new_conclusions,
        new_actions,
    ).with_new_vars(new_nvs);

    // HS-faithful: SubstVFresh.hs:199-202 — `mapFrees` only renames the
    // DOMAIN, leaving the range terms identical (`(,t) <$> mapFrees f v`).
    let new_substs: Vec<LNSubstVFresh> = substs.into_iter().map(|s| {
        let pairs: Vec<(LVar, LNTerm)> = s.to_list().into_iter().map(|(k, t)| {
            (map_var(&k), t)
        }).collect();
        LNSubstVFresh::from_list(pairs)
    }).collect();

    (new_rule, new_substs)
}

pub fn expand_rule_variants(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
    reducible: &std::collections::BTreeSet<tamarin_term::function_symbols::FunSym>,
) -> Result<Vec<ProtoRuleAC>, VariantsError> {
    let ac = match variants_proto_rule(maude, rule)? {
        Some(ac) => ac,
        None => return Ok(Vec::new()),
    };
    let substs = &ac.info.variants;
    // Drop pure-renaming variants — Maude's identity variant comes
    // back as `x0 → ~mw1:Msg, x1 → ~mw2:Msg` etc., which carries no
    // information beyond α-renaming and is already covered by the
    // raw rule the solver instantiates. Keep only variants with at
    // least one App in their range (i.e. actually-narrowing).
    let useful: Vec<&LNSubstVFresh> = substs.iter()
        .filter(|s| s.range().any(|t| matches!(t, Term::App(_, _))))
        .collect();
    if useful.is_empty() {
        return Ok(Vec::new());
    }
    // After applying a variant substitution we must renormalise via
    // Maude so destructor terms reduce to their narrowed form: e.g.
    // `Out(snd(sdec(senc(pair(a,b), k), k)))` must reduce to `Out(b)`.
    // Without this, the rule conclusion stays as the literal pre-
    // reduction shape and won't unify with destructor-free goals.
    let normalize = |t: LNTerm| -> LNTerm {
        match maude.reduce(&t) { Ok(n) => n, Err(_) => t }
    };
    let mut out: Vec<ProtoRuleAC> = Vec::with_capacity(useful.len() + 1);
    // Include the raw (un-narrowed) rule alongside the narrowed
    // variants — Haskell's Disj-of-variants does include the
    // identity, and the chain-fold enumeration needs the un-narrowed
    // form for non-destructor-driven goals.
    {
        let info = ProtoRuleACInfo {
            name: rule.info.name.clone(),
            attributes: rule.info.attributes.clone(),
            variants: vec![LNSubstVFresh::empty()],
            loop_breakers: Vec::new(),
        };
        out.push(crate::rule::Rule {
            info,
            premises: rule.premises.clone(),
            conclusions: rule.conclusions.clone(),
            actions: rule.actions.clone(),
            new_vars: rule.new_vars.clone(),
        });
    }
    fn has_reducible(
        t: &LNTerm,
        rs: &std::collections::BTreeSet<tamarin_term::function_symbols::FunSym>,
    ) -> bool {
        match t {
            Term::Lit(_) => false,
            Term::App(f, args) =>
                rs.contains(f) || args.iter().any(|a| has_reducible(a, rs)),
        }
    }
    for vsubst in useful {
        let lnsubst: LNSubst = LNSubst::from_list(vsubst.to_list());
        let premises: Vec<Fact<LNTerm>> = rule.premises.iter()
            .map(|f| f.clone().map(|t| normalize(apply_vterm(&lnsubst, t))))
            .collect();
        let actions: Vec<Fact<LNTerm>> = rule.actions.iter()
            .map(|f| f.clone().map(|t| normalize(apply_vterm(&lnsubst, t))))
            .collect();
        let conclusions: Vec<Fact<LNTerm>> = rule.conclusions.iter()
            .map(|f| f.clone().map(|t| normalize(apply_vterm(&lnsubst, t))))
            .collect();
        let new_vars: Vec<LNTerm> = rule.new_vars.iter()
            .map(|t| normalize(apply_vterm(&lnsubst, t.clone())))
            .collect();
        // Skip partial-narrowing variants: if any conclusion term still
        // contains a reducible function symbol after normalisation, the
        // variant didn't fully narrow through. The raw rule already
        // covers this case shape, so emitting the intermediate just
        // bloats search.
        let has_destr_in_concs = conclusions.iter()
            .any(|f| f.terms.iter().any(|t| has_reducible(t, reducible)));
        if has_destr_in_concs { continue; }
        // Each per-variant ProtoRuleAC carries the identity inside —
        // the variant subst is already applied to the terms above.
        let info = ProtoRuleACInfo {
            name: rule.info.name.clone(),
            attributes: rule.info.attributes.clone(),
            variants: vec![LNSubstVFresh::empty()],
            loop_breakers: Vec::new(),
        };
        out.push(crate::rule::Rule {
            info,
            premises,
            conclusions,
            actions,
            new_vars,
        });
    }
    Ok(out)
}

/// `findPos`-style subterm check: returns true if `needle` appears
/// anywhere within `haystack` (including as the whole term).  Mirrors
/// HS's `isJust . findPos` used in `isFreshRedundant`.
fn contains_subterm(needle: &LNTerm, haystack: &LNTerm) -> bool {
    use tamarin_term::term::Term;
    if needle == haystack { return true; }
    if let Term::App(_, args) = haystack {
        for a in args.iter() { if contains_subterm(needle, a) { return true; } }
    }
    false
}

/// WF-only check: mirrors HS `variantsCheck` (Wellformedness.hs:354-372)
/// sub-check `guard (null recomputedVariants)`.  Returns `true` iff
/// `variantsProtoRule hnd rule` would return `Nothing` — i.e. the rule
/// has no non-fresh-redundant variants.
///
/// HS faithfulness: `recomputedVariants` is empty iff
/// `variantsProtoRule` returns `Nothing`, which happens when
/// `convertRule`'s `substs` list (RuleVariants.hs:87-91) is empty after
/// `isFreshRedundant` filtering.
///
/// Two paths lead to empty `substs`:
///
/// 1. **Contradiction (no-reducible) path**: the rule has no reducible-
///    headed sub-terms.  Maude returns only identity/renaming variants,
///    which become `{}` after `removeRenamings`.  `isFreshRedundant {}`
///    fires iff any freshly-introduced term `~v` (from `Fr(~v)`) appears
///    as a sub-term of any non-Fr premise term.  For the canonical case
///    `Fr(~x), In(~x)`: `~x` IS in both `freshlyIntroduced` and
///    `premiseTerms` → all variants redundant → `Nothing`.
///
/// 2. **Reducible path**: the rule has reducible-headed terms.  Maude
///    may return non-renaming variants, but after composition and the
///    full `isFreshRedundant` pipeline all may still be filtered.  This
///    is handled by `abstract_rule_and_variants` returning `Ok(None)`.
///
/// `maude` is only needed for path 2; for path 1 the check is purely
/// syntactic.  The function requires a `MaudeHandle` for completeness.
pub fn rule_has_no_variants_for_wf(
    maude: &MaudeHandle,
    rule: &ProtoRuleE,
) -> bool {
    // Path 1: syntactic fresh-redundancy check (no Maude call needed).
    //
    // If the rule has NO reducible-headed sub-terms, the only Maude
    // variant is identity/renaming → collapses to `{}` after
    // `removeRenamings`.  `isFreshRedundant {}` = True iff any
    // Fr-introduced term also appears in a non-Fr premise.
    let has_reducible = {
        fn term_has_red(t: &LNTerm, irred: &std::collections::BTreeSet<tamarin_term::function_symbols::FunSym>) -> bool {
            use tamarin_term::term::Term;
            if let Term::App(f, args) = t {
                if !irred.contains(f) { return true; }
                args.iter().any(|a| term_has_red(a, irred))
            } else {
                false
            }
        }
        let irred = &maude.maude_sig().irreducible_fun_syms;
        rule.premises.iter().chain(rule.actions.iter()).chain(rule.conclusions.iter())
            .any(|f| f.terms.iter().any(|t| term_has_red(t, irred)))
            || rule.new_vars.iter().any(|t| term_has_red(t, irred))
    };

    if !has_reducible {
        // Syntactic `isFreshRedundant {}` check.
        let freshly_introduced: Vec<&LNTerm> = rule.premises.iter()
            .filter(|f| matches!(f.tag, crate::fact::FactTag::Fresh))
            .filter_map(|f| f.terms.first())
            .collect();
        let premise_terms: Vec<&LNTerm> = rule.premises.iter()
            .filter(|f| !matches!(f.tag, crate::fact::FactTag::Fresh))
            .flat_map(|f| f.terms.iter())
            .collect();
        if freshly_introduced.is_empty() || premise_terms.is_empty() {
            // No Fr facts or no non-Fr premise terms → identity variant
            // survives → rule HAS a variant.
            return false;
        }
        // isFreshRedundant {} = True iff any fresh term appears in a
        // non-Fr premise (i.e. all identity variants are redundant).
        return freshly_introduced.iter().any(|ft| {
            premise_terms.iter().any(|p| contains_subterm(ft, p))
        });
    }

    // Path 2: reducible rule — use `abstract_rule_and_variants`.
    // Returns `Ok(None)` when all composed substs are filtered out.
    matches!(abstract_rule_and_variants(maude, rule), Ok(None))
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::maude_sig::pair_maude_sig;
    use tamarin_term::vterm::Lit;

    use crate::fact::{Fact, FactTag};
    use crate::rule::{ProtoRuleEInfo, ProtoRuleName, RuleAttributes, Rule};

    fn maude_path() -> Option<String> {
        if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
        let candidates = [
            "/home/linuxbrew/.linuxbrew/bin/maude",
            "/usr/local/bin/maude",
            "/usr/bin/maude",
            "maude",
        ];
        for c in &candidates {
            if std::path::Path::new(c).exists() { return Some((*c).to_string()); }
        }
        None
    }

    fn empty_rule(name: &str) -> ProtoRuleE {
        let info = ProtoRuleEInfo {
            name: ProtoRuleName::Stand(name.to_string()),
            attributes: RuleAttributes::empty(),
            restrictions: Vec::new(),
        };
        Rule::new(info, Vec::new(), Vec::new(), Vec::new())
    }

    #[test]
    fn variants_of_rule_with_no_terms_is_identity() {
        let path = match maude_path() {
            Some(p) => p,
            None => { eprintln!("skipping: no maude"); return; }
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        let rule = empty_rule("R");
        let ac = variants_proto_rule(&h, &rule).expect("variants").unwrap();
        // No terms → identity variant.
        assert_eq!(ac.info.variants.len(), 1);
        assert!(ac.info.variants[0].is_empty());
    }

    #[test]
    fn variants_of_simple_rule_via_maude() {
        let path = match maude_path() {
            Some(p) => p,
            None => { eprintln!("skipping: no maude"); return; }
        };
        let h = MaudeHandle::start(&path, pair_maude_sig()).unwrap();
        // Rule: [Fr(~k)] --> [Out(~k)]
        let k = LVar::new("k", LSort::Fresh, 0);
        let kt: LNTerm = Term::Lit(Lit::Var(k));
        let prem = Fact::new(FactTag::Fresh, vec![kt.clone()]);
        let conc = Fact::new(FactTag::Out, vec![kt.clone()]);
        let info = ProtoRuleEInfo {
            name: ProtoRuleName::Stand("R".into()),
            attributes: RuleAttributes::empty(),
            restrictions: Vec::new(),
        };
        let rule = Rule::new(info, vec![prem], vec![conc], Vec::new());
        let ac = variants_proto_rule(&h, &rule).expect("variants").unwrap();
        // For a rule with no reducible operators, Maude returns one
        // trivial variant (the identity).
        assert!(!ac.info.variants.is_empty(),
            "expected at least one variant, got none");
    }
}
