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
//! For the first cut we implement steps 2-5 directly on the
//! rule's free variables (no abstraction). That's adequate for rules
//! whose terms are already in a form Maude can variant-narrow; it
//! covers most parsed rules. The full `abstrTerm` machinery follows
//! once we've ported `Term.Narrowing.Variants`.

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
    NoVariants,
}

impl std::fmt::Display for VariantsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VariantsError::Maude(s) => write!(f, "Maude error: {}", s),
            VariantsError::NoVariants => write!(f, "no variants returned by Maude"),
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
    let packed = pack_rule_terms(rule);
    if packed.is_none() {
        // No reducible terms → no variants beyond the identity.
        return Ok(Some(make_proto_rule_ac(rule, &LNSubst::default(), vec![LNSubstVFresh::empty()])));
    }
    let packed = packed.unwrap();
    let raw = maude.variants(&packed)?;
    if raw.is_empty() {
        return Ok(None);
    }
    let substs: Vec<LNSubstVFresh> = raw.into_iter()
        .map(|pairs| LNSubstVFresh::from_list(pairs.into_iter()))
        .collect();
    // HS-faithful `simpDisjunction hnd (const (const False)) (Disj substs)`
    // (RuleVariants.hs:82).  Routes through `simp1`'s full pipeline
    // including `simpSingleton` (EquationStore.hs:596) — that pass
    // folds a singleton-variant disj into the free subst, which is
    // what HS's `commonSubst` carries.  Without this, the SplitG
    // residual retains entries that HS bakes into the rule body via
    // `makeRule`'s `apply commonSubst` (RuleVariants.hs:114-117) —
    // which is the root of the NAXOS_eCK_private Init_1-vs-Ltk_reveal
    // divergence.
    //
    // Previously this call was deliberately skipped because RS's
    // simp_disjunction (no Maude handle) collapsed identity-containing
    // disjunctions to Nothing.  Since f7321d2e added
    // `simp_disjunction_with_maude` (which uses `simp_with_fresh_avoiding`
    // → `simp_singleton` → only folds genuine singletons), the
    // simplification is now safe to run.
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
    else { Some(Term::App(FunSym::List, all)) }
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

/// Compute the rule variants for `rule` and return one `ProtoRuleAC`
/// per Maude-returned variant, each with the variant's substitution
/// already applied to the rule's terms. Returns the empty vector when
/// Maude reports a single identity variant (caller can use the raw
/// rule).
///
/// Mirrors the result-shape of Haskell's `variantsProtoRule` plumbed
/// into the solver: `OpenProtoRule.variants` is a `Vec<ProtoRuleAC>`
/// where each entry has the variant's narrowing already baked in.
/// Destructor-narrowed conclusions (e.g. `Out(snd(sdec(msg, key)))`
/// reduced via `msg → senc(pair(_, t), key)` to `Out(t)`) become
/// enumerable by chain-fold without any extra Maude calls at search
/// time.
///
/// Only emits variants whose conclusion terms contain **no** reducible
/// function symbols — the partial-narrowing intermediates (e.g.
/// `Out(snd(senc-something))`) carry redundant destructor heads that
/// can't unify with a destructor-free goal and just bloat the search
/// case tree. The fully-narrowed forms are the ones chain-fold
/// actually needs.
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
    maude.ensure_above(avoid_max);

    fn sort_of_term(t: &LNTerm) -> tamarin_term::lterm::LSort {
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Var(v)) => v.sort,
            Term::Lit(Lit::Con(_)) => tamarin_term::lterm::LSort::Pub,
            Term::App(_, _) => tamarin_term::lterm::LSort::Msg,
        }
    }

    fn name_hint(t: &LNTerm) -> String {
        use tamarin_term::vterm::Lit;
        match t {
            Term::Lit(Lit::Var(v)) => v.name.clone(),
            _ => "z".to_string(),
        }
    }

    // Memoization: original term → fresh LVar.  HS: `BindT` state
    // (RuleVariants.hs:93) ensures each unique LNTerm gets ONE binding,
    // reused on subsequent encounters.
    let mut bindings: Vec<(LNTerm, LVar)> = Vec::new();

    // HS-faithful `abstrTerm` (RuleVariants.hs:103-109).
    fn abstr_term(
        t: &LNTerm,
        irreducible: &std::collections::BTreeSet<FunSym>,
        bindings: &mut Vec<(LNTerm, LVar)>,
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
        if let Some((_, v)) = bindings.iter().find(|(k, _)| k == t) {
            return Term::Lit(tamarin_term::vterm::Lit::Var(v.clone()));
        }
        let new_idx = maude.reserve_idxs(1);
        let v = LVar {
            name: name_hint(t),
            sort: sort_of_term(t),
            idx: new_idx,
        };
        bindings.push((t.clone(), v.clone()));
        Term::Lit(tamarin_term::vterm::Lit::Var(v))
    }

    fn abstr_fact(
        f: &Fact<LNTerm>,
        irreducible: &std::collections::BTreeSet<FunSym>,
        bindings: &mut Vec<(LNTerm, LVar)>,
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
    // `TAM_RS_DISABLE_LEAF_RENAME=1` opts out for diagnosis.
    let leaf_rename = std::env::var("TAM_RS_DISABLE_LEAF_RENAME").is_err();
    if leaf_rename {
        let mut leaf_vars: Vec<LVar> = Vec::new();
        let mut seen: std::collections::BTreeSet<LVar> = std::collections::BTreeSet::new();
        // HS uses `frees` over a Map — deduplicated.  Order is the Map's
        // traversal order (alphabetical by name/sort/idx via Ord).
        let mut visit = |v: &LVar| {
            if seen.insert(v.clone()) {
                leaf_vars.push(v.clone());
            }
        };
        for f in &rule.premises { f.terms.iter().for_each(|t| t.for_each_free(&mut visit)); }
        for f in &rule.actions { f.terms.iter().for_each(|t| t.for_each_free(&mut visit)); }
        for f in &rule.conclusions { f.terms.iter().for_each(|t| t.for_each_free(&mut visit)); }
        for t in &rule.new_vars { t.for_each_free(&mut visit); }
        for v in leaf_vars {
            let leaf_term: LNTerm = Term::Lit(tamarin_term::vterm::Lit::Var(v));
            // The result is discarded; the side effect on `bindings` is
            // what matters.
            let _ = abstr_term(&leaf_term, &irreducible, &mut bindings, maude);
        }
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
    let abstraction_pairs: Vec<(LVar, LNTerm)> = bindings.iter()
        .map(|(t, v)| (v.clone(), t.clone()))
        .collect();
    let abstraction_subst: LNSubst = Subst::from_list(abstraction_pairs.clone());

    // `abstractedTerms = map snd eqsAbstr` — the ORIGINAL terms.
    let abstracted_terms: Vec<LNTerm> = bindings.iter().map(|(t, _)| t.clone()).collect();
    let packed = Term::App(FunSym::List, abstracted_terms);
    let raw_substs = match maude.variants(&packed) {
        Ok(v) => v,
        Err(e) => return Err(e.into()),
    };
    if raw_substs.is_empty() {
        return Ok(None);
    }

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

    // `TAM_RS_DISABLE_HS_COMPOSE_PIPELINE=1` reverts to the old manual
    // composition path for diagnosis.
    let use_hs_compose = std::env::var("TAM_RS_DISABLE_HS_COMPOSE_PIPELINE").is_err();

    if std::env::var("TAM_DBG_HS_COMPOSE").is_ok() {
        eprintln!("[hs-compose] rule={:?} leaf_rename={} use_hs_compose={} #variants={}",
                  rule.info.name, leaf_rename, use_hs_compose, raw_substs.len());
    }
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
    let h20_enabled = std::env::var("TAM_RS_DISABLE_H20").is_err();
    let raw_substs: Vec<_> = if h20_enabled {
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
            raw_substs.into_iter().filter(|pairs| {
                let s_fresh = LNSubstVFresh::from_list(pairs.clone());
                let mut counter = maude.fresh_idx();
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
    } else {
        raw_substs
    };

    let composed_substs: Vec<LNSubstVFresh> = raw_substs.into_iter().map(|pairs| {
        if use_hs_compose {
            // HS-faithful path.
            // HS's `msubstToLSubstVFresh` (Maude/Types.hs:130) returns
            // `removeRenamings $ substFromListVFresh slist` — i.e. raw
            // Maude variants have their pure-rename entries (e.g.
            // identity-variant `{s → s_w, pkA → pkA_w}` where each
            // witness doesn't appear elsewhere) removed FIRST.
            //
            // Without this, Rust's identity variant keeps `{s.0 → s.1,
            // pkA.0 → pkA.2, A.0 → A.3}` (DIFFERENT witness idxs from
            // Maude's sequential allocation), then composeVFresh's
            // uniform shift preserves the gap → witnesses end at
            // DIFFERENT idxs.
            //
            // HS's identity variant becomes EMPTY here, so composeVFresh
            // operates on empty s1_0 and adds renamings for the
            // abstraction subst's range vars (the rule's leaves, all at
            // idx 0 from parser) — uniform shift collapses them ALL to
            // the SAME fresh idx.  THAT's how HS gets `{pkA.5, s.5}`
            // (both at idx 5) for the CHECKSIGN identity variant.
            //
            // `TAM_RS_DISABLE_VARIANT_REMOVE_RENAMINGS=1` opts out.
            let raw_vsubst = LNSubstVFresh::from_list(pairs);
            let use_remove_renamings = std::env::var("TAM_RS_DISABLE_VARIANT_REMOVE_RENAMINGS").is_err();
            let vsubst = if use_remove_renamings {
                raw_vsubst.remove_renamings()
            } else {
                raw_vsubst.clone()
            };
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
        } else {
            // Old (pre-pipeline) manual composition path.
            let sigma: LNSubst = Subst::from_list(pairs.into_iter().collect::<Vec<_>>());
            let mut composed_pairs: Vec<(LVar, LNTerm)> = abstraction_pairs.iter()
                .map(|(z, t)| {
                    let new_t = apply_vterm(&sigma, t.clone());
                    let normalised = maude.reduce(&new_t).unwrap_or(new_t);
                    (z.clone(), normalised)
                })
                .collect();
            let z_domain: std::collections::BTreeSet<LVar> = abstraction_pairs.iter()
                .map(|(z, _)| z.clone()).collect();
            let abstr_frees_set: std::collections::BTreeSet<LVar> =
                abstr_frees.iter().cloned().collect();
            for (v, t) in sigma.to_list().iter() {
                if z_domain.contains(v) { continue; }
                if !abstr_frees_set.contains(v) { continue; }
                let normalised = maude.reduce(t).unwrap_or_else(|_| t.clone());
                composed_pairs.push((v.clone(), normalised));
            }
            LNSubstVFresh::from_list(composed_pairs)
        }
    })
    .filter(|s| !s.is_renaming())
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
    // HS-faithful: variantsProtoRule (RuleVariants.hs:106) calls
    // `simpDisjunction hnd ...` with a Maude handle, which routes through
    // `simp1`'s FULL pipeline including `simpSingleton` (EquationStore.hs:596).
    // That pass folds a single-variant disj into the free subst — so the
    // residual returned to `makeRule` is `Nothing` and the variant subst
    // content gets baked into the rule body via commonSubst.  RS's
    // `simp_disjunction` (no Maude handle) SKIPS simpSingleton; use the
    // `_with_maude` variant here to match HS.  Without it, e.g.
    // JKL_TS1_2004 Init_2 keeps `z.0 → 'g'^lkR; z.1 → 'g'^(lkI*lkR)` in
    // the residual instead of baking them into the rule's `!Sessk(...)`
    // conclusion — diverging Sessk_reveal source-case numbering downstream.
    let (common_subst, residual) = crate::tools::equation_store::EquationStore::simp_disjunction_with_maude(
        composed_substs, |_, _| false, maude);

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

    // Filter out trivial-true disjuncts and degenerate cases.
    let final_substs: Vec<LNSubstVFresh> = match residual {
        Some(rs) => rs.into_iter()
            .filter(|s| !s.is_renaming())
            .filter(|s| s.range().any(|t| matches!(t, Term::App(_, _))) ||
                        !s.is_empty())
            .collect(),
        None => Vec::new(),
    };

    // Even if there are no useful residual substs, the common_subst
    // application changed the rule — we still need to return the
    // abstracted rule shape so the canonical-rule path picks it up.
    // But if common_subst was empty AND no residual, there's nothing
    // to gain from abstraction.
    if common_subst.is_empty() && final_substs.is_empty() {
        return Ok(None);
    }

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
    // `TAM_RS_DISABLE_VARIANT_RENAME_PRECISE=1` opts out for diagnosis.
    let use_rename_precise = std::env::var("TAM_RS_DISABLE_VARIANT_RENAME_PRECISE").is_err();
    let (abstracted_rule, final_substs) = if use_rename_precise {
        rename_precise_rule_with_variants(abstracted_rule, final_substs)
    } else {
        (abstracted_rule, final_substs)
    };

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

/// `findPos`-style subterm check: returns true if `needle` appears
/// anywhere within `haystack` (including as the whole term).  Mirrors
/// HS's `isJust . findPos` used in `isFreshRedundant`.
fn contains_subterm(needle: &LNTerm, haystack: &LNTerm) -> bool {
    use tamarin_term::term::Term;
    if needle == haystack { return true; }
    if let Term::App(_, args) = haystack {
        for a in args { if contains_subterm(needle, a) { return true; } }
    }
    false
}
