//! Port of `Theory.Constraint.Solver.Contradictions`.
//!
//! Identifies all reasons a `System` is contradictory. The full
//! Haskell version probes ~12 conditions. Most are pure structural
//! checks (cycles, false formulas, fact incompatibilities); a few
//! consult signature-aware helpers (`nf_via_haskell`,
//! `irreducible_fun_syms`, `enableDH`).  ForbiddenBP remains
//! unported (small corpus impact); everything else has a faithful
//! port below.

use std::collections::{BTreeMap, BTreeSet};

use crate::constraint::constraints::{LessAtom, NodeId};
use crate::constraint::solver::context::ProofContext;
use crate::constraint::system::System;

/// Reasons why a `System` is contradictory. Variants match Haskell
/// 1-to-1 so downstream pretty printers can reuse the names.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Contradiction {
    /// The `<` order has a cycle.
    Cyclic,
    /// The subterm constraints form a cycle.
    SubtermCyclic,
    /// Has terms that aren't in normal form modulo theory.
    NonNormalTerms,
    /// Forbidden Exp-down rule instance.
    ForbiddenExp,
    /// Forbidden bilinear pairing rule instance.
    ForbiddenBP,
    /// Has a forbidden KD-fact.
    ForbiddenKD,
    /// Has an impossible chain.
    ImpossibleChain,
    /// Has a forbidden chain.
    ForbiddenChain,
    /// Conflicting injective-fact instances.
    NonInjectiveFactInstance(NodeId, NodeId, NodeId),
    /// Equation store became false.
    IncompatibleEqs,
    /// `false` appeared in the formula store.
    FormulasFalse,
    /// A term is derived both before and after a learn step.
    SuperfluousLearn(tamarin_term::lterm::LNTerm, NodeId),
    /// There is a node strictly after `last(...)`.
    NodeAfterLast(NodeId, NodeId),
}

/// Collect every contradiction currently witnessed by the system.
pub fn contradictions(_ctxt: &ProofContext, sys: &System) -> Vec<Contradiction> {
    let mut out = Vec::new();
    let has_i_1 = sys.nodes.iter().any(|(_, r)|
        matches!(&r.info, crate::rule::RuleInfo::Proto(p)
            if matches!(&p.name, crate::rule::ProtoRuleName::Stand(s) if s == "I_1")));
    let has_r_1 = sys.nodes.iter().any(|(_, r)|
        matches!(&r.info, crate::rule::RuleInfo::Proto(p)
            if matches!(&p.name, crate::rule::ProtoRuleName::Stand(s) if s == "R_1")));
    if std::env::var("TAM_DBG_IMPL").is_ok() && has_i_1 && has_r_1 {
        let has_bot = sys.formulas.iter()
            .any(|f| matches!(f, crate::guarded::Guarded::Disj(v) if v.is_empty()));
        eprintln!("[contra] HAS I_1+R_1: formulas.len={} has_bot={}",
            sys.formulas.len(), has_bot);
    }
    // Mirror Haskell's `rawLessRel = sLessAtoms ++ rawEdgeRel` —
    // every graph edge induces a strict ordering src < tgt, and the
    // cyclic check has to fold both relations together.
    //
    // **Apply eq_store subst before cycle detection**.  Haskell's
    // `cyclic` is called via `runReduction` which invariantly threads
    // the eq-store's substitution through every node-id lookup; their
    // `nodeConcNode` / `nodePremNode` resolve through `eqsSubst`
    // implicitly.  Our `subst_system` propagates eq-store bindings to
    // sys.edges / sys.less_atoms, but it isn't always called between
    // every reduction step (e.g. between `solve_fact_eqs` and the next
    // `contradictions(...)` call from `is_finished`).  When the
    // eq-store binds `vr.X → ~mw.Y` but the system's edges still
    // reference `vr.X`, the cyclic graph carries DOUBLE node identity
    // for the same logical node — two distinct entries that should
    // collapse, sometimes producing a spurious back-edge.
    //
    // Apply the eq-store's substitution to less.smaller / less.larger
    // before walking, so the cyclic graph reflects the canonical
    // node identity. Pure node-id lookups (LVar variable terms) — no
    // term traversal needed.
    use tamarin_term::lterm::LVar;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    let subst = &sys.eq_store.subst;
    let resolve = |v: &LVar| -> LVar {
        let t = tamarin_term::subst::apply_vterm(
            subst,
            Term::Lit(Lit::Var(v.clone())),
        );
        if let Term::Lit(Lit::Var(w)) = t { w } else { v.clone() }
    };
    let mut all_less: Vec<LessAtom> = sys.less_atoms.iter().map(|l| LessAtom {
        smaller: resolve(&l.smaller),
        larger: resolve(&l.larger),
        reason: l.reason,
    }).collect();
    for e in &sys.edges {
        all_less.push(LessAtom {
            smaller: resolve(&e.src.0),
            larger: resolve(&e.tgt.0),
            reason: crate::constraint::constraints::Reason::Adversary,
        });
    }
    // HS-faithful: `rawEdgeRel = sEdges ++ unsolvedChains` (System.hs:1613-
    // 1616) — unsolved chain goals contribute (c.0, p.0) to the less-
    // relation for cycle detection. Without this, RS misses cycles HS
    // catches when the cycle goes through an open chain. Root cause of
    // StatVerif KU(pcs) saturate over-enumeration.
    for (g, st) in &sys.goals {
        if st.solved { continue; }
        if let crate::constraint::constraints::Goal::Chain(c, p) = g {
            all_less.push(LessAtom {
                smaller: resolve(&c.0),
                larger: resolve(&p.0),
                reason: crate::constraint::constraints::Reason::Adversary,
            });
        }
    }
    if cyclic(&all_less) {
        // H14-style diagnostic: dump the actual cycle path so a missing
        // less_atom (vs HS) can be identified by diffing the paths.
        if std::env::var("TAM_RS_DBG_CYCLE_PATH").is_ok() {
            let path = cyclic_with_path(&all_less);
            let path_str: Vec<String> = path.iter()
                .map(|n| format!("{}_{}", n.name, n.idx)).collect();
            eprintln!("[CYCLE_PATH] cycle: {}", path_str.join(" → "));
        }
        out.push(Contradiction::Cyclic);
    }
    // Sort-conflated LVars defence-in-depth: two LVars sharing
    // `(name, idx)` but with disjoint sub-sorts (Pub vs Fresh, etc.)
    // can't be reconciled.  Haskell freshens globally so this never
    // arises; our Maude-witness pipeline could in principle produce
    // such pairs across grafted source-cases.  Empirically this check
    // doesn't fire on the current NSLPK3 false-positive corpus (those
    // FPs have a different root cause — see solver-memory #26), but
    // it's a cheap correctness guard for any future regression.
    if has_sort_conflated_lvars(sys) { out.push(Contradiction::IncompatibleEqs); }
    if sys.subterm_store.is_false() { out.push(Contradiction::SubtermCyclic); }
    if has_subterm_cycle_contra(_ctxt, sys) { out.push(Contradiction::SubtermCyclic); }
    if has_non_normal_terms(_ctxt, sys) { out.push(Contradiction::NonNormalTerms); }
    if has_incompatible_edge_facts(sys) { out.push(Contradiction::IncompatibleEqs); }
    if has_fresh_fact_sort_violation(sys) { out.push(Contradiction::IncompatibleEqs); }
    if sys.eq_store.is_false() { out.push(Contradiction::IncompatibleEqs); }
    // FormulasFalse: detect a `gfalse` (empty disjunction) at the top
    // level. Our `Guarded` represents False as `Disj([])`.
    if has_false_formula(sys) { out.push(Contradiction::FormulasFalse); }
    if has_forbidden_chain(sys) { out.push(Contradiction::ForbiddenChain); }
    if has_forbidden_kd(sys) { out.push(Contradiction::ForbiddenKD); }
    if has_impossible_chain(_ctxt, sys) { out.push(Contradiction::ImpossibleChain); }
    // HS-faithful port: ForbiddenExp (Contradictions.hs:147 +
    // 362-388).  Drops Exp-down rule instances whose g is simple,
    // whose MsgVar args are KU-known earlier, and whose exponent
    // factors are already in the up-premise.  Gated on enableDH.
    if _ctxt.maude.maude_sig().enable_dh && has_forbidden_exp(sys) {
        out.push(Contradiction::ForbiddenExp);
    }
    // ForbiddenBP — still unported (the BP-using corpus is small).
    // Despite the original "Maude-dependent" comment, the HS BP
    // check is structural (Contradictions.hs:357-388 mirrors the
    // ForbiddenExp shape over `em`/`pmult`/`one`) and a future port
    // can follow the ForbiddenExp pattern.
    out.extend(node_after_last(sys));
    out.extend(non_injective_fact_instances(_ctxt, sys));
    out
}

/// `hasNonNormalTerms` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasNonNormalTerms`
/// (`Contradictions.hs:163-166`).
///
/// HS spec:
/// ```haskell
/// hasNonNormalTerms sig se =
///     any (not . (`runReader` hnd) . nf') (maybeNonNormalTerms hnd se)
///   where hnd = L.get sigmMaudeHandle sig
/// ```
///
/// And `nf' = nfViaHaskell` (Norm.hs:130-131) — a PURE structural
/// NF check that walks the term tree against the reducibility
/// patterns in Norm.hs:60-99.  This is NOT a Maude-driven check;
/// it's pattern-based on the signature's reducibility shape.
///
/// Walks every node's premise, conclusion, action facts and
/// `new_vars`; for each subterm whose head could be reducible,
/// asks `nf_via_haskell` whether the term is in normal form.  If
/// any term is not in NF, the system is contradictory (we only
/// ever construct normal-form-respecting traces).
///
/// Skip optimization: when the proof context's signature has an
/// empty `reducible_fun_syms` set (e.g. pair-only or hashing-only,
/// which have no rewrite rules with a reducible head — all
/// destructors come from intruder rules, not subterm rewriting),
/// no term can be in non-normal form structurally, so we skip
/// the per-term check.
///
/// The previous Rust implementation used `maude.reduce(t) != t`
/// (mirroring `nfViaMaude`, Norm.hs:134-136 — `nfViaMaude sortOf t
/// = (t ==) <$> norm sortOf t`).  HS does NOT use `nfViaMaude` for
/// this purpose; it uses `nf'`.  The two predicates can disagree
/// on AC operator argument order (Maude canonicalises `mult(tid,
/// x)` and `mult(x, tid)` to the same form, but the pure
/// structural check treats both as in NF) — the same reason
/// `subst_creates_non_normal_terms` was switched to `nf_via_haskell`
/// in commit `a7b2e3c5`.  The two checks are observably equivalent
/// on the current corpus (no lemma's verdict changes) but the
/// mechanism alignment to HS source is the point.
fn has_non_normal_terms(ctx: &ProofContext, sys: &System) -> bool {
    // NF check is cheap (pure structural walk) but we call this
    // from `is_finished` on every expand step, so the early-exit
    // still helps for pair-only theories with no subterm rewrite
    // rules.
    //
    // Set TAM_SKIP_NF=1 to disable (e.g. for speed-critical probes).
    if std::env::var("TAM_SKIP_NF").is_ok() { return false; }
    let sig = ctx.maude.maude_sig();
    if sig.reducible_fun_syms.is_empty() { return false; }
    let irreducible = &sig.irreducible_fun_syms;

    // Collect every (possibly-not-NF) subterm across all node
    // facts and new-vars.  Mirrors Haskell's `maybeNonNormalTerms`
    // ∘ `maybeNotNfSubterms`.
    let mut candidates: std::collections::BTreeSet<tamarin_term::lterm::LNTerm>
        = std::collections::BTreeSet::new();
    for (_, rule) in &sys.nodes {
        for f in rule.premises.iter().chain(&rule.conclusions).chain(&rule.actions) {
            for t in &f.terms {
                maybe_not_nf_subterms(irreducible, t, &mut candidates);
            }
        }
        for t in &rule.new_vars {
            maybe_not_nf_subterms(irreducible, t, &mut candidates);
        }
    }
    if candidates.is_empty() { return false; }

    // HS-faithful NF check: `nf'` = `nfViaHaskell` (Norm.hs:131).
    // Short-circuit on the first term that is NOT in NF.
    for t in &candidates {
        if !tamarin_term::norm::nf_via_haskell(&ctx.maude, t) {
            return true;
        }
    }
    false
}

/// `maybeNotNfSubterms` — collect subterms that might not be in
/// normal form.  Constants in NF; irreducible-headed apps recurse
/// into args; anything else (variables OR reducible-headed apps)
/// is returned as a candidate.
///
/// Variables MUST be included — for `subst_creates_non_normal_terms`,
/// a variable `z` becomes a reducible term after the variant subst
/// (e.g. `{z → verify(s,m,pkA)}`).  Without including vars we miss
/// the SplitG variant filter and the picked variant pulls the
/// reducible term into the system unfiltered.
/// Mirrors Haskell `maybeNotNfSubterms` exactly (Norm.hs:162-168):
/// the `_` arm catches both `Lit (Var _)` and reducible `FApp`.
///
/// For `has_non_normal_terms` the variable case is harmless:
/// `reduce(z) == z` since variables are already NF, and the
/// Maude bridge caches the result.
fn maybe_not_nf_subterms(
    irreducible: &tamarin_term::function_symbols::FunSig,
    t: &tamarin_term::lterm::LNTerm,
    out: &mut std::collections::BTreeSet<tamarin_term::lterm::LNTerm>,
) {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Con(_)) => {}
        Term::App(sym, args) if irreducible.contains(sym) => {
            for a in args {
                maybe_not_nf_subterms(irreducible, a, out);
            }
        }
        _ => { out.insert(t.clone()); }
    }
}

/// Run `has_subterm_cycle` against the system's positive subterm
/// dag.  Equivalent to one prong of Haskell's `simpSubterms` →
/// `hasSubtermCycle` check; we run it eagerly during contradiction
/// detection because our `simpSubterms` pass is currently a stub.
fn has_subterm_cycle_contra(ctx: &ProofContext, sys: &System) -> bool {
    let reducible = &ctx.maude.maude_sig().reducible_fun_syms;
    crate::tools::subterm_store::has_subterm_cycle(reducible, &sys.subterm_store)
}

/// `hasImpossibleChain` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasImpossibleChain`
/// (`Contradictions.hs:225`).
///
/// For every chain goal `(c, p)`:
///   - Collect the root symbols reachable from `t_start = c`'s
///     KD-conclusion term via deconstruction (`possible_root_syms`).
///   - Collect the possible root symbols of `t_end = p`'s KD-prem
///     term (`possible_end_syms` — the set of root symbols any
///     subterm of `t_end` could have).
///
/// If both sets are determined and don't intersect, the chain
/// can never be solved — declare contradictory.
///
/// Skips DH/BP-specific cases (FExp/FPMult/FEMap) for now —
/// corpus filters DH/BP-using protocols.  When DH support lands,
/// these branches need adding.
fn has_impossible_chain(ctx: &ProofContext, sys: &System) -> bool {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    let dbg = std::env::var("TAM_RS_DBG_IMPOSSIBLE_CHAIN").is_ok();

    for (g, st) in &sys.goals {
        if st.solved { continue; }
        let Goal::Chain(c, p) = g else { continue };
        let c_rule = sys.nodes.iter().find(|(id, _)| id == &c.0)
            .map(|(_, r)| r);
        let p_rule = sys.nodes.iter().find(|(id, _)| id == &p.0)
            .map(|(_, r)| r);
        let (Some(c_rule), Some(p_rule)) = (c_rule, p_rule) else { continue };
        let conc_fact = match c_rule.conclusions.get(c.1.0) {
            Some(f) => f, None => continue,
        };
        let prem_fact = match p_rule.premises.get(p.1.0) {
            Some(f) => f, None => continue,
        };
        if !matches!(conc_fact.tag, FactTag::Kd) { continue; }
        if !matches!(prem_fact.tag, FactTag::Kd) { continue; }
        let t_start = match conc_fact.terms.first() { Some(t) => t, None => continue };
        let t_end = match prem_fact.terms.first() { Some(t) => t, None => continue };
        let poss_opt = possible_root_syms(t_start);
        if dbg {
            use tamarin_term::pretty::pretty_lnterm;
            eprintln!("[ic] t_start={} t_end={} poss_root={:?} pc_true_subterm={}",
                pretty_lnterm(t_start), pretty_lnterm(t_end),
                poss_opt.is_some(), ctx.pc_true_subterm);
        }
        let Some(poss) = poss_opt else { continue };
        // Haskell:
        //   if pcTrueSubterm
        //      then do req_end <- rootSym t_end
        //              return $ not (req_end `elem` poss)
        //      else do req_end <- possibleEndSyms t_end
        //              return $ null (req_end `intersect` poss)
        // True branch: STRICT — fire if the chain-end's root sym is
        // not among the possible decomposition syms.
        // False branch: LENIENT — fire only if NO subterm sym of the
        // chain-end matches any possible decomposition sym.
        let fires = if ctx.pc_true_subterm {
            match root_sym(t_end) {
                Some(req) => !poss.iter().any(|s| s == &req),
                None => false,
            }
        } else {
            match possible_end_syms(t_end) {
                Some(req) => poss.iter().all(|s| !req.contains(s)),
                None => false,
            }
        };
        if dbg {
            eprintln!("[ic] fires={}", fires);
        }
        if fires {
            return true;
        }
    }
    false
}

/// Determines the root symbol of a term if it can be statically
/// fixed.  Mirrors Haskell's `rootSym`:
///   - `FApp sym _` → `Some(Right sym)`
///   - `Lit _` of sort Msg → `None` (a Msg-var could be anything)
///   - `Lit _` otherwise → `Some(Left sort)` (sort fixes the value)
///
/// Encoding in Rust: we use a tagged enum-like type expressed as
/// an `Option<RootSym>` where RootSym has both branches.
#[derive(Clone, PartialEq, Eq, Hash)]
enum RootSym {
    Sym(tamarin_term::function_symbols::FunSym),
    Sort(tamarin_term::lterm::LSort),
}

fn root_sym(t: &tamarin_term::lterm::LNTerm) -> Option<RootSym> {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::App(sym, _) => Some(RootSym::Sym(sym.clone())),
        Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg => None,
        Term::Lit(Lit::Var(v)) => Some(RootSym::Sort(v.sort)),
        Term::Lit(Lit::Con(n)) => {
            use tamarin_term::lterm::NameTag;
            let s = match n.tag {
                NameTag::Pub => LSort::Pub,
                NameTag::Fresh => LSort::Fresh,
                NameTag::Nat => LSort::Nat,
                NameTag::Node => LSort::Node,
            };
            Some(RootSym::Sort(s))
        }
    }
}

/// `possibleEndSyms`: collect the root symbol of `t` and recursively
/// of all its subterms.  Returns `None` if any subterm's root symbol
/// is undetermined (Msg-var).
fn possible_end_syms(
    t: &tamarin_term::lterm::LNTerm,
) -> Option<Vec<RootSym>> {
    use tamarin_term::term::Term;
    let head = root_sym(t)?;
    match t {
        Term::App(_, args) => {
            let mut out = vec![head];
            for a in args {
                let sub = possible_end_syms(a)?;
                out.extend(sub);
            }
            Some(out)
        }
        Term::Lit(_) => Some(vec![head]),
    }
}

/// `possibleRootSyms`: same as `possible_end_syms` but returns
/// `Some([])` (no possible decomposition) when the term cannot
/// contain fresh names or private functions — equivalent to
/// `isForbiddenDeconstruction`.
fn possible_root_syms(
    t: &tamarin_term::lterm::LNTerm,
) -> Option<Vec<RootSym>> {
    if never_contains_fresh_priv(t) {
        return Some(Vec::new());
    }
    possible_end_syms(t)
}

/// `hasForbiddenKD` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasForbiddenKD`
/// (`Contradictions.hs:131`).
///
/// A KD-conclusion `KD(t)` is forbidden if *no instance* of `t`
/// can ever contain fresh names or private function symbols —
/// because then the adversary already knows `t` (it can be
/// derived from public constants and public function symbols
/// alone), so deconstructing it via KD-chain would be wasteful
/// and violates normal form N6.
///
/// `neverContainsFreshPriv t`:
///   - no subterm uses a private function symbol, AND
///   - every literal (variable or constant) has sort in
///     `{Pub, Nat, Node}` — no `Msg` or `Fresh` literals.
///
/// (A `Msg` literal could instantiate to anything including
/// fresh, so we must conservatively say it *might* contain
/// fresh.  Same for `Fresh` literals.)
///
/// Skipped in diff mode (Haskell guards with `not isDiffSystem`).
fn has_forbidden_kd(sys: &System) -> bool {
    use crate::fact::FactTag;
    if sys.side.is_some() { return false; } // diff-system guard
    for (_, rule) in &sys.nodes {
        for fa in &rule.conclusions {
            if !matches!(fa.tag, FactTag::Kd) { continue; }
            let Some(t) = fa.terms.first() else { continue };
            if never_contains_fresh_priv(t) { return true; }
        }
    }
    false
}

/// True iff no instance of `t` can ever contain fresh names or
/// private function symbols.  Walks the term; rejects Msg/Fresh
/// literals (they could instantiate to anything) and any private
/// function symbol.
fn never_contains_fresh_priv(t: &tamarin_term::lterm::LNTerm) -> bool {
    use tamarin_term::function_symbols::{FunSym, Privacy};
    use tamarin_term::lterm::{LSort, NameTag};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => {
            !matches!(v.sort, LSort::Msg | LSort::Fresh)
        }
        Term::Lit(Lit::Con(n)) => {
            !matches!(n.tag, NameTag::Fresh)
        }
        Term::App(sym, args) => {
            // Reject if the head is a private function symbol.
            let is_private = match sym {
                FunSym::NoEq(s) => s.privacy == Privacy::Private,
                _ => false,
            };
            if is_private { return false; }
            args.iter().all(never_contains_fresh_priv)
        }
    }
}

/// `hasForbiddenChain` — port of Haskell's
/// `Theory.Constraint.Solver.Contradictions.hasForbiddenChain`
/// (`Contradictions.hs:284`).
///
/// Detects normal-form-violating chains.  A `Chain(c, p)` goal is
/// forbidden when:
///
///   1. The chain start (KD-conc at `c`) is a *message variable*
///      (LVar of sort Msg) — i.e. the adversary doesn't know what
///      term they're deconstructing.
///   2. The chain end (KD-prem at `p`) is *not* an `IEquality`
///      rule instance (those are exempt; they're the diff-mode
///      equality bridge).
///   3. There exists a `KU(t_start)` action somewhere in the
///      system whose node strictly *precedes* the chain start
///      `nodeConcNode c`.
///
/// All three conditions together violate normal form invariant
/// N6: if the adversary already knew `t_start` (KU before), they
/// shouldn't be deconstructing it (KD chain) afterwards.  Hits an
/// otherwise-undetected contradiction earlier than the search
/// would, pruning a search branch.
fn has_forbidden_chain(sys: &System) -> bool {
    use crate::constraint::constraints::Goal;
    use crate::fact::FactTag;
    use tamarin_term::lterm::is_msg_var;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // Build a disj-equivalence relation over Msg-Vars: two vars are
    // equivalent if, in some disj subst, they both have the same
    // non-trivial image.  Mirrors HS's behavior at this case state
    // where simp would have folded the disj down to one subst before
    // the contradictions check — but RS's variant-pick produces a
    // 2-subst disj that simp doesn't fold (subst[0] keeps the var,
    // subst[1] binds it to a concrete term).  HS's path commits to
    // subst[0] via simpMinimize+substCreatesNonNormalTerms on subst[1];
    // since RS's NF check doesn't catch this case, walk the disj
    // substs directly and treat vars that coincide in any branch as
    // equivalent.
    //
    // For each disj subst, group vars by their image term.  Vars
    // sharing a non-trivial image in some subst are equivalent under
    // that branch.  Conservative: treat them as equivalent for the
    // ForbiddenChain check, which means firing on chains where t_start
    // would equal a KU-action term in any branch.  Root cause of
    // StatVerif Resolve2_d_1_check_getmsg_d_0_fst_d_1_check_getmsg
    // case survival (see [[project-statverif-aborted-contract-reachable]]).
    let mut equivalence_classes: std::collections::HashMap<
        tamarin_term::lterm::LVar,
        std::collections::HashSet<tamarin_term::lterm::LVar>> =
        std::collections::HashMap::new();
    // Compute a coarse "head signature" of a term for grouping: the
    // outermost function symbol (or Var/Const tag).  Two Msg-Vars
    // mapped to App-headed terms with the same outer function symbol
    // in the same disj subst are treated as candidate-equivalent — they
    // would unify modulo the inner witness aliasing.  This catches HS's
    // variant-pick behavior where Maude returns multiple unifiers but
    // simp collapses them to a single canonical form.
    let term_head_sig = |t: &tamarin_term::lterm::LNTerm| -> Option<Vec<u8>> {
        match t {
            Term::App(tamarin_term::function_symbols::FunSym::NoEq(sym), _) =>
                Some(sym.name.clone()),
            _ => None,
        }
    };
    for disj in &sys.eq_store.conj {
        for subst in &disj.substs {
            let pairs = subst.to_list();
            // Group Msg-vars by their image's outermost function symbol.
            let mut by_head: std::collections::HashMap<
                Vec<u8>,
                Vec<tamarin_term::lterm::LVar>> = std::collections::HashMap::new();
            for (v, t) in pairs {
                if v.sort != tamarin_term::lterm::LSort::Msg { continue; }
                let head = match term_head_sig(&t) {
                    Some(h) => h, None => continue,
                };
                by_head.entry(head).or_default().push(v);
            }
            for (_, vars) in by_head {
                if vars.len() < 2 { continue; }
                for vi in &vars {
                    for vj in &vars {
                        if vi == vj { continue; }
                        equivalence_classes.entry(vi.clone())
                            .or_default().insert(vj.clone());
                    }
                }
            }
        }
    }

    for (g, st) in &sys.goals {
        if st.solved { continue; }
        let Goal::Chain(c, p) = g else { continue };
        // Look up the chain-conc fact.
        let c_rule = sys.nodes.iter().find(|(id, _)| id == &c.0)
            .map(|(_, r)| r);
        let p_rule = sys.nodes.iter().find(|(id, _)| id == &p.0)
            .map(|(_, r)| r);
        let (Some(c_rule), Some(p_rule)) = (c_rule, p_rule) else { continue };
        let conc_fact = match c_rule.conclusions.get(c.1.0) {
            Some(f) => f, None => continue,
        };
        let prem_fact = match p_rule.premises.get(p.1.0) {
            Some(f) => f, None => continue,
        };
        // Chain ends and starts must both be KD facts.
        if !matches!(conc_fact.tag, FactTag::Kd) { continue; }
        if !matches!(prem_fact.tag, FactTag::Kd) { continue; }
        // Apply eq_store subst to chain conc term — substSystem may not
        // have run since the last variant fold, so the rule's raw conc
        // can lag behind the canonical term.  HS evaluates `nodeConcFact`
        // through the eq-store-substituted node lookup; mirror that here.
        let raw_t_start = match conc_fact.terms.first() { Some(t) => t.clone(), None => continue };
        let t_start_owned = tamarin_term::subst::apply_vterm(&sys.eq_store.subst, raw_t_start);
        let t_start = &t_start_owned;
        // (1) Chain starts at a message variable.
        if !is_msg_var(t_start) { continue; }
        // (2) End rule is not IEquality.
        if matches!(&p_rule.info,
            crate::rule::RuleInfo::Intr(crate::rule::IntrRuleACInfo::IEquality)) {
            continue;
        }
        let t_start_var = match t_start {
            Term::Lit(Lit::Var(v)) => v.clone(),
            _ => continue,
        };
        // Build the set of candidate-equal Msg-Vars: t_start itself
        // plus any var in its disj-equivalence class.
        let mut candidate_vars: std::collections::HashSet<tamarin_term::lterm::LVar>
            = std::collections::HashSet::new();
        candidate_vars.insert(t_start_var.clone());
        if let Some(eqs) = equivalence_classes.get(&t_start_var) {
            for v in eqs {
                candidate_vars.insert(v.clone());
            }
        }
        let candidate_terms: Vec<tamarin_term::lterm::LNTerm> = candidate_vars.iter()
            .map(|v| Term::Lit(Lit::Var(v.clone()))).collect();
        // (3) Some KU(t_start) action node precedes the chain
        // start `c.0`.  HS-faithful: `allKUActions` (System.hs:1582-1585)
        // unions BOTH `unsolvedActionAtoms` (unsolved ActionG goals)
        // AND node `rActs` lists.  Rust previously only checked node
        // actions, missing the unsolved-goal half — Cyclic/ForbiddenChain
        // didn't fire on chain-destruction branches where t_start is
        // a Msg-var that appears as an open KU action goal (no node yet
        // labeled).  Root cause of StatVerif Resolve1/Resolve2 KU(pcs)
        // case survival.
        //
        // Walk node actions first:
        for (id, rule) in &sys.nodes {
            for fa in &rule.actions {
                if !matches!(fa.tag, FactTag::Ku) { continue; }
                let t_ku = match fa.terms.first() { Some(t) => t, None => continue };
                if !candidate_terms.contains(t_ku) { continue; }
                if id == &c.0 { continue; }
                if sys.always_before(id, &c.0) {
                    return true;
                }
            }
        }
        // Then walk unsolved ActionG goals (HS's `unsolvedActionAtoms`):
        for (g, gst) in &sys.goals {
            if gst.solved { continue; }
            let Goal::Action(id, fa) = g else { continue };
            if !matches!(fa.tag, FactTag::Ku) { continue; }
            let t_ku = match fa.terms.first() { Some(t) => t, None => continue };
            if !candidate_terms.contains(t_ku) { continue; }
            if id == &c.0 { continue; }
            if sys.always_before(id, &c.0) {
                return true;
            }
        }
    }
    false
}

/// HS-faithful port of `hasForbiddenExp`
/// (`Theory.Constraint.Solver.Contradictions:364-388`).
///
/// Detects an `Exp-down` (d_exp) rule instance whose conclusion is
/// not allowed in a normal dependency graph.
///
/// The check: for each node whose rule has shape
///   [ KD(p1 :: exp(_, _)), KU(b) ] -> [ KD(conc) ]
/// the rule is forbidden iff
///   (1) conc has shape `KD(exp(g, c))` AND
///       - `g` is simple (no fresh names/vars, no private syms)
///       - all `MsgVar` args of `g` are KU-known earlier than `i`
///       - every non-inverse factor of `c` is already a factor of `b`
///         (`niFactors c \\ niFactors b == []`)
///   OR
///   (2) conc has shape `KD(g)` (not an exp) AND
///       - `g` is simple
///       - all `MsgVar` args of `g` are KU-known earlier than `i`
///
/// Without this, RS lets through every variant d_exp chain extend
/// regardless of whether the resulting destruction is constructible
/// from the original KU premise — at the saturate step for
/// `KU(exp(t.1,t.2))`, RS produces 16 cases vs HS's 3, because each
/// of the 4 surviving d_exp chain-extend variants would be dropped
/// by ForbiddenExp in HS (verified in agent #11 trace: HS_SAS_CONTRA
/// shows `[ForbiddenExp]` for 3 of 4 d_exp branches with
/// cn=["...","d_exp"]).
fn has_forbidden_exp(sys: &System) -> bool {
    use crate::fact::FactTag;
    use crate::rule::{IntrRuleACInfo, RuleInfo};
    use tamarin_term::function_symbols::{EXP_SYM_STRING, FunSym, AcSym, INV_SYM_STRING};
    use tamarin_term::lterm::{LNTerm, LSort, is_msg_var, frees, contains_private, sort_of_name};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;

    // `niFactors`: HS Term/LTerm.hs:351-355.  The non-inverse
    // factors of a term.  `Mult(ts...)` → concat-map ni_factors;
    // `Inv(t)` → ni_factors t; else `[t]`.
    fn ni_factors(t: &LNTerm) -> Vec<LNTerm> {
        match t {
            Term::App(FunSym::Ac(AcSym::Mult), args) => {
                let mut out = Vec::new();
                for a in args { out.extend(ni_factors(a)); }
                out
            }
            Term::App(FunSym::NoEq(s), args)
                if s.name == INV_SYM_STRING && args.len() == 1 =>
            {
                ni_factors(&args[0])
            }
            _ => vec![t.clone()],
        }
    }

    // `isSimpleTerm`: HS Term/LTerm.hs:383-386.
    // `not (containsPrivate t) && all (LSortFresh /=) (lits t)`.
    fn is_simple_term(t: &LNTerm) -> bool {
        if contains_private(t) { return false; }
        let mut ok = true;
        let mut visit = |term: &LNTerm| {
            match term {
                Term::Lit(Lit::Var(v)) => {
                    if v.sort == LSort::Fresh { ok = false; }
                }
                Term::Lit(Lit::Con(c)) => {
                    if sort_of_name(c) == LSort::Fresh {
                        ok = false;
                    }
                }
                _ => {}
            }
        };
        fn walk(t: &LNTerm, f: &mut dyn FnMut(&LNTerm)) {
            f(t);
            if let Term::App(_, args) = t {
                for a in args { walk(a, f); }
            }
        }
        walk(t, &mut visit);
        ok
    }

    // `kFactView`: returns (DirTag, term) for KU / KD facts.
    // DirTag::Up = KU (constructible), DirTag::Dn = KD (destruction).
    #[derive(Copy, Clone, PartialEq, Eq)]
    enum DirTag { Up, Dn }
    fn k_fact_view<'a>(fa: &'a crate::fact::LNFact) -> Option<(DirTag, &'a LNTerm)> {
        if fa.terms.len() != 1 { return None; }
        match fa.tag {
            FactTag::Ku => Some((DirTag::Up, &fa.terms[0])),
            FactTag::Kd => Some((DirTag::Dn, &fa.terms[0])),
            _ => None,
        }
    }
    fn view_exp(t: &LNTerm) -> Option<(&LNTerm, &LNTerm)> {
        if let Term::App(FunSym::NoEq(s), args) = t {
            if s.name == EXP_SYM_STRING && args.len() == 2 {
                return Some((&args[0], &args[1]));
            }
        }
        None
    }

    // `allKUActions`: HS System.hs:1582-1585.  Unions
    // `unsolvedActionAtoms sys` (open KU goals) and the
    // `rActs` lists of each node.  Returns (NodeId, fact, term).
    // For "knownEarlier" we only need (NodeId, term).
    let mut all_ku: Vec<(NodeId, LNTerm)> = Vec::new();
    for (g, st) in &sys.goals {
        if st.solved { continue; }
        if let crate::constraint::constraints::Goal::Action(i, fa) = g {
            if matches!(fa.tag, FactTag::Ku) {
                if let Some(m) = fa.terms.first() {
                    all_ku.push((i.clone(), m.clone()));
                }
            }
        }
    }
    for (id, rule) in &sys.nodes {
        for fa in &rule.actions {
            if matches!(fa.tag, FactTag::Ku) {
                if let Some(m) = fa.terms.first() {
                    all_ku.push((id.clone(), m.clone()));
                }
            }
        }
    }

    // Mirror HS `forbiddenDExp` exactly.
    for (i, ru) in &sys.nodes {
        // Only intruder DestrRules can be exp-down; cheap pre-filter.
        if !matches!(&ru.info,
            RuleInfo::Intr(IntrRuleACInfo::DestrRule(_, _, _, _)))
        { continue; }
        if ru.premises.len() != 2 { continue; }
        if ru.conclusions.len() != 1 { continue; }
        let p1 = &ru.premises[0];
        let p2 = &ru.premises[1];
        let conc = &ru.conclusions[0];

        let (dt1, p1_term) = match k_fact_view(p1) { Some(x) => x, None => continue };
        if dt1 != DirTag::Dn { continue; }
        if view_exp(p1_term).is_none() { continue; }
        let (dt2, b) = match k_fact_view(p2) { Some(x) => x, None => continue };
        if dt2 != DirTag::Up { continue; }

        let (dtc, conc_term) = match k_fact_view(conc) { Some(x) => x, None => continue };
        if dtc != DirTag::Dn { continue; }

        // The "earlier MsgVars" set: KU-known terms which are MsgVars
        // whose node `j` is `alwaysBefore` `i`.
        let earlier_msg_vars = || -> Vec<LNTerm> {
            let mut out = Vec::new();
            for (j, t) in &all_ku {
                if !is_msg_var(t) { continue; }
                if sys.always_before(j, i) {
                    out.push(t.clone());
                }
            }
            out
        };
        let all_msg_vars_known_earlier = |g: &LNTerm| -> bool {
            let mvs = earlier_msg_vars();
            // `varTerm <$> frees g` then keep only MsgVars.
            for v in frees(g) {
                let vt: LNTerm = Term::Lit(Lit::Var(v.clone()));
                if !is_msg_var(&vt) { continue; }
                if !mvs.contains(&vt) {
                    return false;
                }
            }
            true
        };

        let forbidden = if let Some((g, c)) = view_exp(conc_term) {
            // (1) conc = exp(g, c): g simple + all msg vars known earlier
            //     + niFactors c \\ niFactors b == []
            if !is_simple_term(g) { false }
            else if !all_msg_vars_known_earlier(g) { false }
            else {
                let nfc = ni_factors(c);
                let nfb = ni_factors(b);
                // multiset difference: every element of nfc must appear in nfb.
                let mut nfb_remaining = nfb.clone();
                let mut all_in_b = true;
                for x in &nfc {
                    if let Some(pos) = nfb_remaining.iter().position(|y| y == x) {
                        nfb_remaining.remove(pos);
                    } else {
                        all_in_b = false;
                        break;
                    }
                }
                all_in_b
            }
        } else {
            // (2) conc = g (not exp-shaped)
            is_simple_term(conc_term) && all_msg_vars_known_earlier(conc_term)
        };

        if forbidden {
            if std::env::var("TAM_RS_DBG_FORBIDDEN_EXP").is_ok() {
                eprintln!("[FORBIDDEN_EXP] node={:?} ru_concl={:?}", i, conc_term);
            }
            return true;
        }
    }
    false
}

/// Direct port of Haskell's `nonInjectiveFactInstances`
/// (`Theory.Constraint.Solver.Contradictions:186`).
///
/// For every edge `(i,_) → (k,_)` whose conclusion fact has an
/// injective tag and first term `t`, find every reachable node `j`
/// (via the raw less-relation) such that `j ≠ i, k` and `j`'s rule
/// produces or consumes a fact of the same tag with the same first
/// term, AND `k` is reachable from `j` (or `k` is the last node).
///
/// Such a `(i, j, k)` triple witnesses two simultaneous "live"
/// instances of the injective fact, contradicting injectivity.
fn non_injective_fact_instances(
    ctxt: &ProofContext,
    sys: &System,
) -> Vec<Contradiction> {
    let mut out = Vec::new();
    let inj_tags: BTreeSet<&crate::fact::FactTag> =
        ctxt.injective_fact_insts.iter().map(|(t, _)| t).collect();
    if inj_tags.is_empty() { return out; }

    // Build reverse adjacency: who can reach whom via less + edges.
    // We re-implement here rather than reuse always_before because we
    // need to enumerate reachable sets, not query a single pair.
    let mut adj: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for l in &sys.less_atoms {
        adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
    }
    for e in &sys.edges {
        adj.entry(e.src.0.clone()).or_default().push(e.tgt.0.clone());
    }
    let reachable = |from: &NodeId| -> BTreeSet<NodeId> {
        let mut out = BTreeSet::new();
        let mut stack = vec![from.clone()];
        while let Some(n) = stack.pop() {
            if !out.insert(n.clone()) { continue; }
            if let Some(succs) = adj.get(&n) {
                for s in succs { stack.push(s.clone()); }
            }
        }
        out.remove(from);
        out
    };
    let lookup_node = |id: &NodeId| -> Option<&crate::rule::RuleACInst> {
        sys.nodes.iter().find(|(n, _)| n == id).map(|(_, r)| r)
    };

    for e in &sys.edges {
        let (i, conc_idx) = (e.src.0.clone(), e.src.1.clone());
        let k = e.tgt.0.clone();
        // Look up the conclusion fact at (i, conc_idx).
        let i_rule = match lookup_node(&i) { Some(r) => r, None => continue };
        let k_fa_prem = match i_rule.conclusions.get(conc_idx.0) {
            Some(f) => f, None => continue,
        };
        if !inj_tags.contains(&k_fa_prem.tag) { continue; }
        let k_term = match k_fa_prem.terms.first() {
            Some(t) => t, None => continue,
        };
        // Reachable set from i.
        let reach = reachable(&i);
        for j in &reach {
            if j == &i || j == &k { continue; }
            let j_rule = match lookup_node(j) { Some(r) => r, None => continue };
            // Conflicting fact in j's prems or concs.
            let conflicting = |fa: &crate::fact::LNFact| -> bool {
                fa.tag == k_fa_prem.tag && fa.terms.first() == Some(k_term)
            };
            let has_conflict = j_rule.premises.iter().any(conflicting)
                || j_rule.conclusions.iter().any(conflicting);
            if !has_conflict { continue; }
            // k reachable from j OR k is the last node.
            let j_reach = reachable(j);
            let k_after_j = j_reach.contains(&k);
            let k_is_last = sys.last_atom.as_ref() == Some(&k);
            if k_after_j || k_is_last {
                out.push(Contradiction::NonInjectiveFactInstance(
                    i.clone(), j.clone(), k.clone(),
                ));
            }
        }
    }
    out
}

/// Detect two LVars sharing `(name, idx)` but with disjoint sub-sorts.
/// Pub/Fresh/Nat are pairwise disjoint sub-sorts of Msg; if the system
/// contains both `~mw:Pub 58` and `~mw:Fresh 58`, no model can satisfy
/// both occurrences simultaneously.  Returns true if any such conflict
/// exists.
fn has_sort_conflated_lvars(sys: &System) -> bool {
    use tamarin_term::lterm::{HasFrees, LSort, LVar};
    use std::cell::RefCell;
    let seen: RefCell<BTreeMap<(String, u64), LSort>> = RefCell::new(BTreeMap::new());
    let conflict: RefCell<bool> = RefCell::new(false);
    let mut visit = |v: &LVar| {
        if *conflict.borrow() { return; }
        let mut s = seen.borrow_mut();
        let key = (v.name.clone(), v.idx);
        match s.get(&key).copied() {
            None => { s.insert(key, v.sort); }
            Some(prev) if prev == v.sort => {}
            Some(prev) => {
                // Two distinct sorts at same (name, idx).  Pub/Fresh/
                // Nat are disjoint; pairs that include Msg can be
                // narrowed (Msg is the join), so don't flag those.
                let disjoint = matches!((prev, v.sort),
                    (LSort::Pub, LSort::Fresh) | (LSort::Fresh, LSort::Pub) |
                    (LSort::Pub, LSort::Nat)   | (LSort::Nat, LSort::Pub) |
                    (LSort::Fresh, LSort::Nat) | (LSort::Nat, LSort::Fresh));
                if disjoint {
                    *conflict.borrow_mut() = true;
                }
            }
        }
    };
    for (id, rule) in &sys.nodes {
        id.for_each_free(&mut visit);
        rule.for_each_free(&mut visit);
        if *conflict.borrow() { return true; }
    }
    for e in &sys.edges {
        e.src.0.for_each_free(&mut visit);
        e.tgt.0.for_each_free(&mut visit);
        if *conflict.borrow() { return true; }
    }
    for l in &sys.less_atoms {
        l.smaller.for_each_free(&mut visit);
        l.larger.for_each_free(&mut visit);
        if *conflict.borrow() { return true; }
    }
    if let Some(la) = &sys.last_atom { la.for_each_free(&mut visit); }
    for (g, _) in &sys.goals {
        match g {
            crate::constraint::constraints::Goal::Action(n, fa) => {
                n.for_each_free(&mut visit);
                fa.for_each_free(&mut visit);
            }
            crate::constraint::constraints::Goal::Premise(p, fa) => {
                p.0.for_each_free(&mut visit);
                fa.for_each_free(&mut visit);
            }
            crate::constraint::constraints::Goal::Chain(c, p) => {
                c.0.for_each_free(&mut visit);
                p.0.for_each_free(&mut visit);
            }
            _ => {}
        }
        if *conflict.borrow() { return true; }
    }
    let c = *conflict.borrow();
    c
}

/// Has the system's formula list been forced to ⊥?
fn has_false_formula(sys: &System) -> bool {
    use crate::guarded::Guarded;
    sys.formulas.iter().any(|f| matches!(f, Guarded::Disj(v) if v.is_empty()))
}

/// `Fr(t)` requires `t` to be a Fresh-sorted variable. Maude's
/// sort-aware unifier rejects bindings like `seed = f(k)` where
/// `f` is a constructor (returning Msg sort). When our source-case
/// grafting bypasses that check — e.g. on Minimal_HashChain where
/// the Gen_Start direct-to-Gen_Stop precomputed case is grafted
/// onto a runtime `!Final(f(k))` premise, conflating Gen_Start's
/// `seed` with `f(k)` — the resulting `Fr(f(k))` is unsatisfiable.
/// Mirrors the sort-check Haskell's unifier performs implicitly.
fn has_fresh_fact_sort_violation(sys: &System) -> bool {
    use tamarin_term::lterm::LSort;
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use crate::fact::FactTag;
    let subst = &sys.eq_store.subst;
    for (_, rule) in &sys.nodes {
        // Check premises (where Fr lives) and conclusions/actions
        // for completeness — any Fresh-tagged fact with a non-Fresh
        // term is a sort violation.
        for fact in rule.premises.iter()
            .chain(rule.conclusions.iter())
            .chain(rule.actions.iter())
        {
            if !matches!(fact.tag, FactTag::Fresh) { continue; }
            let t = match fact.terms.first() { Some(t) => t, None => continue };
            let t_norm = tamarin_term::subst::apply_vterm(subst, t.clone());
            match t_norm {
                Term::Lit(Lit::Var(v)) if v.sort == LSort::Fresh => {}
                Term::Lit(Lit::Var(v)) if v.sort == LSort::Msg => {
                    // Msg can narrow to Fresh later — don't flag.
                    let _ = v;
                }
                _ => return true,
            }
        }
    }
    false
}

/// Soundness invariant: every edge in a well-formed system must
/// connect a conclusion and premise with identical fact tags (and
/// arity).  Tamarin's `solveChainGoal` / `solvePremise` only ever
/// add edges after `solveFactEqs` succeeds, which requires the
/// fact tags to match.  In our port, an edge with mismatched tags
/// can arise when node-id substitution collapses a case node onto
/// an unrelated live node — the edge survives the rename but
/// connects incompatible facts.  Such a system has no model.
fn has_incompatible_edge_facts(sys: &System) -> bool {
    for e in &sys.edges {
        let src_rule = sys.nodes.iter().find(|(id, _)| id == &e.src.0);
        let tgt_rule = sys.nodes.iter().find(|(id, _)| id == &e.tgt.0);
        let (Some((_, sr)), Some((_, tr))) = (src_rule, tgt_rule) else {
            continue;
        };
        let fc = match sr.conclusions.get(e.src.1.0) { Some(f) => f, None => continue };
        let fp = match tr.premises.get(e.tgt.1.0) { Some(f) => f, None => continue };
        if fc.tag != fp.tag || fc.terms.len() != fp.terms.len() {
            return true;
        }
    }
    false
}

/// True if the strict `<` partial order has a cycle.
pub fn cyclic(less: &[LessAtom]) -> bool {
    // Build adjacency list keyed by NodeId.
    let mut adj: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for l in less {
        adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
    }
    // Run DFS detecting back-edges.
    let mut color: BTreeMap<NodeId, u8> = BTreeMap::new(); // 0=white,1=gray,2=black
    let nodes: Vec<NodeId> = adj.keys().cloned().collect();
    fn dfs(
        node: &NodeId,
        adj: &BTreeMap<NodeId, Vec<NodeId>>,
        color: &mut BTreeMap<NodeId, u8>,
    ) -> bool {
        match color.get(node).copied().unwrap_or(0) {
            1 => return true,    // gray ancestor → back-edge
            2 => return false,   // already explored
            _ => {}
        }
        color.insert(node.clone(), 1);
        if let Some(succs) = adj.get(node) {
            for s in succs {
                if dfs(s, adj, color) { return true; }
            }
        }
        color.insert(node.clone(), 2);
        false
    }
    for n in &nodes {
        if dfs(n, &adj, &mut color) { return true; }
    }
    false
}

/// `cyclic_with_path` — same as `cyclic` but returns the cycle path
/// when one exists.  Intended for H14-style diagnostics: when HS
/// detects a Cyclic contradiction at some cn but RS doesn't, comparing
/// HS's cycle path against RS's available less_atoms shows EXACTLY
/// which less_atom is missing in RS.
///
/// **Instrumentation that would have caught H14.x earlier**: add a
/// `TAM_RS_DBG_CYCLE_PATH=1` env-gated trace at every contradiction
/// check that calls this function (or a HS-side equivalent) and dumps
/// the cycle path.  Diffing HS's path against RS's less_atom set
/// identifies the missing edge immediately.
///
/// Returns the cycle as a `Vec<NodeId>` where the first and last
/// entries are equal (the back-edge node).  Empty if no cycle.
pub fn cyclic_with_path(less: &[LessAtom]) -> Vec<NodeId> {
    let mut adj: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for l in less {
        adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
    }
    let mut color: BTreeMap<NodeId, u8> = BTreeMap::new();
    let mut path: Vec<NodeId> = Vec::new();
    let nodes: Vec<NodeId> = adj.keys().cloned().collect();
    fn dfs(
        node: &NodeId,
        adj: &BTreeMap<NodeId, Vec<NodeId>>,
        color: &mut BTreeMap<NodeId, u8>,
        path: &mut Vec<NodeId>,
    ) -> Option<NodeId> {
        match color.get(node).copied().unwrap_or(0) {
            1 => return Some(node.clone()),   // back-edge target
            2 => return None,
            _ => {}
        }
        color.insert(node.clone(), 1);
        path.push(node.clone());
        if let Some(succs) = adj.get(node) {
            for s in succs {
                if let Some(target) = dfs(s, adj, color, path) {
                    return Some(target);
                }
            }
        }
        color.insert(node.clone(), 2);
        path.pop();
        None
    }
    for n in &nodes {
        if let Some(target) = dfs(n, &adj, &mut color, &mut path) {
            // Truncate path to the cycle (from `target` onwards).
            if let Some(start) = path.iter().position(|x| x == &target) {
                let mut cycle: Vec<NodeId> = path[start..].to_vec();
                cycle.push(target);
                return cycle;
            }
        }
    }
    Vec::new()
}

/// Detect any node that is strictly after `last(_)`. Mirrors Haskell's
/// `nodesAfterLast`.
///
/// Walks BOTH `less_atoms` AND `edges` to build the < relation.  Each
/// edge `(src, _) → (tgt, _)` induces `src < tgt` (the producer must
/// fire before the consumer).  Without including edges, a `last_atom`
/// at a node that has chain successors via edges (but no explicit
/// `LessAtom`) would survive — losing the contradiction Haskell uses
/// to prune typing-class source cases at precompute.
fn node_after_last(sys: &System) -> Vec<Contradiction> {
    let last = match &sys.last_atom { Some(l) => l.clone(), None => return Vec::new() };
    // Port of Haskell `Theory.Constraint.Solver.Contradictions.nodesAfterLast`:
    //
    //   nodesAfterLast sys = case sLastAtom sys of
    //     Just i  -> [(i,j) | j ∈ reachableSet [i] (rawLessRel sys)
    //                       , j /= i, isInTrace sys j ]
    //
    // where `rawLessRel = lessAtoms ∪ rawEdgeRel` and
    // `isInTrace sys i = i ∈ sNodes ∨ isLast sys i ∨
    //                    any ((i ==) . fst) (unsolvedActionAtoms sys)`.
    //
    // Walk BOTH less_atoms AND edges (rawLessRel) — without edges,
    // the typing-case `Last(#vr_inner)` branch never contradicts even
    // when `vr_inner` has a chain-edge successor that pins down the
    // ordering.  Filter by `isInTrace`: a successor only counts if
    // it's a rule instance in `sNodes`, the system's last, or carries
    // an unsolved Action goal — otherwise abstract precompute-time
    // node-ids spuriously trip the contradiction.
    let mut adj: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for l in &sys.less_atoms {
        adj.entry(l.smaller.clone()).or_default().push(l.larger.clone());
    }
    for e in &sys.edges {
        adj.entry(e.src.0.clone()).or_default().push(e.tgt.0.clone());
    }
    // isInTrace: collect every node-id that is "in the trace".
    let mut in_trace: BTreeSet<NodeId> = BTreeSet::new();
    for (id, _) in &sys.nodes {
        in_trace.insert(id.clone());
    }
    in_trace.insert(last.clone()); // isLast is true for `last`
    for (g, st) in &sys.goals {
        if st.solved { continue; }
        if let crate::constraint::constraints::Goal::Action(id, _) = g {
            in_trace.insert(id.clone());
        }
    }
    let mut visited: BTreeSet<NodeId> = BTreeSet::new();
    let mut stack = vec![last.clone()];
    while let Some(n) = stack.pop() {
        if !visited.insert(n.clone()) { continue; }
        if let Some(s) = adj.get(&n) {
            for x in s { stack.push(x.clone()); }
        }
    }
    visited.remove(&last);
    visited.into_iter()
        .filter(|n| in_trace.contains(n))
        .map(|after| Contradiction::NodeAfterLast(last.clone(), after))
        .collect()
}

/// `maybeNonNormalTerms`: walk all node facts + new_vars in `sys`,
/// returning every subterm that could be non-normal under some
/// substitution.  Used by `subst_creates_non_normal_terms` below.
/// Mirrors Haskell's `Contradictions.maybeNonNormalTerms`
/// (Contradictions.hs:170-175).
pub fn maybe_non_normal_terms(
    sys: &System,
    irreducible: &tamarin_term::function_symbols::FunSig,
) -> Vec<tamarin_term::lterm::LNTerm> {
    let mut candidates: std::collections::BTreeSet<tamarin_term::lterm::LNTerm>
        = std::collections::BTreeSet::new();
    for (_, rule) in &sys.nodes {
        for f in rule.premises.iter().chain(&rule.conclusions).chain(&rule.actions) {
            for t in &f.terms {
                maybe_not_nf_subterms(irreducible, t, &mut candidates);
            }
        }
        for t in &rule.new_vars {
            maybe_not_nf_subterms(irreducible, t, &mut candidates);
        }
    }
    candidates.into_iter().collect()
}

/// `substCreatesNonNormalTerms`: returns `true` if applying
/// `vfresh_subst` to the system's `maybe-non-normal` terms (already
/// substituted by `fsubst`) creates a non-normal-form term.  Used by
/// `simp_minimize` to filter SplitG variants that would violate the
/// nf-respecting trace semantics.  Mirrors Haskell's
/// `Contradictions.substCreatesNonNormalTerms` (Contradictions.hs:177-184):
///
/// ```haskell
/// substCreatesNonNormalTerms hnd sys fsubst =
///     \subst -> any (not . nfApply subst) terms
///   where terms = apply fsubst $ maybeNonNormalTerms hnd sys
///         nfApply subst0 t = t == t' || nf' t' `runReader` hnd
///           where tvars = freesList t
///                 subst = restrictVFresh tvars subst0
///                 t'    = apply (freshToFreeAvoidingFast subst tvars) t
/// ```
pub fn subst_creates_non_normal_terms(
    maude: &tamarin_term::maude_proc::MaudeHandle,
    sys: &System,
    fsubst: &crate::tools::equation_store::LNSubst,
    vfresh_subst: &crate::tools::equation_store::LNSubstVFresh,
) -> bool {
    use tamarin_term::subst::apply_vterm;
    use tamarin_term::vterm::vars_vterm;
    let sig = maude.maude_sig();
    let irreducible = &sig.irreducible_fun_syms;
    // Apply fsubst once upfront.
    let terms: Vec<tamarin_term::lterm::LNTerm> = maybe_non_normal_terms(sys, irreducible)
        .into_iter()
        .map(|t| apply_vterm(fsubst, t))
        .collect();
    for t in &terms {
        let tvars: Vec<tamarin_term::lterm::LVar> = vars_vterm(t);
        if tvars.is_empty() { continue; }
        let restricted = vfresh_subst.restrict(&tvars);
        if restricted.dom().count() == 0 { continue; }
        // Build a free subst from the restricted VFresh, allocating
        // fresh idxs above the rest of the system.
        let free_subst = restricted.fresh_to_free(|n| maude.reserve_idxs(n));
        let t_prime = apply_vterm(&free_subst, t.clone());
        // Fast path: if subst doesn't change the term, it's still NF.
        if &t_prime == t { continue; }
        // Slow path: structural NF check (HS-faithful).  Mirrors HS
        // `nfApply subst0 t = t == t' || nf' t' \`runReader\` hnd`
        // where `nf' = nfViaHaskell` (Norm.hs:130-131).  This is a
        // PURE structural check, NOT `maude.reduce(t) == t`.  The
        // distinction matters because Maude canonicalises AC operator
        // arguments (multiset / mult / xor / nat-plus), so
        // `mult(tid, x)` and `mult(x, tid)` are different `Eq`
        // representations but both in NF.  The previous Rust check
        // `match maude.reduce(&t_prime) { Ok(t_red) if t_red == t_prime
        // => continue, _ => return true }` reported `creates non-normal`
        // for AC-reordered arms, over-filtering `simpMinimize` and
        // dropping legitimate `solve_term_eqs` cases in DH protocols
        // (JKL_TS2_2004{,_KI_wPFS} key-secrecy lemmas).
        let is_nf = tamarin_term::norm::nf_via_haskell(maude, &t_prime);
        if !is_nf {
            if std::env::var("TAM_RS_DBG_SUBST_NF").is_ok() {
                eprintln!("[rs-subst-nf] CREATES t={:?} t_prime={:?}", t, t_prime);
            }
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::constraints::Reason;
    use tamarin_term::lterm::{LSort, LVar};

    fn n(name: &str) -> NodeId { LVar::new(name, LSort::Node, 0) }

    #[test]
    fn empty_system_has_no_contradictions() {
        let sig = crate::signature::SignaturePure::empty(false);
        // Without a real Maude we shouldn't run contradictions(); but
        // we can call cyclic directly.
        assert!(!cyclic(&[]));
        let _ = sig;
    }

    #[test]
    fn cycle_detected() {
        let l = vec![
            LessAtom::new(n("a"), n("b"), Reason::Fresh),
            LessAtom::new(n("b"), n("c"), Reason::Fresh),
            LessAtom::new(n("c"), n("a"), Reason::Fresh),
        ];
        assert!(cyclic(&l));
    }

    #[test]
    fn no_cycle_detected() {
        let l = vec![
            LessAtom::new(n("a"), n("b"), Reason::Fresh),
            LessAtom::new(n("b"), n("c"), Reason::Fresh),
        ];
        assert!(!cyclic(&l));
    }

    /// `nonInjectiveFactInstances` direct port: feed in a system with
    /// an Init→Stop edge for an injective fact `Inj` and a Copy node
    /// reachable from Init that also produces/consumes Inj with the
    /// same first arg, then check we see exactly one
    /// `NonInjectiveFactInstance(i, j, k)` triple.
    #[test]
    fn non_injective_fact_witness_emitted() {
        use crate::constraint::constraints::{Edge, LessAtom, Reason};
        use crate::constraint::system::System;
        use crate::fact::{Fact, FactTag, Multiplicity};
        use crate::rule::{
    Rule, ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes,
    RuleInfo, IntrRuleACInfo, RuleACInst, ConcIdx, PremIdx,
};
        use tamarin_term::builtin::msg_var;
        use tamarin_term::maude_proc::MaudeHandle;

        // Build the rule instances.
        let inj_tag = FactTag::Proto(Multiplicity::Linear, "Inj".to_string(), 1);
        let inj_fact = Fact::new(inj_tag.clone(), vec![msg_var("x", 0)]);

        let init: RuleACInst = Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Init".into()),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![],
            vec![inj_fact.clone()],
            vec![],
        );
        let copy: RuleACInst = Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Copy".into()),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![inj_fact.clone()],
            vec![inj_fact.clone()],
            vec![],
        );
        let stop: RuleACInst = Rule::new(
            RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                name: ProtoRuleName::Stand("Stop".into()),
                attributes: RuleAttributes::empty(),
                loop_breakers: Vec::new(),
            }),
            vec![inj_fact.clone()],
            vec![],
            vec![],
        );

        // Construct a system: i = #1 (Init) → k = #2 (Stop) directly,
        // with j = #3 (Copy) reachable from i and k from j.
        let i = n("1");
        let j = n("3");
        let k = n("2");
        let mut sys = System::empty();
        sys.add_node(i.clone(), init);
        sys.add_node(j.clone(), copy);
        sys.add_node(k.clone(), stop);
        // i → k edge (Inj fact).
        sys.add_edge(Edge {
            src: (i.clone(), ConcIdx(0)),
            tgt: (k.clone(), PremIdx(0)),
        });
        // i < j, j < k via less atoms.
        sys.add_less(LessAtom::new(i.clone(), j.clone(), Reason::Adversary));
        sys.add_less(LessAtom::new(j.clone(), k.clone(), Reason::Adversary));

        // Build the proof context that knows `Inj` is injective.
        fn maude_path() -> Option<String> {
            if let Ok(p) = std::env::var("MAUDE_PATH") { return Some(p); }
            for c in ["/home/linuxbrew/.linuxbrew/bin/maude", "/usr/local/bin/maude", "maude"] {
                if std::path::Path::new(c).exists() { return Some(c.to_string()); }
            }
            None
        }
        let mp = match maude_path() { Some(p) => p, None => return };
        let h = MaudeHandle::start(&mp, tamarin_term::maude_sig::pair_maude_sig()).unwrap();
        let mut ctx = ProofContext::new(h, Vec::new());
        ctx.injective_fact_insts = vec![(inj_tag.clone(), Vec::new())];

        let cs = contradictions(&ctx, &sys);
        let injs: Vec<_> = cs.iter().filter(|c| matches!(c,
            Contradiction::NonInjectiveFactInstance(_, _, _))).collect();
        assert!(!injs.is_empty(),
            "expected at least one NonInjectiveFactInstance contradiction; got {:?}", cs);
    }

    /// Two LVars sharing `(name, idx)` but with disjoint sub-sorts
    /// (Pub vs Fresh) must be flagged.  This is the soundness fix for
    /// the NSLPK3-class false positives — see solver-memory bug #26.
    #[test]
    fn sort_conflated_pub_vs_fresh_detected() {
        use crate::constraint::system::System;
        use crate::fact::{Fact, FactTag, Multiplicity};
        use crate::rule::{
            Rule, ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes,
            RuleInfo, IntrRuleACInfo, RuleACInst,
        };

        // Build a system with two nodes, each containing an action
        // using "x" at idx 58 but with conflicting sorts: Pub vs Fresh.
        let pub_var = LVar::new("x", LSort::Pub, 58);
        let fresh_var = LVar::new("x", LSort::Fresh, 58);
        let tag = FactTag::Proto(Multiplicity::Linear, "X".to_string(), 1);
        let pub_term = tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(pub_var.clone()));
        let fresh_term = tamarin_term::term::Term::Lit(
            tamarin_term::vterm::Lit::Var(fresh_var.clone()));
        let mk_rule = |name: &str, t| -> RuleACInst {
            Rule::new(
                RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(name.into()),
                    attributes: RuleAttributes::empty(),
                    loop_breakers: Vec::new(),
                }),
                vec![],
                vec![Fact::new(tag.clone(), vec![t])],
                vec![],
            )
        };
        let mut sys = System::empty();
        sys.add_node(LVar::new("i", LSort::Node, 1), mk_rule("R_pub", pub_term));
        sys.add_node(LVar::new("j", LSort::Node, 2), mk_rule("R_fresh", fresh_term));
        assert!(has_sort_conflated_lvars(&sys),
            "expected sort-conflict between ~mw:Pub 58 and ~mw:Fresh 58");
    }

    /// Pub vs Msg should NOT be flagged — Msg is the join sort and
    /// Pub ⊂ Msg, so the pair can be narrowed at unification time.
    #[test]
    fn sort_conflated_pub_vs_msg_not_flagged() {
        use crate::constraint::system::System;
        use crate::fact::{Fact, FactTag, Multiplicity};
        use crate::rule::{
            Rule, ProtoRuleACInstInfo, ProtoRuleName, RuleAttributes,
            RuleInfo, IntrRuleACInfo, RuleACInst,
        };
        let pub_var = LVar::new("x", LSort::Pub, 58);
        let msg_var = LVar::new("x", LSort::Msg, 58);
        let tag = FactTag::Proto(Multiplicity::Linear, "X".to_string(), 1);
        let mk = |name: &str, t| -> RuleACInst {
            Rule::new(
                RuleInfo::<ProtoRuleACInstInfo, IntrRuleACInfo>::Proto(ProtoRuleACInstInfo {
                    name: ProtoRuleName::Stand(name.into()),
                    attributes: RuleAttributes::empty(),
                    loop_breakers: Vec::new(),
                }),
                vec![], vec![Fact::new(tag.clone(), vec![t])], vec![],
            )
        };
        let mut sys = System::empty();
        sys.add_node(LVar::new("i", LSort::Node, 1),
            mk("R_p", tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(pub_var))));
        sys.add_node(LVar::new("j", LSort::Node, 2),
            mk("R_m", tamarin_term::term::Term::Lit(
                tamarin_term::vterm::Lit::Var(msg_var))));
        assert!(!has_sort_conflated_lvars(&sys),
            "Pub vs Msg should NOT be flagged (Msg is join sort)");
    }
}
