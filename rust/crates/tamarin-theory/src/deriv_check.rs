//! Dynamic message-derivation check.
//!
//! Mirrors HS's `Theory.Tools.MessageDerivationChecks.checkVariableDeducability`
//! (lib/theory/src/Theory/Tools/MessageDerivationChecks.hs:35-50).  For each
//! protocol rule, asks the prover: "given that the intruder has access to all
//! of this rule's premise terms, can it derive each of the rule's free
//! variables?"  When a variable IS bound by some premise fact but cannot
//! actually be derived by the intruder (because the fact's containing rule
//! is unreachable / requires private knowledge), HS flags it as an
//! "unintended pattern match".
//!
//! How HS does it (verbatim — see `MessageDerivationChecks.hs:35-50,181-188`):
//!
//!   For each rule R indexed by idx:
//!     1. Drop ALL rules/lemmas/restrictions from the theory.
//!     2. `makeFunsPublic`: rewrite every private NoEq fun-sym to public,
//!        because the synthetic rule emits Out facts and the intruder must
//!        be able to apply destructors.
//!     3. Add a single generated rule:
//!          rule Generated_<idx>:
//!            [ Fr(~v1), Fr(~v2), ... ]                  // each free var of R
//!            --[ Generated_<idx>(v1, v2, ...) ]->        // sole action
//!            [ Out(t1), Out(t2), ... ]                   // R's premise terms
//!     4. Add one exists-trace lemma per free var v.  HS's `landFormula`
//!        gives each conjunct its OWN timepoint via `zip [0..]`, and the
//!        intruder-knowledge predicate is `KU` (`lntermToKUFact = kuFact`):
//!          lemma deriv_v: exists-trace
//!            "Ex v1 v2 ... #t0 #t1. Generated_<idx>(v1, v2, ...) @ #t0 & KU(v) @ #t1"
//!     5. Run the prover on each lemma with `--derivcheck-timeout`.
//!     6. Lemmas whose proof did NOT find a trace identify non-derivable
//!        variables — report them.
//!
//! Note: `prove_probe` builds the `ProofContext` + runs `ensure_saturated()`
//! ONCE per probe and then iterates the per-variable lemmas reusing that
//! shared, already-saturated context, so a rule with N free vars incurs N
//! proof attempts but only one context build.  Each attempt is bounded by
//! the user's timeout (default 5s, mirrored on the HS side).  The check is
//! gated by `args.derivcheck_timeout`; passing `0` disables it entirely (HS:
//! `Main.TheoryLoader.hs`).

use std::time::Duration;
use tamarin_parser::ast as p;
use tamarin_parser::wf::WfError;
use tamarin_term::maude_proc::MaudeHandle;

/// Run HS's per-variable derivability check on every rule.
///
/// `timeout_secs == 0` disables the check (returns `vec![]`).  Otherwise
/// each per-variable prove call is bounded by `timeout_secs` of wall-clock
/// time (mirrors HS's `--derivcheck-timeout`).
pub fn check_message_derivation(
    parsed: &p::Theory,
    maude: &MaudeHandle,
    timeout_secs: u32,
) -> Vec<WfError> {
    if timeout_secs == 0 { return Vec::new(); }
    let timeout = Duration::from_secs(timeout_secs as u64);
    let dbg = std::env::var_os("TAM_DBG_DERIV_CHECK").is_some();
    // TAM_DBG_DERIV_TIMING=1: emit per-rule / per-variable wall-clock
    // timings on stderr.  Off-path when env var is absent.
    let dbg_timing = std::env::var_os("TAM_DBG_DERIV_TIMING").is_some();
    let t_total_start = std::time::Instant::now();

    // Collect the names that should NOT be treated as variables:
    //  * `functions: <name>/0` — user-declared 0-arity functions.
    //  * Builtin 0-arity constants (signing's `true`, DH's `1`, etc.).
    // HS-faithful: HS resolves these via `nullaryApp` at parse-time
    // (lib/theory/src/Theory/Text/Parser/Term.hs::nullaryApp); RS
    // does the same resolution at elaborate-time, but the deriv-check
    // walks the un-elaborated parser AST so it needs an explicit
    // deny-list.  See `MessageDerivationChecks.hs:39` (HS uses
    // `originalRules = map (applyMacroInProtoRule ...)`).
    let nullary_funs = collect_all_nullary_fun_names(parsed);

    let mut per_rule: Vec<(String, Vec<String>)> = Vec::new();
    let mut rule_count = 0usize;
    let mut var_count = 0usize;
    let mut total_synth = Duration::ZERO;
    let mut total_prove = Duration::ZERO;
    for (idx, raw_rule) in protocol_rules(parsed).enumerate() {
        if raw_rule.attributes.iter().any(|a| matches!(a, p::RuleAttr::NoDerivCheck)) {
            continue;
        }
        // HS applies macros (which include let-bindings) before the
        // deriv check (MessageDerivationChecks.hs:39 -- `originalRules
        // = map (applyMacroInProtoRule (theoryMacros thy)) $
        // theoryRules thy`).  Mirror that here: substitute let-bound
        // names so we walk the same shape HS does.  Without this, RS
        // flags every let-bound name (`pkB`, `mtr`, `ci2`, ...) as
        // non-derivable.
        let expanded = crate::elaborate::apply_let_block(raw_rule);
        let rule = &expanded;
        let free_vars = collect_rule_free_vars(rule, &nullary_funs);
        if free_vars.is_empty() { continue; }
        rule_count += 1;

        // Build the probe theory ONCE per rule (it contains all the
        // per-variable lemmas).  The synthesised theory is small —
        // one rule, N lemmas, the original signature.
        let t_synth = std::time::Instant::now();
        let probe = synthesise_probe_theory(parsed, rule, idx, &free_vars);
        let synth_dt = t_synth.elapsed();
        total_synth += synth_dt;
        if dbg {
            eprintln!("[deriv] rule={} free_vars={:?}", rule.name,
                free_vars.iter().map(|v| &v.name).collect::<Vec<_>>());
            eprintln!("[deriv] probe theory items:");
            for it in &probe.items {
                match it {
                    p::TheoryItem::Rule(r) => eprintln!("  rule {}: prem={} act={} conc={}",
                        r.name, r.premises.len(), r.actions.len(), r.conclusions.len()),
                    p::TheoryItem::Lemma(l) => eprintln!("  lemma {} ({:?})",
                        l.name, l.trace_quantifier),
                    _ => {}
                }
            }
        }

        // Try each variable's lemma.  HS's "TraceFound" status maps
        // to RS's `NodeStatus::Solved` for exists-trace lemmas.
        //
        // HS-faithful structure: `closeTheoryWithMaude` is called ONCE
        // per probe theory (HS `MessageDerivationChecks.hs:40-44`
        // calls `closeTheoryWithMaude` once per modified theory; then
        // `proveTheory` walks the N lemmas reusing the closed theory's
        // sources/cache — `Prover.hs:260-279`).  Build the
        // `ProofContext` + run `ensure_saturated()` ONCE per probe,
        // then iterate the per-variable lemmas reusing it.  Previously
        // each `prove_lemma` call rebuilt the context and re-saturated;
        // on wireguard's bigger probes that was ~80% of the deriv-check
        // wall-clock.
        let undecidable = match prove_probe(&probe, maude.clone(), idx, &free_vars, timeout, dbg_timing, &rule.name, &mut total_prove, &mut var_count) {
            Some(u) => u,
            None => continue,
        };
        if dbg_timing {
            eprintln!(
                "[deriv-timing] rule={} synth={:.3}s nvars={} total_prove={:.3}s",
                rule.name, synth_dt.as_secs_f64(), free_vars.len(),
                total_prove.as_secs_f64(),
            );
        }
        if !undecidable.is_empty() {
            per_rule.push((rule.name.clone(), undecidable));
        }
    }
    if dbg_timing {
        eprintln!(
            "[deriv-timing] TOTAL rules={} vars={} synth={:.3}s prove={:.3}s wall={:.3}s",
            rule_count, var_count,
            total_synth.as_secs_f64(),
            total_prove.as_secs_f64(),
            t_total_start.elapsed().as_secs_f64(),
        );
    }
    format_deriv_report(&per_rule)
}

/// Iterate over Rule items in declaration order.  Skips IntrRule
/// declarations (intruder rules), Restrictions, Lemmas.
fn protocol_rules(thy: &p::Theory) -> impl Iterator<Item = &p::Rule> {
    thy.items.iter().filter_map(|it| match it {
        p::TheoryItem::Rule(r) => Some(r),
        _ => None,
    })
}

/// HS-faithful counterpart to `nullaryApp` (parser-state-driven
/// 0-arity function-symbol lookup, `Theory/Text/Parser/Term.hs`).
/// Combines (a) user-declared `functions: name/0` and (b) the 0-arity
/// constants any enabled `builtins:` declaration brings in (signing's
/// `true`, DH's `1`, etc.).
fn collect_all_nullary_fun_names(thy: &p::Theory) -> std::collections::BTreeSet<String> {
    let mut out: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for it in &thy.items {
        match it {
            p::TheoryItem::Functions(decls) => {
                for d in decls {
                    if d.arg_types.is_empty() {
                        out.insert(d.name.clone());
                    }
                }
            }
            p::TheoryItem::Builtins(names) => {
                for n in names {
                    for c in crate::elaborate::builtin_nullary_constants(n) {
                        out.insert(c);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// All variables that appear anywhere in a rule's premise / action /
/// conclusion terms, in first-occurrence order, deduped, EXCLUDING:
///   - `Pub`-sort vars (`$x`) — HS's `deleteGlobals` drops these:
///     they are adversary-known by definition.
///   - `Node`-sort vars (`#i`) — timepoints, not message vars.
///   - Suffix-sorted vars whose underlying sort is Pub or Node, for the
///     same reason.
///   - Names that are actually 0-arity function calls (e.g. user-
///     declared `true/0`, builtin `1`).  HS-faithful: `nullaryApp`
///     resolves these to `App` not `Var` at parse-time.
fn collect_rule_free_vars(
    r: &p::Rule,
    nullary_funs: &std::collections::BTreeSet<String>,
) -> Vec<p::VarSpec> {
    let mut out: Vec<p::VarSpec> = Vec::new();
    let mut seen: std::collections::BTreeSet<(String, u64)> = std::collections::BTreeSet::new();
    let push = |v: &p::VarSpec, out: &mut Vec<p::VarSpec>, seen: &mut std::collections::BTreeSet<_>| {
        if matches!(v.sort, p::SortHint::Pub | p::SortHint::Node) {
            return;
        }
        if matches!(v.sort, p::SortHint::Suffix(p::SuffixSort::Pub)
            | p::SortHint::Suffix(p::SuffixSort::Node))
        {
            return;
        }
        if nullary_funs.contains(&v.name) {
            return;
        }
        let key = (v.name.clone(), v.idx);
        if seen.insert(key) {
            out.push(v.clone());
        }
    };
    let visit_term = |t: &p::Term, out: &mut Vec<p::VarSpec>, seen: &mut _| {
        let mut vs = Vec::new();
        collect_term_vars(t, &mut vs);
        for v in vs { push(&v, out, seen); }
    };
    for f in &r.premises { for a in &f.args { visit_term(a, &mut out, &mut seen); } }
    for f in &r.actions { for a in &f.args { visit_term(a, &mut out, &mut seen); } }
    for f in &r.conclusions { for a in &f.args { visit_term(a, &mut out, &mut seen); } }
    // HS-faithful: sort by (idx, sort, name) to match HS's `LVar Ord`
    // (LTerm.hs:522-524: `compare x3 y3 <> compare x2 y2 <> compare x1 y1`
    //  where x3=idx, x2=sort, x1=name).  HS uses `frees . L.get oprRuleE` →
    // `S.toList` which returns elements in ascending LVar Ord.
    fn sort_hint_ord(s: &p::SortHint) -> u8 {
        // mirrors HS LSort derived-Ord: Pub=0, Fresh=1, Msg=2, Node=3, Nat=4
        match s {
            p::SortHint::Pub => 0,
            p::SortHint::Fresh => 1,
            p::SortHint::Msg => 2,
            p::SortHint::Node => 3,
            p::SortHint::Nat => 4,
            p::SortHint::Suffix(p::SuffixSort::Pub) => 0,
            p::SortHint::Suffix(p::SuffixSort::Fresh) => 1,
            p::SortHint::Suffix(p::SuffixSort::Msg) => 2,
            p::SortHint::Suffix(p::SuffixSort::Node) => 3,
            p::SortHint::Suffix(p::SuffixSort::Nat) => 4,
            p::SortHint::Untagged => 2, // untagged → Msg by default
        }
    }
    out.sort_by(|a, b| {
        a.idx.cmp(&b.idx)
            .then_with(|| sort_hint_ord(&a.sort).cmp(&sort_hint_ord(&b.sort)))
            .then_with(|| a.name.cmp(&b.name))
    });
    out
}

/// Apply a (name,idx) → VarSpec rename map to all variables in a term.
fn rename_term_vars(
    t: &p::Term,
    map: &std::collections::HashMap<(String, u64), p::VarSpec>,
) -> p::Term {
    match t {
        p::Term::Var(v) => {
            if let Some(new) = map.get(&(v.name.clone(), v.idx)) {
                p::Term::Var(new.clone())
            } else {
                t.clone()
            }
        }
        p::Term::App(name, args) => p::Term::App(
            name.clone(),
            args.iter().map(|a| rename_term_vars(a, map)).collect(),
        ),
        p::Term::Pair(args) => p::Term::Pair(
            args.iter().map(|a| rename_term_vars(a, map)).collect(),
        ),
        p::Term::BinOp(op, l, r) => p::Term::BinOp(
            *op,
            Box::new(rename_term_vars(l, map)),
            Box::new(rename_term_vars(r, map)),
        ),
        p::Term::AlgApp(name, l, r) => p::Term::AlgApp(
            name.clone(),
            Box::new(rename_term_vars(l, map)),
            Box::new(rename_term_vars(r, map)),
        ),
        _ => t.clone(),
    }
}

fn collect_term_vars(t: &p::Term, out: &mut Vec<p::VarSpec>) {
    match t {
        p::Term::Var(v) => out.push(v.clone()),
        p::Term::App(_, args) | p::Term::Pair(args) => {
            for a in args { collect_term_vars(a, out); }
        }
        p::Term::BinOp(_, l, rt) => { collect_term_vars(l, out); collect_term_vars(rt, out); }
        p::Term::AlgApp(_, l, rt) => { collect_term_vars(l, out); collect_term_vars(rt, out); }
        _ => {}
    }
}

/// Build the per-rule probe theory:
///
///   theory Probe_<idx>
///     <copy of original signature: builtins, functions, equations, macros>
///
///     rule Probe_<idx>:
///       [ Fr(~v) for each free Fresh-sort var ]
///       --[ Generated_<idx>(v1, v2, ...) ]->
///       [ Out(t) for each premise term in R ]
///
///     lemma deriv_check_<idx>_<v>: exists-trace
///       "Ex v1 v2 ... #t0 #t1. Generated_<idx>(...) @ #t0 & KU(v) @ #t1"
///     ...one per free var...  (two distinct timepoints; the knowledge
///     predicate is `KU`, not `K` — consistent with the module header
///     and the inline comment in the body.)
fn synthesise_probe_theory(
    src: &p::Theory,
    rule: &p::Rule,
    idx: usize,
    free_vars: &[p::VarSpec],
) -> p::Theory {
    let mut probe = p::Theory {
        is_diff: false,
        name: format!("Probe_{}", idx),
        configuration: None,
        items: Vec::new(),
    };
    // Carry over the signature items.  Drops rules/lemmas/restrictions.
    for it in &src.items {
        match it {
            p::TheoryItem::Builtins(_)
            | p::TheoryItem::Functions(_)
            | p::TheoryItem::Equations { .. }
            | p::TheoryItem::Macros(_) => {
                probe.items.push(it.clone());
            }
            _ => {}
        }
    }
    // Rename ALL free vars to Fresh sort throughout the rule (mirrors
    // HS's `freesToFresh` + the implicit retyping the synthetic rule
    // needs to be wf — Fr( ) only accepts Fresh- or Msg-sorted args).
    // We use Fresh so the resulting var IS a fresh-sourced nonce the
    // intruder learns from Out, not a Msg-sort var.  The rename is
    // applied consistently to (a) the new Fr( ) premises, (b) the
    // action's args, (c) the Out( ) conclusions, AND (d) the lemma's
    // existential quantifier and KU goal.
    let rename: std::collections::HashMap<(String, u64), p::VarSpec> = free_vars.iter()
        .map(|v| {
            let mut vf = v.clone();
            vf.sort = p::SortHint::Fresh;
            ((v.name.clone(), v.idx), vf)
        })
        .collect();
    let renamed_free_vars: Vec<p::VarSpec> = free_vars.iter()
        .map(|v| rename[&(v.name.clone(), v.idx)].clone())
        .collect();
    let fresh_premises: Vec<p::Fact> = renamed_free_vars.iter()
        .map(|v| p::Fact {
            persistent: false,
            name: "Fr".into(),
            args: vec![p::Term::Var(v.clone())],
            annotations: Vec::new(),
        })
        .collect();
    let action = p::Fact {
        persistent: false,
        name: format!("Generated_{}", idx),
        args: renamed_free_vars.iter().map(|v| p::Term::Var(v.clone())).collect(),
        annotations: Vec::new(),
    };
    let out_concs: Vec<p::Fact> = rule.premises.iter()
        .flat_map(|f| f.args.iter().cloned())
        .map(|t| p::Fact {
            persistent: false,
            name: "Out".into(),
            args: vec![rename_term_vars(&t, &rename)],
            annotations: Vec::new(),
        })
        .collect();
    let probe_rule = p::Rule {
        name: format!("Probe_{}", idx),
        modulo: None,
        attributes: Vec::new(),
        let_block: Vec::new(),
        premises: fresh_premises,
        actions: vec![action.clone()],
        conclusions: out_concs,
        embedded_restrictions: Vec::new(),
        variants: Vec::new(),
        left_right: None,
    };
    probe.items.push(p::TheoryItem::Rule(probe_rule));

    // Build one lemma per free var.  HS's `landFormula` gives each
    // conjoined fact its OWN timepoint (MessageDerivationChecks.hs:202-203):
    //   `Generated_<idx>(...) @ #t0  ∧  KU(v) @ #t1`
    // Two DIFFERENT timepoints — asking "is there ever a time the
    // intruder knows v AND a (possibly different) time Generated fires?"
    // not "are these simultaneous".  The intruder-knowledge predicate
    // is `KU` (HS's `lntermToKUFact = kuFact`), not `K`.
    let action_atom = |action: p::Fact, t: p::Term| -> p::Formula {
        p::Formula::Atom(p::Atom::Action(action, t))
    };
    for v in free_vars {
        let lemma_name = format!("deriv_check_{}_{}", idx, v.name);
        let v_renamed = rename[&(v.name.clone(), v.idx)].clone();
        let t0 = p::VarSpec { name: "t0".into(), idx: 0, sort: p::SortHint::Node, typ: None };
        let t1 = p::VarSpec { name: "t1".into(), idx: 0, sort: p::SortHint::Node, typ: None };
        let gen_at = action_atom(action.clone(), p::Term::Var(t0.clone()));
        let ku_fact = p::Fact {
            // KU is Persistent per factTagMultiplicity (Model/Fact.hs:358);
            // keep the "for special names, persistent == tag multiplicity"
            // invariant so GFact equality with parsed KU facts is faithful.
            persistent: true,
            name: "KU".into(),
            args: vec![p::Term::Var(v_renamed)],
            annotations: Vec::new(),
        };
        let ku_at = action_atom(ku_fact, p::Term::Var(t1.clone()));
        let conj = p::Formula::And(Box::new(gen_at), Box::new(ku_at));
        // Ex t0 t1 vars... . <conj>
        let mut all_quant = renamed_free_vars.clone();
        all_quant.push(t0);
        all_quant.push(t1);
        let body = p::Formula::Exists(all_quant, Box::new(conj));
        probe.items.push(p::TheoryItem::Lemma(p::Lemma {
            name: lemma_name,
            modulo: None,
            attributes: Vec::new(),
            trace_quantifier: p::TraceQuantifier::ExistsTrace,
            formula: body,
            proof: None,
        }));
    }

    probe
}

/// HS-faithful per-probe prover.  Builds the elaborated probe theory
/// and a single `ProofContext` (with one `ensure_saturated` call),
/// then iterates the per-variable lemmas, invoking `run_proof_search`
/// directly on each lemma's `System` with the shared, already-saturated
/// context.
///
/// Mirrors HS's `closeTheoryWithMaude` (called once per modified theory
/// in `MessageDerivationChecks.hs:40-44`) followed by `proveTheory`'s
/// per-lemma walk (`Prover.hs:260-279`).  Returns `None` on elaboration
/// failure (caller continues to the next probe rule); otherwise returns
/// the list of variable names whose lemma did NOT find a trace
/// (= non-derivable variables).
fn prove_probe(
    probe: &p::Theory,
    maude: MaudeHandle,
    idx: usize,
    free_vars: &[p::VarSpec],
    timeout: Duration,
    dbg_timing: bool,
    rule_name: &str,
    total_prove: &mut Duration,
    var_count: &mut usize,
) -> Option<Vec<String>> {
    use crate::constraint::solver::context::ProofContext;
    use crate::constraint::solver::search::{run_proof_search, NodeStatus};
    use crate::constraint::system::{formula_to_system, SourceKind};
    use crate::elaborate::elaborate;
    use crate::guarded::formula_to_guarded;
    use crate::theory::OpenProtoRule;

    // Per-prove deadline gate: set TAM_PROVE_DEADLINE_MS from `timeout`
    // so each variable's `run_proof_search` still honours the deadline.
    let prev_deadline = std::env::var("TAM_PROVE_DEADLINE_MS").ok();
    let ms = (timeout.as_millis() as u64).max(1);
    std::env::set_var("TAM_PROVE_DEADLINE_MS", ms.to_string());

    let _user_funs_guard = crate::elaborate::set_user_funs_for_theory(probe);
    let elaborated = match elaborate(probe) {
        Ok(t) => t,
        Err(_) => {
            // Restore deadline before bailing.
            match prev_deadline {
                Some(v) => std::env::set_var("TAM_PROVE_DEADLINE_MS", v),
                None => std::env::remove_var("TAM_PROVE_DEADLINE_MS"),
            }
            return None;
        }
    };
    let rules: Vec<OpenProtoRule> = elaborated.rules().cloned().collect();
    let mut ctx = ProofContext::new_with_restrictions(maude, rules, Vec::new());
    ctx.is_exists_trace = true;
    // Probes have no `[sources]`-tagged lemmas, so no typing
    // assumptions — but `ensure_saturated()` still must run to compute
    // the source-case cache exactly as HS's `closeTheoryWithMaude`
    // does once per modified theory (Prover.hs:170-251).
    ctx.ensure_saturated();

    let mut undecidable = Vec::new();
    for v in free_vars {
        let lemma_name = format!("deriv_check_{}_{}", idx, v.name);
        let lemma = match elaborated.lookup_lemma(&lemma_name) {
            Some(l) => l,
            None => continue,
        };
        let g = match formula_to_guarded(&lemma.formula) {
            Ok(g) => g,
            Err(_) => continue,
        };
        let sys = formula_to_system(
            Vec::new(),
            SourceKind::RawSources,
            p::TraceQuantifier::ExistsTrace,
            false,
            &g,
        );
        let t_prove = std::time::Instant::now();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_proof_search(&ctx, sys, 1000)
        }));
        let ok = matches!(result, Ok(ref n) if matches!(n.status, NodeStatus::Solved));
        let prove_dt = t_prove.elapsed();
        *total_prove += prove_dt;
        *var_count += 1;
        if dbg_timing {
            eprintln!(
                "[deriv-timing] rule={} var={} prove={:.3}s ok={}",
                rule_name, v.name, prove_dt.as_secs_f64(), ok,
            );
        }
        if !ok {
            // HS reports `show LVar` — sort prefix included
            // (MessageDerivationChecks.hs:138,156).
            let prefix = match v.sort {
                p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) => "~",
                p::SortHint::Pub | p::SortHint::Suffix(p::SuffixSort::Pub) => "$",
                p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node) => "#",
                p::SortHint::Nat | p::SortHint::Suffix(p::SuffixSort::Nat) => "%",
                _ => "",
            };
            if v.idx == 0 {
                undecidable.push(format!("{}{}", prefix, v.name));
            } else {
                undecidable.push(format!("{}{}.{}", prefix, v.name, v.idx));
            }
        }
    }

    // Restore prior deadline so the deriv check doesn't leak into the
    // main prove loop.
    match prev_deadline {
        Some(v) => std::env::set_var("TAM_PROVE_DEADLINE_MS", v),
        None => std::env::remove_var("TAM_PROVE_DEADLINE_MS"),
    }
    Some(undecidable)
}

fn format_deriv_report(per_rule: &[(String, Vec<String>)]) -> Vec<WfError> {
    if per_rule.is_empty() { return Vec::new(); }
    // HS `reportVars` (Theory/Tools/MessageDerivationChecks.hs:122-127)
    //   `[(underlineTopic "Message Derivation Checks",
    //     text $ "The variables of the following rule(s) ... pattern matching.\n\n" ++ errors)]`
    // The renderer in HS (`prettyWfErrorReport`) lays the topic + body
    // out as `<title>\n<====>\n\n  <body>\n`. The body is then indented
    // by 2 spaces at its first line via `nest 2`-equivalent, then the
    // per-rule blocks follow at col 0. See HS output bytes — the intro
    // line has a 2-space leading indent.
    let mut msg = tamarin_parser::wf::underline_topic("Message Derivation Checks");
    msg.push('\n');
    msg.push_str(
        "  The variables of the following rule(s) are not derivable \
         from their premises, you may be performing unintended pattern \
         matching.\n\n");
    let blocks: Vec<String> = per_rule.iter()
        .map(|(rule_name, vars)| {
            format!("Rule {}: \nFailed to derive Variable(s): {}",
                rule_name, vars.join(", "))
        })
        .collect();
    msg.push_str(&blocks.join("\n\n"));
    vec![WfError::new("Message Derivation Checks", msg)]
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parse_theory;

    fn maude() -> Option<MaudeHandle> {
        let p = "/home/linuxbrew/.linuxbrew/bin/maude";
        if !std::path::Path::new(p).exists() { return None; }
        MaudeHandle::start(p, tamarin_term::maude_sig::pair_maude_sig()).ok()
    }

    #[test]
    fn deriv_check_passes_on_derivable_var() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [In(x)] --[Use(x)]-> [Out(x)]
              lemma trivial: "T"
            end
        "#;
        let thy = parse_theory(src, &[]).expect("parse");
        let report = check_message_derivation(&thy, &m, 5);
        // `x` appears in `In(x)` which is intruder-known → derivable.
        assert!(report.is_empty(), "expected no warnings, got {:?}", report);
    }

    #[test]
    fn deriv_check_flags_unbound_var() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [] --[Use(unbound)]-> [Out(unbound)]
              lemma trivial: "T"
            end
        "#;
        let thy = parse_theory(src, &[]).expect("parse");
        let report = check_message_derivation(&thy, &m, 5);
        // Free `unbound` has no premise → not derivable.
        assert_eq!(report.len(), 1);
        assert!(report[0].message.contains("unbound"),
            "expected 'unbound' in report, got {:?}", report);
    }

    #[test]
    fn deriv_check_disabled_by_zero_timeout() {
        let Some(m) = maude() else { return };
        let src = r#"
            theory T begin
              rule R: [] --[Use(unbound)]-> [Out(unbound)]
              lemma trivial: "T"
            end
        "#;
        let thy = parse_theory(src, &[]).expect("parse");
        let report = check_message_derivation(&thy, &m, 0);
        assert!(report.is_empty(), "timeout=0 should disable the check");
    }
}
