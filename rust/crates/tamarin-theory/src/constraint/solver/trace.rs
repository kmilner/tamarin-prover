//! Synchronized execution-trace facility for diffing against the
//! Haskell tamarin-prover's `TAM_HS_TRACE_EXEC` output.
//!
//! Set `TAM_RS_TRACE_EXEC=1` to enable.  Each major solver entry point
//! emits a single `[EXEC] <function> <canonical-data>` line via
//! [`trace_exec`].  Output format is intentionally identical to the
//! Haskell side's `T.traceExecM` so the two logs can be `diff`-ed to
//! find the first execution divergence between the implementations.
//!
//! Design choices:
//! - The env var is read once via `std::sync::OnceLock` so the check
//!   is essentially free when the trace is disabled.
//! - No sequence numbers in the output — keeps the diff focused on
//!   trace-content drift instead of counter drift.
//! - Data is normalised to suppress fresh-var indices (use canonical
//!   sort prefix + name only).  Mirror Haskell's `goalKind` /
//!   `factCanonical` choices in the trace sites.

use std::sync::OnceLock;
use std::cell::RefCell;

thread_local! {
    /// Stack of case-names from proof tree root to current node.
    /// Pushed/popped by `case_path_push` / `case_path_pop` in
    /// `search.rs::expand` and HS analog `solve`.  Emitted by
    /// `trace_state` so each [STATE] line can be matched by the
    /// EXACT proof path that produced it — solves the HS Disj-monad
    /// branch-interleaving problem where the same goal-shape appears
    /// at many proof positions.
    static CASE_PATH: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

pub fn case_path_push(name: &str) {
    CASE_PATH.with(|p| p.borrow_mut().push(name.to_string()));
}

pub fn case_path_pop() {
    CASE_PATH.with(|p| { p.borrow_mut().pop(); });
}

pub fn case_path_string() -> String {
    CASE_PATH.with(|p| {
        let v = p.borrow();
        if v.is_empty() { "/".to_string() } else { format!("/{}", v.join("/")) }
    })
}

/// TAM_RS_TRACE_FORM=1 emits `[FORMULA_ADD] path=... kind=... <repr>` lines
/// for each formula insertion into sys.formulas / sys.goals.  Pairs with
/// HS's `TAM_HS_TRACE_FORM` for finding insertion divergences.
pub fn form_flag() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("TAM_RS_TRACE_FORM").is_ok())
}

pub fn trace_form(kind: &str, repr: &str) {
    if form_flag() {
        eprintln!("[FORMULA_ADD] path={} kind={} {}", case_path_string(), kind, repr);
    }
}

/// Canonicalized representation of a Guarded formula for [FORMULA_ADD]
/// tracing — recursive structural dump with full bound-term content
/// (var idxs suppressed via name-only LVar rendering) so HS/Rust diffs
/// can distinguish formulas with the same head shape but different
/// instantiation of free vars (e.g., `KU(ni:42)` vs `KU(ni:44)`).
pub fn guarded_repr(g: &crate::guarded::Guarded) -> String {
    use crate::guarded::Guarded;
    match g {
        Guarded::Atom(a) => format!("Atom({})", atom_repr(a)),
        Guarded::Conj(items) => {
            let s: Vec<String> = items.iter().map(guarded_repr).collect();
            format!("Conj[{}]", s.join(","))
        }
        Guarded::Disj(items) => {
            let s: Vec<String> = items.iter().map(guarded_repr).collect();
            format!("Disj[{}]", s.join("|"))
        }
        Guarded::GGuarded { qua, vars, guards, body } => {
            let g_strs: Vec<String> = guards.iter().map(atom_repr).collect();
            format!("{:?}{}v[{}]({})", qua, vars.len(), g_strs.join(","), guarded_repr(body))
        }
    }
}

fn atom_repr(a: &tamarin_parser::ast::Atom) -> String {
    use tamarin_parser::ast::Atom;
    match a {
        Atom::Eq(s, t) => format!("Eq({},{})", term_repr(s), term_repr(t)),
        Atom::Less(s, t) => format!("Less({},{})", term_repr(s), term_repr(t)),
        Atom::LessMset(s, t) => format!("LMset({},{})", term_repr(s), term_repr(t)),
        Atom::Subterm(s, t) => format!("Subterm({},{})", term_repr(s), term_repr(t)),
        Atom::Last(s) => format!("Last({})", term_repr(s)),
        Atom::Action(f, t) => format!("{}({})@{}",
            f.name, f.args.iter().map(term_repr).collect::<Vec<_>>().join(","),
            term_repr(t)),
        Atom::Pred(f) => format!("Pred({})", f.name),
    }
}

fn term_repr(t: &tamarin_parser::ast::Term) -> String {
    use tamarin_parser::ast::Term;
    match t {
        Term::Var(v) => format!("{}{}#{}", match v.sort {
            tamarin_parser::ast::SortHint::Fresh => "~",
            tamarin_parser::ast::SortHint::Pub   => "$",
            tamarin_parser::ast::SortHint::Node  => "#",
            tamarin_parser::ast::SortHint::Nat   => "%",
            tamarin_parser::ast::SortHint::Msg   => "",
            _ => "?",
        }, v.name, v.idx),  // idx KEPT so we can spot real differences
        Term::App(name, args) => format!("{}({})", name,
            args.iter().map(term_repr).collect::<Vec<_>>().join(",")),
        Term::Pair(args) =>
            format!("<{}>", args.iter().map(term_repr).collect::<Vec<_>>().join(",")),
        Term::AlgApp(name, a, b) => format!("{}({},{})", name, term_repr(a), term_repr(b)),
        Term::Diff(a, b) => format!("diff({},{})", term_repr(a), term_repr(b)),
        Term::BinOp(op, a, b) => format!("{:?}({},{})", op, term_repr(a), term_repr(b)),
        Term::PubLit(s) => format!("'{}'", s),
        Term::FreshLit(s) => format!("~'{}'", s),
        Term::NatLit(s) => format!("%'{}'", s),
        Term::Number(n) => format!("{}", n),
        Term::NumberOne => "1".to_string(),
        Term::NatOne => "%1".to_string(),
        Term::DhNeutral => "1g".to_string(),
        Term::PatMatch(t) => format!("=({})", term_repr(t)),
    }
}

fn flag() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("TAM_RS_TRACE_EXEC").is_ok())
}

/// Static-string `traceExecM` labels that HS emits exactly once per
/// program run due to GHC CSE on the literal `String` argument to
/// `traceM`.  The full set, identified by grepping HS for
/// `T.traceExecM "..."` (literal-only):
///
///   - `simplifySystem`            (Simplify.hs:67)
///   - `solveChain ENTER`          (Goals.hs:323)
///   - `FrNarrow`                  (Reduction.hs:271)
///   - `exploitPrem InFact`        (Reduction.hs:250)
///
/// All other `traceExecM` callsites use a concatenated string
/// (`++ show n`, `++ getRuleName ru`, etc.) which has a distinct
/// expression per call and emits per-invocation in HS.
///
/// Rust's `trace_exec` would otherwise emit per call for these too —
/// diverging from HS even though the underlying work matches.  Dedup
/// here on first emission per program run, matching HS line-for-line.
fn is_cse_deduplicated_label(label: &str) -> bool {
    matches!(label,
        "simplifySystem"
        | "solveChain ENTER"
        | "FrNarrow"
        | "exploitPrem InFact"
    )
}

/// Has this CSE-deduplicated label already been emitted in this
/// program run?  Returns `true` if already seen (skip emission),
/// `false` and records it if first time.
fn check_and_mark_emitted(label: &str) -> bool {
    use std::collections::HashSet;
    use std::sync::Mutex;
    static EMITTED: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
    let set = EMITTED.get_or_init(|| Mutex::new(HashSet::new()));
    let mut g = set.lock().unwrap();
    if g.contains(label) {
        true
    } else {
        g.insert(label.to_string());
        false
    }
}

/// Emit a `[EXEC] <label>` line to stderr when `TAM_RS_TRACE_EXEC=1`.
/// No-op otherwise.  Keep `label` in the same canonical form as the
/// Haskell `T.traceExecM` callsite so the outputs diff cleanly.
///
/// For labels HS deduplicates via GHC CSE (see
/// [`is_cse_deduplicated_label`]), emit only on first occurrence per
/// program run — matching HS's effective once-per-program emission
/// for those literal-string `traceExecM` callsites.
#[inline]
pub fn trace_exec(label: &str) {
    if !flag() { return; }
    if is_cse_deduplicated_label(label) && check_and_mark_emitted(label) {
        return;
    }
    eprintln!("[EXEC] {}", label);
}

/// Convenience: format a `LSort`-tagged short variable identifier
/// matching Haskell's `Show LVar` (e.g., `~name`, `$name`, `#name`,
/// `name` for Msg).  Use for the term-head field of `solveGoal` so
/// the canonical form matches the Haskell side.
pub fn sort_prefix(s: tamarin_term::lterm::LSort) -> &'static str {
    use tamarin_term::lterm::LSort;
    match s {
        LSort::Msg   => "",
        LSort::Fresh => "~",
        LSort::Pub   => "$",
        LSort::Node  => "#",
        LSort::Nat   => "%",
    }
}

fn state_flag() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("TAM_RS_TRACE_STATE").is_ok())
}

/// Emit a `[STATE]` line summarising the system state in a form designed
/// to diff against Haskell's `TAM_HS_TRACE_STATE` output.  Fields:
///
/// - `nodes`: sorted, count-compressed list of rule-case-names
///   (e.g. `I_2×1, I_1×1, Register_pk×3, isend×2, Fresh×4, Secrecy_claim×1`).
///   Var idxs are suppressed so two structurally-identical systems compare
///   equal across HS/Rust idx allocation drift.
/// - `goals`: sorted list of UNSOLVED goal kinds with canonical fact heads:
///   `Action(KU(aenc)), Premise(Secret), Disj[Ku(t)∥Out_R_1]`. The fact head
///   matches Haskell `goalKind`'s `factCanonical` (Goals.hs:218-234).
/// - `formulas` / `solved_formulas`: counts only (full bodies elided to
///   keep the line readable; depth dumps available via other flags).
///
/// Called right before each `solveGoal` dispatch (paired with the
/// `[EXEC] solveGoal ...` line) so we can see exactly what state HS / Rust
/// had when each ranking decision was made.
pub fn trace_state(sys: &crate::constraint::system::System) {
    if !state_flag() { return; }
    eprintln!("[STATE] path={} nodes={} goals={} formulas={} solved_formulas={}",
        case_path_string(),
        canonical_nodes(sys),
        canonical_open_goals(sys),
        sys.formulas.len(),
        sys.solved_formulas.len());
    if state_full_flag() {
        // Additional [STATE_FULL] emission for fine-grained lockstep
        // diff: dumps the FULL action terms with var idxs suppressed
        // (canonical form for clean HS-Rust diff).
        eprintln!("[STATE_FULL] node_actions={}", canonical_node_actions(sys));
        eprintln!("[STATE_FULL] open_actions={}", canonical_open_actions(sys));
    }
    if state_eqs_flag() {
        // `TAM_RS_TRACE_STATE_EQS=1`: dump canonical eq_store contents
        // for HS vs Rust binding-divergence diagnosis.  Idxs suppressed
        // so the diff catches semantic divergences (different name
        // unifications) rather than idx-allocation drift.
        eprintln!("[STATE_EQS] path={} subst={} conj={}",
            case_path_string(),
            canonical_eq_store_subst(sys),
            sys.eq_store.conj.len());
    }
    if state_forms_flag() {
        // `TAM_RS_TRACE_STATE_FORMS=1`: dump full formula content at
        // each [STATE] checkpoint.  Used when state counts diverge from
        // HS (e.g., HS has more formulas than Rust at the same path):
        // shows which specific formulas Rust is missing relative to HS.
        for (i, f) in sys.formulas.iter().enumerate() {
            eprintln!("[STATE_FORM] path={} formulas[{}]={}",
                case_path_string(), i, guarded_repr(f));
        }
        for (i, f) in sys.solved_formulas.iter().enumerate() {
            eprintln!("[STATE_FORM] path={} solved[{}]={}",
                case_path_string(), i, guarded_repr(f));
        }
    }
    if state_nodes_flag() {
        // `TAM_RS_TRACE_STATE_NODES=1`: dump each node with its full
        // rule case-name + ALL actions (with var idxs preserved) so
        // HS↔Rust diff can detect missing chain levels (e.g.
        // Helper_Loop_and_success: HS has Loop(~n, f(f(k.1)), kOrig)
        // at parent path; Rust only has Loop(~n, k, kOrig) / Loop(~n,
        // f(k), kOrig) — missing the third chain level).
        for (id, rule) in &sys.nodes {
            let rc = crate::constraint::solver::reduction::rule_case_name(rule);
            let acts: Vec<String> = rule.actions.iter()
                .map(canonical_fact_with_idx).collect();
            eprintln!("[STATE_NODE] path={} {}.{}={} actions=[{}]",
                case_path_string(), id.name, id.idx, rc, acts.join(", "));
        }
        for e in &sys.edges {
            eprintln!("[STATE_EDGE] path={} {}.{}/{} -> {}.{}/{}",
                case_path_string(),
                e.src.0.name, e.src.0.idx, e.src.1.0,
                e.tgt.0.name, e.tgt.0.idx, e.tgt.1.0);
        }
        // Also dump open Action goals with their idx-preserved fact
        // content (the canonical [STATE] line above suppresses idxs).
        // These are Ex-decomposed action atoms that haven't been folded
        // into nodes yet — they participate in `impl_formulas` matching
        // and are critical for diagnosing IH-Forall-fires-but-misses-
        // gfalse divergences at case-3 (Helper_Loop_and_success).
        use crate::constraint::constraints::Goal;
        for (g, st) in &sys.goals {
            if st.solved { continue; }
            if let Goal::Action(node, fa) = g {
                eprintln!("[STATE_GOAL] path={} Action@{}.{}={}",
                    case_path_string(), node.name, node.idx,
                    canonical_fact_with_idx(fa));
            }
        }
    }
}

fn state_nodes_flag() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("TAM_RS_TRACE_STATE_NODES").is_ok())
}

/// Like `canonical_fact` but KEEPS the LVar idx so diffs reveal node
/// chain depth (which would otherwise canonicalise to the same shape).
fn canonical_fact_with_idx(fa: &crate::fact::LNFact) -> String {
    let terms: Vec<String> = fa.terms.iter().map(canonical_lnterm_with_idx).collect();
    format!("{}({})", fact_tag_short(&fa.tag), terms.join(","))
}

fn canonical_lnterm_with_idx(t: &tamarin_term::lterm::LNTerm) -> String {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_term::function_symbols::FunSym;
    match t {
        Term::Lit(Lit::Var(v)) => {
            format!("{}{}#{}", sort_prefix(v.sort), v.name, v.idx)
        }
        Term::Lit(Lit::Con(n)) => {
            let nm = &n.id.0;
            match n.tag {
                tamarin_term::lterm::NameTag::Pub => format!("'{}'", nm),
                tamarin_term::lterm::NameTag::Fresh => format!("~'{}'", nm),
                tamarin_term::lterm::NameTag::Nat => format!("%{}", nm),
                tamarin_term::lterm::NameTag::Node => format!("#'{}'", nm),
            }
        }
        Term::App(sym, args) => {
            let head = match sym {
                FunSym::NoEq(s) => String::from_utf8_lossy(&s.name).to_string(),
                FunSym::C(_) => "C".to_string(),
                FunSym::Ac(_) => "AC".to_string(),
                FunSym::List => "List".to_string(),
            };
            let args_s: Vec<String> = args.iter().map(canonical_lnterm_with_idx).collect();
            format!("{}({})", head, args_s.join(","))
        }
    }
}

fn state_forms_flag() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("TAM_RS_TRACE_STATE_FORMS").is_ok())
}

fn state_full_flag() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("TAM_RS_TRACE_STATE_FULL").is_ok())
}

fn state_eqs_flag() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("TAM_RS_TRACE_STATE_EQS").is_ok())
}

/// Canonical dump of `sys.eq_store.subst`: sorted list of canonical
/// `var → term` bindings, var idxs suppressed.  Mirrors HS's
/// `canonicalEqStoreSubst` (Trace.hs) so the lines diff line-by-line.
fn canonical_eq_store_subst(sys: &crate::constraint::system::System) -> String {
    let mut entries: Vec<String> = sys.eq_store.subst.to_list().into_iter().map(|(k, v)| {
        let k_str = format!("{}{}:{:?}", sort_prefix(k.sort), k.name, k.sort);
        let v_str = canonical_lnterm(&v);
        format!("{}→{}", k_str, v_str)
    }).collect();
    entries.sort();
    format!("[{}]", entries.join(", "))
}

/// Canonicalize an LNTerm by suppressing LVar idxs.  Keeps name+sort,
/// strips the numeric idx.  Same shape on HS / Rust => diff-able.
fn canonical_lnterm(t: &tamarin_term::lterm::LNTerm) -> String {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_term::function_symbols::FunSym;
    match t {
        Term::Lit(Lit::Var(v)) => {
            format!("{}{}:{:?}", sort_prefix(v.sort), v.name, v.sort)
        }
        Term::Lit(Lit::Con(n)) => {
            let nm = &n.id.0;
            match n.tag {
                tamarin_term::lterm::NameTag::Pub => format!("'{}'", nm),
                tamarin_term::lterm::NameTag::Fresh => format!("~'{}'", nm),
                tamarin_term::lterm::NameTag::Nat => format!("%{}", nm),
                tamarin_term::lterm::NameTag::Node => format!("#'{}'", nm),
            }
        }
        Term::App(sym, args) => {
            let head = match sym {
                FunSym::NoEq(s) => String::from_utf8_lossy(&s.name).to_string(),
                FunSym::C(_) => "C".to_string(),
                FunSym::Ac(_) => "AC".to_string(),
                FunSym::List => "List".to_string(),
            };
            let args_s: Vec<String> = args.iter().map(canonical_lnterm).collect();
            format!("{}({})", head, args_s.join(","))
        }
    }
}

fn canonical_fact(fa: &crate::fact::LNFact) -> String {
    let terms: Vec<String> = fa.terms.iter().map(canonical_lnterm).collect();
    format!("{}({})", fact_tag_short(&fa.tag), terms.join(","))
}

fn canonical_node_actions(sys: &crate::constraint::system::System) -> String {
    // Dump all action atoms from sys.nodes — same iteration order as
    // Haskell's `allActions sys` (M.toList sNodes <- rActs).  Idxs
    // suppressed for clean diff.
    let mut acts: Vec<String> = Vec::new();
    for (_, rule) in &sys.nodes {
        for a in &rule.actions {
            acts.push(canonical_fact(a));
        }
    }
    acts.sort();
    let compressed = compress_dups(&acts);
    compressed
}

fn canonical_open_actions(sys: &crate::constraint::system::System) -> String {
    use crate::constraint::constraints::Goal;
    let mut acts: Vec<String> = Vec::new();
    for (g, st) in &sys.goals {
        if st.solved { continue; }
        if let Goal::Action(_, fa) = g {
            acts.push(canonical_fact(fa));
        }
    }
    acts.sort();
    let compressed = compress_dups(&acts);
    compressed
}

/// Emit a [PICK] line indicating which goal was selected for this dispatch.
/// Paired with HS's `tracePickM` so we can compare goal-ranking decisions.
pub fn trace_pick(g: &crate::constraint::constraints::Goal) {
    use crate::constraint::constraints::Goal;
    if !state_flag() { return; }
    let s = match g {
        Goal::Action(_, fa)  => format!("Action({}/{})",
            fact_tag_short(&fa.tag), fa.terms.len()),
        Goal::Premise(_, fa) => format!("Premise({}/{})",
            fact_tag_short(&fa.tag), fa.terms.len()),
        Goal::Chain(_, _)    => "Chain".to_string(),
        Goal::Split(_)       => "Split".to_string(),
        Goal::Disj(d)        => format!("Disj[{}]", disj_heads(d)),
        Goal::Subterm(_)     => "Subterm".to_string(),
    };
    // For Disj goals, also dump the full alternatives (with var idxs
    // preserved) so HS↔Rust comparison can catch dispatch-order
    // divergences — e.g. Helper_Loop_and_success at case_3 has 2
    // Disj goals with identical PICK heads (`Disj[Atom(Eq)|Atom(Less)
    // |Ex1v]`) but DIFFERENT alternatives (one has ChainKey(k#1) in
    // its Ex body, the other has ChainKey(f(k#1))).  HS picks the
    // f-wrapped one first; Rust picks the bare-k#1 one — causing the
    // case_3 over-split.
    if let Goal::Disj(d) = g {
        if std::env::var("TAM_RS_TRACE_PICK_DISJ").is_ok() {
            let alts: Vec<String> = d.0.iter().map(guarded_repr).collect();
            eprintln!("[PICK_DISJ] Disj[{}]", alts.join(" || "));
        }
    }
    eprintln!("[PICK] {}", s);
}

fn canonical_nodes(sys: &crate::constraint::system::System) -> String {
    use crate::constraint::solver::reduction::rule_case_name;
    let mut names: Vec<String> = sys.nodes.iter()
        .map(|(_, r)| rule_case_name(r))
        .collect();
    names.sort();
    compress_dups(&names)
}

fn canonical_open_goals(sys: &crate::constraint::system::System) -> String {
    use crate::constraint::constraints::Goal;
    let mut digests: Vec<String> = sys.goals.iter()
        .filter(|(_, st)| !st.solved)
        .map(|(g, _)| match g {
            Goal::Action(_, fa)  => format!("Action({}/{})",
                fact_tag_short(&fa.tag), fa.terms.len()),
            Goal::Premise(_, fa) => format!("Premise({}/{})",
                fact_tag_short(&fa.tag), fa.terms.len()),
            Goal::Chain(_, _)    => "Chain".to_string(),
            Goal::Split(_)       => "Split".to_string(),
            Goal::Disj(d)        => format!("Disj[{}]", disj_heads(d)),
            Goal::Subterm(_)     => "Subterm".to_string(),
        })
        .collect();
    digests.sort();
    format!("[{}]", digests.join(","))
}

fn fact_tag_short(t: &crate::fact::FactTag) -> String {
    use crate::fact::FactTag;
    match t {
        FactTag::Ku => "KU".to_string(),
        FactTag::Kd => "KD".to_string(),
        FactTag::Fresh => "Fr".to_string(),
        FactTag::Out => "Out".to_string(),
        FactTag::In => "In".to_string(),
        FactTag::Proto(_, name, _) => name.clone(),
        _ => "?".to_string(),
    }
}

fn fact_term_head(fa: &crate::fact::LNFact) -> String {
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    if let Some(t) = fa.terms.first() {
        match t {
            Term::Lit(Lit::Var(v)) => format!("{}var", sort_prefix(v.sort)),
            Term::Lit(Lit::Con(_)) => "<const>".to_string(),
            // Use Debug; suffices for a stable rendering across runs as long
            // as the function symbol's Debug output is name-only.  We don't
            // need the full term tree — just the head — so truncate.
            Term::App(sym, _) => {
                let s = format!("{:?}", sym);
                s.chars().take(40).collect::<String>()
            }
        }
    } else {
        String::new()
    }
}

fn disj_heads(d: &crate::constraint::constraints::Disj<crate::guarded::Guarded>) -> String {
    let heads: Vec<String> = d.0.iter().map(guarded_head).collect();
    heads.join("|")
}

fn guarded_head(g: &crate::guarded::Guarded) -> String {
    use crate::guarded::Guarded;
    match g {
        Guarded::Atom(a) => format!("Atom({})", atom_head(a)),
        Guarded::Conj(_) => "Conj".to_string(),
        Guarded::Disj(_) => "Disj".to_string(),
        // Format matches HS Trace.hs::guardedHead: `<Quant><N>v` (e.g. `Ex1v`).
        // Suppresses bound-var names so HS/Rust line up.
        Guarded::GGuarded { qua, vars, .. } => format!("{:?}{}v",
            qua, vars.len()),
    }
}

fn atom_head(a: &tamarin_parser::ast::Atom) -> String {
    use tamarin_parser::ast::Atom;
    match a {
        Atom::Eq(_, _) => "Eq".to_string(),
        Atom::Less(_, _) => "Less".to_string(),
        Atom::LessMset(_, _) => "LessMset".to_string(),
        Atom::Subterm(_, _) => "Subterm".to_string(),
        Atom::Last(_) => "Last".to_string(),
        Atom::Action(f, _) => format!("Action({})", f.name),
        Atom::Pred(f) => format!("Pred({})", f.name),
    }
}

fn compress_dups(sorted: &[String]) -> String {
    if sorted.is_empty() { return "[]".to_string(); }
    let mut out = String::from("[");
    let mut iter = sorted.iter().peekable();
    while let Some(first) = iter.next() {
        let mut count = 1usize;
        while iter.peek().map(|s| s.as_str()) == Some(first.as_str()) {
            iter.next();
            count += 1;
        }
        if count > 1 {
            out.push_str(&format!("{}×{}", first, count));
        } else {
            out.push_str(first);
        }
        if iter.peek().is_some() { out.push(','); }
    }
    out.push(']');
    out
}
