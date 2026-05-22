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

fn flag() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("TAM_RS_TRACE_EXEC").is_ok())
}

/// Emit a `[EXEC] <label>` line to stderr when `TAM_RS_TRACE_EXEC=1`.
/// No-op otherwise.  Keep `label` in the same canonical form as the
/// Haskell `T.traceExecM` callsite so the outputs diff cleanly.
#[inline]
pub fn trace_exec(label: &str) {
    if flag() {
        eprintln!("[EXEC] {}", label);
    }
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
    eprintln!("[STATE] nodes={} goals={} formulas={} solved_formulas={}",
        canonical_nodes(sys),
        canonical_open_goals(sys),
        sys.formulas.len(),
        sys.solved_formulas.len());
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
