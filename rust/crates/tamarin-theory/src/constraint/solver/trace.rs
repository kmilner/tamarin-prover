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
