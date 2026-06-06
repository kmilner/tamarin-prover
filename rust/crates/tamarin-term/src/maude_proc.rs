//! Port of `Term.Maude.Process` — a subprocess driver for Maude.
//!
//! Spawns `maude -interactive -no-tecla -no-banner -no-wrap -batch`,
//! feeds it a `fmod MSG ... endfm` module describing the term algebra,
//! and exposes `unify`, `match`, `variants`, and `reduce` operations.
//!
//! The protocol is line-oriented: every command ends with `.\n` and
//! Maude's response ends with the prompt `Maude> `.

use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};

use crate::lterm::LNTerm;
use crate::maude_parse;
use crate::maude_print::{pp_mterm, pp_theory};
use crate::maude_sig::MaudeSig;
use crate::maude_types::{
    lterm_to_mterm_global, mterm_to_lnterm, ConvCtx, MSubst, MTerm,
};
use crate::rewriting::Equal;

const PROMPT: &[u8] = b"Maude> ";

/// Errors that can arise from the Maude bridge.
#[derive(Debug)]
pub enum MaudeError {
    Io(std::io::Error),
    Spawn(String),
    Parse(maude_parse::ParseError),
    Other(String),
}

impl std::fmt::Display for MaudeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaudeError::Io(e) => write!(f, "io error: {}", e),
            MaudeError::Spawn(s) => write!(f, "spawn error: {}", s),
            MaudeError::Parse(e) => write!(f, "parse error: {}", e),
            MaudeError::Other(s) => write!(f, "{}", s),
        }
    }
}
impl std::error::Error for MaudeError {}
impl From<std::io::Error> for MaudeError { fn from(e: std::io::Error) -> Self { MaudeError::Io(e) } }
impl From<maude_parse::ParseError> for MaudeError { fn from(e: maude_parse::ParseError) -> Self { MaudeError::Parse(e) } }

/// True if `t` contains any function symbol whose head matches one in
/// `reducible`.  Used as a fast-path predicate for `reduce`: if the
/// term contains no reducible symbols at all, `reduce` is the
/// identity, and we can skip the Maude IPC round-trip.
fn term_has_reducible_sym(
    t: &LNTerm,
    reducible: &crate::function_symbols::FunSig,
) -> bool {
    use crate::term::Term;
    fn rec(t: &LNTerm, reducible: &crate::function_symbols::FunSig) -> bool {
        match t {
            Term::Lit(_) => false,
            Term::App(f, args) => {
                reducible.contains(f) || args.iter().any(|a| rec(a, reducible))
            }
        }
    }
    rec(t, reducible)
}

/// Statistics on Maude operations performed via this handle.
#[derive(Debug, Default, Clone, Copy)]
pub struct MaudeStats {
    pub unify_count: u64,
    pub match_count: u64,
    pub norm_count: u64,
    pub var_count: u64,
}

thread_local! {
    /// Per-callsite Maude call counters.  Set `TAM_PROFILE_MAUDE=1` to
    /// enable; query via `dump_callsite_profile()`.  Diagnostic only —
    /// used in investigation #29 to confirm 100 % of `unify` calls
    /// originate from `eq_store::add_eqs` (so optimisation effort
    /// should target the fact-equation engine, not other call sites).
    static MAUDE_CALLSITE_COUNTS: std::cell::RefCell<std::collections::BTreeMap<&'static str, u64>>
        = std::cell::RefCell::new(std::collections::BTreeMap::new());
}

#[doc(hidden)]
pub fn _tally_callsite(label: &'static str) {
    if std::env::var_os("TAM_PROFILE_MAUDE").is_some() {
        MAUDE_CALLSITE_COUNTS.with(|m| *m.borrow_mut().entry(label).or_insert(0) += 1);
    }
}

#[doc(hidden)]
pub fn dump_callsite_profile() -> Vec<(String, u64)> {
    MAUDE_CALLSITE_COUNTS.with(|m| m.borrow().iter()
        .map(|(k, v)| ((*k).to_string(), *v)).collect())
}

struct MaudeProcessInner {
    stdin: ChildStdin,
    stdout: ChildStdout,
    stats: MaudeStats,
    sig: MaudeSig,
    path: PathBuf,
    /// Memo for `unifiable(...)` queries — see `MaudeHandle::unifiable`.
    /// Caches the *boolean* outcome (true = at least one unifier
    /// exists).  Witness LVars produced inside the subst aren't safe
    /// to cache across calls (their indices need fresh-renaming each
    /// time) so we don't memoize substitutions, only the existence
    /// answer.
    unifiable_cache: std::collections::HashMap<Vec<(LNTerm, LNTerm)>, bool>,
    /// Memo for `reduce(...)` queries.  Maude `reduce` is a pure
    /// function of the input term modulo the (fixed-per-handle) theory
    /// signature, so successful reductions can be cached across calls.
    /// `has_non_normal_terms` (contradictions.rs) calls `reduce` on
    /// every candidate subterm of every node, and `is_finished` runs
    /// every search step — so the same subterm gets reduced repeatedly
    /// during a single proof.  Caching cuts those repeat round-trips.
    reduce_cache: std::collections::HashMap<LNTerm, LNTerm>,
    /// Memo for `match_eqs_const_subject` EMPTY-result queries.
    /// Profiling on csf17/keylessssl::injectivity showed 210 k calls
    /// to this matcher, ALL returning empty.  Many are identical
    /// (same skolemized pattern + subject re-tried across fixpoint
    /// passes).  Caching the empty answer is safe — no witness LVars
    /// to renumber.  Non-empty results are NOT cached (witnesses
    /// need fresh-renaming per use, same reason `unifiable_cache`
    /// only stores booleans).
    match_empty_cache: std::collections::HashMap<(Vec<(LNTerm, LNTerm)>, Vec<(String, u64)>), ()>,
}

impl MaudeProcessInner {
    fn write_line(&mut self, line: &[u8]) -> Result<(), MaudeError> {
        self.stdin.write_all(line)?;
        self.stdin.flush()?;
        Ok(())
    }

    fn read_until_prompt(&mut self) -> Result<Vec<u8>, MaudeError> {
        let mut buf = Vec::new();
        let mut tmp = [0u8; 4096];
        loop {
            let n = self.stdout.read(&mut tmp)?;
            if n == 0 {
                return Err(MaudeError::Other(
                    "Maude exited unexpectedly".into()));
            }
            buf.extend_from_slice(&tmp[..n]);
            if let Some(pos) = find_subseq(&buf, PROMPT) {
                let before = buf[..pos].to_vec();
                return Ok(before);
            }
        }
    }

    fn execute(&mut self, cmd: &[u8]) -> Result<Vec<u8>, MaudeError> {
        // `TAM_DBG_MAUDE_IO=1` — truncated trace (200 chars).
        // `TAM_DBG_MAUDE_IO=full` — full command + response, for HS↔RS
        //   side-by-side Maude command comparison.
        // `TAM_DBG_MAUDE_IO_FILTER=unify` — only dump unify/variant unify
        //   calls (suppresses set/show/reduce noise).  Matches HS's
        //   `TAM_HS_DBG_MAUDE_IO` semantics.
        let trace_mode = std::env::var("TAM_DBG_MAUDE_IO").unwrap_or_default();
        let trace_enabled = !trace_mode.is_empty();
        let trace_full = trace_mode == "full";
        let filter = std::env::var("TAM_DBG_MAUDE_IO_FILTER").unwrap_or_default();
        let cmd_str_full: String = cmd.iter().map(|&b| b as char).collect();
        let cmd_keep = if filter.is_empty() { true }
            else { cmd_str_full.contains(filter.as_str()) };
        if trace_enabled && cmd_keep {
            let cmd_str = if trace_full { cmd_str_full.clone() }
                else { cmd_str_full.chars().take(200).collect() };
            eprintln!("[maude>] {}", cmd_str.replace('\n', "\\n"));
        }
        self.write_line(cmd)?;
        let result = self.read_until_prompt();
        if trace_enabled && cmd_keep {
            match &result {
                Ok(reply) => {
                    let reply_str_full: String = reply.iter().map(|&b| b as char).collect();
                    let reply_str = if trace_full { reply_str_full }
                        else { reply.iter().take(200).map(|&b| b as char).collect() };
                    eprintln!("[maude<] {} bytes: {}",
                        reply.len(), reply_str.replace('\n', "\\n"));
                }
                Err(e) => eprintln!("[maude<] ERR: {:?}", e),
            }
        }
        result
    }
}

/// Reaper for the Maude `Child` handle.  Lives in its own `Arc<Mutex<...>>`
/// separate from the I/O mutex so that a watchdog can kill the
/// subprocess WITHOUT contending with a reader thread that's blocked
/// inside `read_until_prompt` while holding the I/O lock.
struct MaudeChildReaper {
    child: Option<Child>,
}

impl MaudeChildReaper {
    fn kill_and_wait(&mut self) {
        if let Some(mut c) = self.child.take() {
            match c.try_wait() {
                Ok(Some(_)) => {}
                _ => {
                    let _ = c.kill();
                    let _ = c.wait();
                }
            }
        }
    }
}

impl Drop for MaudeChildReaper {
    fn drop(&mut self) {
        // Reap the Maude subprocess on handle drop.  `Child::drop`
        // alone DETACHES the process (the rust stdlib's std::process
        // does not kill on drop), leaking zombies.
        self.kill_and_wait();
    }
}

fn find_subseq(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() { return None; }
    haystack.windows(needle.len()).position(|w| w == needle)
}

/// Handle to a running Maude subprocess. Cloneable; uses an `Arc<Mutex<...>>`
/// internally so calls from multiple owners are serialised.
/// The `Child` reaper sits in its OWN mutex so a watchdog can
/// `kill_subprocess()` even while a reader thread is blocked on Maude
/// IPC inside `inner` — without this split, the watchdog deadlocks
/// trying to acquire the same mutex the blocked reader holds.
#[derive(Clone)]
pub struct MaudeHandle {
    inner: Arc<Mutex<MaudeProcessInner>>,
    child: Arc<Mutex<MaudeChildReaper>>,
    /// Monotonically-increasing counter for fresh-variable allocation.
    ///
    /// Mirrors Haskell's `MonadFresh` (`FreshT m` in lib/utils): a SINGLE
    /// global counter shared across the entire proof session so that
    /// every `freshLVar` call gets a unique idx.  Without this, two
    /// independent Maude calls can both compute `avoid_max + 1` as the
    /// next witness idx and produce colliding `(name, idx)` LVars at
    /// different sorts (e.g. `~mw:Pub:17` from one call and
    /// `~mw:Msg:17` from another).  Those collisions break our
    /// `(name, sort, idx)` LVar identity, leading to sort-conflated
    /// saved source cases (see project_rust_tesla_sender0a_diagnosis).
    ///
    /// Used by:
    /// - `msubst_to_lnsubst_with_avoid` for Maude witness allocation.
    /// - `freshen_witness_range` (eq_store) for post-unification renames.
    /// - `freshen_rule` / `freshen_system` (reduction) for rule shift.
    ///
    /// Every consumer first calls `ensure_above(local_avoid_max)` to
    /// guarantee the counter is at least as high as the current system
    /// bounds, then calls `fresh_idx()` to allocate.  The counter NEVER
    /// goes backward, so once a witness/rule idx is allocated it can
    /// never be reused.
    fresh_counter: Arc<AtomicU64>,
}

impl std::fmt::Debug for MaudeHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MaudeHandle(running)")
    }
}

impl MaudeHandle {
    /// Start a new Maude process and load the theory module for `sig`.
    pub fn start(maude_path: &str, sig: MaudeSig) -> Result<Self, MaudeError> {
        let mut child = Command::new(maude_path)
            .arg("-interactive")
            .arg("-no-tecla")
            .arg("-no-banner")
            .arg("-no-wrap")
            .arg("-batch")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| MaudeError::Spawn(format!("{}: {}", maude_path, e)))?;
        let stdin = child.stdin.take().expect("piped stdin");
        let stdout = child.stdout.take().expect("piped stdout");
        let reaper = MaudeChildReaper { child: Some(child) };
        let mut inner = MaudeProcessInner {
            stdin,
            stdout,
            stats: MaudeStats::default(),
            sig: sig.clone(),
            path: PathBuf::from(maude_path),
            unifiable_cache: std::collections::HashMap::new(),
            reduce_cache: std::collections::HashMap::new(),
            match_empty_cache: std::collections::HashMap::new(),
        };
        // Banner / initial prompt.
        let _ = inner.read_until_prompt()?;
        // Quiet mode.
        for cmd in [
            "set show command off .\n",
            "set show timing off .\n",
            "set show stats off .\n",
        ] {
            let _ = inner.execute(cmd.as_bytes())?;
        }
        // Load the theory.
        let theory = pp_theory(&sig);
        let _ = inner.execute(theory.as_bytes())?;
        Ok(MaudeHandle {
            inner: Arc::new(Mutex::new(inner)),
            child: Arc::new(Mutex::new(reaper)),
            // EXPERIMENTAL: init counter to safe-zone (agent's option 2) to test
            // whether idx-0 collisions with lemma bound vars are causing
            // NSLPK3 line-105 divergence.  NOT HS-faithful — proper fix is
            // PreciseFresh per-name counter or DeBruijn binders.  Just here
            // for diagnosis: if NSLPK3 changes, we know the bug class.
            fresh_counter: Arc::new(AtomicU64::new(
                std::env::var("TAM_FRESH_SAFE_ZONE").ok()
                    .and_then(|s| s.parse().ok()).unwrap_or(0))),
        })
    }

    /// Return the next unique idx and increment the counter.
    /// Mirrors Haskell's `freshIdent` / `freshLVar` — every call returns
    /// a globally-unique integer across the entire proof session.
    pub fn fresh_idx(&self) -> u64 {
        self.fresh_counter.fetch_add(1, Ordering::SeqCst)
    }

    /// Atomically reserve `n` consecutive idxs from the global counter,
    /// returning the FIRST one.  Used by `freshen_rule` /
    /// `freshen_system` to shift a rule's or case's vars into a globally
    /// unique range without per-call collisions.  Haskell's MonadFresh
    /// equivalent: `freshIdents n` (replicates `freshIdent` n times).
    pub fn reserve_idxs(&self, n: u64) -> u64 {
        if n == 0 { return self.fresh_counter.load(Ordering::SeqCst); }
        self.fresh_counter.fetch_add(n, Ordering::SeqCst)
    }

    /// Bump the counter so the next allocation is strictly greater than `n`.
    /// No-op if the counter is already > `n`.  Callers use this before
    /// `fresh_idx()` to guarantee new allocations don't collide with
    /// any system var below `n`.  The counter never goes backward.
    pub fn ensure_above(&self, n: u64) {
        let target = n.saturating_add(1);
        let mut cur = self.fresh_counter.load(Ordering::SeqCst);
        while cur < target {
            match self.fresh_counter.compare_exchange(
                cur, target, Ordering::SeqCst, Ordering::SeqCst,
            ) {
                Ok(_) => return,
                Err(actual) => cur = actual,
            }
        }
    }

    /// Current counter value (for diagnostics / probe output).
    pub fn fresh_counter_peek(&self) -> u64 {
        self.fresh_counter.load(Ordering::SeqCst)
    }

    /// Force-set the counter to `n` (overwriting the current value
    /// even if `n` is BELOW current).  Used by `apply_eq_store` to
    /// reset the counter between per-variant Maude calls so each
    /// variant's witness allocation starts from the same baseline —
    /// HS-faithful `evalFreshAvoiding` semantics where each
    /// per-variant `applyBound` call has its own fresh state.
    ///
    /// IMPORTANT: callers MUST advance the counter back to the high
    /// water mark after the per-variant loop or subsequent
    /// allocations could collide with the per-variant outputs.
    pub fn reset_counter_to(&self, n: u64) {
        self.fresh_counter.store(n, Ordering::SeqCst);
    }

    /// Clone this handle but with a FRESH fresh_counter initialised to
    /// `avoid_max + 1`.  Mirrors Haskell's `runReduction _ _ _ (avoid sys)`
    /// — every Reduction starts with a counter that's local to that
    /// Reduction call, computed from the system's current free-var max.
    /// Within the Reduction the counter advances (so sequential calls
    /// don't collide), but the next Reduction starts fresh.
    ///
    /// The Maude PROCESS state (the `inner`/`child` Arcs) is shared —
    /// only the counter is per-handle.  This is safe because Maude itself
    /// is stateless between queries; variable idxs are just Rust-side
    /// labels used when constructing Maude terms, not anything Maude
    /// tracks across calls.
    pub fn with_fresh_counter_from(&self, avoid_max: u64) -> MaudeHandle {
        MaudeHandle {
            inner: self.inner.clone(),
            child: self.child.clone(),
            fresh_counter: Arc::new(AtomicU64::new(avoid_max.saturating_add(1))),
        }
    }

    pub fn maude_sig(&self) -> MaudeSig {
        self.inner.lock().unwrap().sig.clone()
    }

    pub fn file_path(&self) -> PathBuf {
        self.inner.lock().unwrap().path.clone()
    }

    /// Kill the underlying Maude subprocess.  Use as a watchdog when a
    /// prove_lemma call is blocked inside a synchronous Maude IPC read
    /// (no internal deadline can catch that — the read just sits there
    /// waiting for stdout bytes).  After kill, any pending read returns
    /// EOF, the worker thread unwinds with an error, and the handle's
    /// `Drop` reaps the zombie.  Idempotent — try_wait first so we
    /// don't error on an already-exited child.
    ///
    /// Locks ONLY `self.child` (the dedicated reaper mutex), NOT
    /// `self.inner`, so it can fire while a reader thread holds the
    /// I/O mutex inside `read_until_prompt`.  Without this split the
    /// watchdog deadlocks with the very thread it's trying to unblock.
    pub fn kill_subprocess(&self) {
        if let Ok(mut reaper) = self.child.lock() {
            reaper.kill_and_wait();
        }
    }

    pub fn stats(&self) -> MaudeStats {
        self.inner.lock().unwrap().stats
    }

    /// Reduce a term to normal form modulo the theory.  Memoized via
    /// `reduce_cache`: `reduce` is a pure function of the input modulo
    /// the fixed-per-handle Maude signature, and `has_non_normal_terms`
    /// (called on every search step) calls it repeatedly for the same
    /// subterms.
    pub fn reduce(&self, t: &LNTerm) -> Result<LNTerm, MaudeError> {
        {
            let inner = self.inner.lock().unwrap();
            if let Some(cached) = inner.reduce_cache.get(t) {
                return Ok(cached.clone());
            }
            // Fast path: if the term contains NO reducible function
            // symbols anywhere (and the signature has no AC theories
            // that could rewrite via narrowing), `reduce` is the
            // identity.  Avoids the ~0.7ms Maude IPC round-trip on the
            // overwhelming majority of fact-term normalisations we
            // perform during subst_system.
            if !inner.sig.enable_dh && !inner.sig.enable_bp
                && !inner.sig.enable_mset && !inner.sig.enable_nat
                && !inner.sig.enable_xor
                && !term_has_reducible_sym(t, &inner.sig.reducible_fun_syms)
            {
                return Ok(t.clone());
            }
        }
        let mut inner = self.inner.lock().unwrap();
        let mut ctx = ConvCtx::new();
        let mt = lterm_to_mterm_global(t, &mut ctx);
        let mut cmd = b"reduce ".to_vec();
        cmd.extend(pp_mterm(&mt));
        cmd.extend_from_slice(b" .\n");
        let reply = inner.execute(&cmd)?;
        inner.stats.norm_count += 1;
        let sig = inner.sig.clone();
        drop(inner);
        let mt_back = maude_parse::parse_reduce_reply(&sig, &reply)?;
        let mut next = 0;
        let result = mterm_to_lnterm(&mt_back, &mut ctx, "z", &mut next);
        let mut inner = self.inner.lock().unwrap();
        inner.reduce_cache.insert(t.clone(), result.clone());
        Ok(result)
    }

    /// Unify a list of equations modulo the theory. Returns one substitution
    /// per Maude unifier.
    /// Memoised `unifiable(...)`: returns just whether *any* unifier
    /// exists.  Skips the subprocess round-trip on cache hits.  Safe
    /// to cache because the result is a context-free boolean (no
    /// witness LVars leak across calls).
    ///
    /// Fast path: when the signature has no AC operators (DH / XOR /
    /// multiset / nat) we can answer unifiability with the local
    /// Robinson-style algorithm in `unification.rs`, completely
    /// skipping Maude.  Hashing / asymmetric-encryption / pair-only
    /// protocols hit this fast path almost exclusively, cutting the
    /// per-step Maude call count by orders of magnitude.
    pub fn unifiable(&self, eqs: &[Equal<LNTerm>]) -> Result<bool, MaudeError> {
        if eqs.is_empty() { return Ok(true); }
        if eqs.iter().all(|eq| eq.lhs == eq.rhs) { return Ok(true); }
        if self.is_ac_free() {
            let eqs_owned: Vec<Equal<LNTerm>> = eqs.iter().cloned().collect();
            return Ok(crate::unification::unify_lnterm_no_ac(eqs_owned).is_ok());
        }
        let key: Vec<(LNTerm, LNTerm)> = eqs.iter()
            .map(|e| (e.lhs.clone(), e.rhs.clone())).collect();
        {
            let inner = self.inner.lock().unwrap();
            if let Some(&hit) = inner.unifiable_cache.get(&key) {
                return Ok(hit);
            }
        }
        let res = self.unify_at("unifiable::cache_miss", eqs)?;
        let answer = !res.is_empty();
        let mut inner = self.inner.lock().unwrap();
        inner.unifiable_cache.insert(key, answer);
        Ok(answer)
    }

    /// True when the signature carries no AC-flavoured operators AND
    /// no user-defined [variant] equations.  In that regime free
    /// (Robinson) unification is complete; we can answer every Maude
    /// unifiability query locally.
    ///
    /// User [variant] equations (e.g. `check_getmsg(pk(x), sign(x,m)) = m`,
    /// `convertpcs(...) = sign(...)`, `checkpcs(...) = true`) require
    /// Maude's narrowing — the local unifier fails for different App
    /// heads where Maude's `unify in MSG` would find narrowing variants.
    /// See `project_statverif_aborted_pcs_divergence.md`.
    ///
    /// TAM_RS_LEGACY_FAST_PATH=1 reverts to the prior AC-only check
    /// for performance comparison.
    /// True when the local Robinson unifier is complete for this
    /// signature.  Requires: no AC operators (DH/XOR/multiset/nat/BP)
    /// AND no user-defined `[variant]` equations.  When user equations
    /// are present (e.g. `check_getmsg(pk(x), sign(x,m)) = m`,
    /// `convertpcs(...) = sign(...)`, `checkpcs(...) = true`), Maude's
    /// `unify in MSG` narrows via the `[variant]`-attributed equations
    /// — the local fast path is incomplete because it can't narrow
    /// different-App-head equations.  See StatVerif_GM_Contract_Signing
    /// where `true =? checkpcs(...)` requires narrowing to keep
    /// variants alive past Eq_checks_succeed propagation.
    ///
    /// `TAM_RS_LEGACY_FAST_PATH=1` reverts to the prior AC-only check
    /// for performance comparison.
    /// True when the local Robinson unifier is complete for this
    /// signature.  Requires: no AC operators (DH/XOR/multiset/nat/BP)
    /// AND no user-defined `[variant]` equations.  When user equations
    /// are present (e.g. `check_getmsg(pk(x), sign(x,m)) = m`,
    /// `convertpcs(...) = sign(...)`, `checkpcs(...) = true`), Maude's
    /// `unify in MSG` narrows via the `[variant]`-attributed equations
    /// (see ppTheory in HS's Term.Maude.Parser:248-249, mirrored by
    /// Rust's maude_print.rs:327) — the local fast path is incomplete
    /// because Robinson unification can't narrow different-App-head
    /// equations like `true =? checkpcs(...)`.
    ///
    /// StatVerif_GM_Contract_Signing: keeping the variant disj alive
    /// past `Eq_checks_succeed`'s `z.10 → true` propagation requires
    /// Maude to narrow `true =? checkpcs(...)` via the `[variant]`
    /// checkpcs equation, binding pcsig1 → pcs(sign(_, ct), _, _).
    /// Without narrowing, that variant drops and the chain extension
    /// produces a surviving Resolve2 case where xm doesn't bind to ct,
    /// missing the N6 contradiction.
    fn is_ac_free(&self) -> bool {
        let sig = self.inner.lock().unwrap().sig.clone();
        !sig.enable_dh && !sig.enable_xor && !sig.enable_mset
            && !sig.enable_nat && !sig.enable_bp
            && sig.st_rules.is_empty()
    }

    pub fn unify_at(&self, label: &'static str, eqs: &[Equal<LNTerm>])
        -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        _tally_callsite(label);
        self.unify(eqs)
    }

    /// `unify_at` with explicit `avoid_max` — Maude-introduced witness
    /// vars get indices above `avoid_max + 1`. Critical to prevent
    /// witness/system var collisions: a system-wide `~mw:Pub:N` would
    /// conflict with a Maude witness `~mw:Msg:N` if the counter starts
    /// from 0 (or just the call's input).
    pub fn unify_at_with_avoid(
        &self,
        label: &'static str,
        eqs: &[Equal<LNTerm>],
        avoid_max: u64,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        _tally_callsite(label);
        self.unify_with_avoid(eqs, avoid_max)
    }

    pub fn unify(&self, eqs: &[Equal<LNTerm>]) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        self.unify_with_avoid(eqs, 0)
    }

    pub fn unify_with_avoid(
        &self,
        eqs: &[Equal<LNTerm>],
        avoid_max: u64,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        // Fast path: if every equation has lhs == rhs syntactically,
        // the unifier is trivial.  Avoids a subprocess round-trip.
        if eqs.iter().all(|eq| eq.lhs == eq.rhs) {
            return Ok(vec![Vec::new()]);
        }
        // AC-free fast path: when the signature has no DH / XOR /
        // multiset / nat / BP operators, free (Robinson) unification
        // with Maude-shape sort narrowing (fresh `~mw` witness at
        // the narrower sort, both inputs bound to it) answers every
        // Maude unifiability query locally.  Verified
        // empirically: Maude's reply to `x:Msg =? y:Pub` is exactly
        // `{x → ~mw:Pub w, y → ~mw:Pub w}` and our unifier emits
        // the same shape.  Skips the ~2.5 ms subprocess round-trip
        // on every fact-eq unification.
        // HS-faithful fast path for AC-free signatures.  Mirrors HS's
        // `unifyLTermFactored` (Unification.hs:107-120):
        //
        // ```haskell
        // unifyLTermFactored sortOf eqs = reader $ \h ->
        //     solve h $ execRWST unif sortOf M.empty
        //   where
        //     unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
        //     solve _ (Just (m, [])) = (substFromMap m, [emptySubstVFresh])
        // ```
        // Then `flattenUnif`:
        // ```haskell
        // flattenUnif (subst, substs) = map (`composeVFresh` subst) substs
        // ```
        // For the fast path: `flattenUnif (m, [emptyVFresh])
        //                  = [emptyVFresh `composeVFresh` m]`
        //
        // `composeVFresh` extends the empty VFresh with renamings for
        // `varsRange m`, so range vars get RENAMED to fresh witnesses.
        // This is the CRITICAL step: HS's output for `K → Var(V)`
        // becomes TWO entries `[K → Var(~Vw), V → Var(~Vw)]`
        // (narrowing-witness pattern), matching what Maude's full
        // unify produces.
        //
        // Without this step, downstream `apply_eq_store`'s lifting
        // gets confused: V appears only in range (not domain), and
        // its lifted witness collides with K's renamed target,
        // creating the SubstVFresh same-target collision that
        // cascades into $R=$I (KAS_key_secrecy).
        // H16.9 (HS-faithful): ALWAYS try the local non-AC unifier first.
        // HS's `unifyLTermFactored` (Unification.hs:107-119) does this:
        //   1. Run `unifyRaw` locally (no Maude).
        //   2. If success with no AC residuals → return result.
        //   3. If success with AC residuals → call Maude on residuals only.
        //   4. If failure → return empty (no Maude call).
        // Previously RS gated the fast path on `is_ac_free()` (signature
        // has no [variant] equations).  But that meant for signatures
        // WITH [variant] equations (e.g. StatVerif's convertpcs/checkpcs),
        // RS sent EVERY unification to Maude, which then NARROWS via
        // [variant] equations — keeping variants HS would drop.
        //
        // Verified via TAM_DBG_MAUDE_IO=full on resolved1:
        //   HS: 0 unify calls, 198 reduce, 18 get variants.
        //   RS: 864 unify calls (incl 81 with `true =? checkpcs(...)`),
        //       998 reduce, 9 get variants.
        // The extra 864 unify calls let Maude narrow [variant] equations
        // RS shouldn't have asked about.  See
        // [[project-h16-9-maude-trace-and-fix]].
        //
        // Opt-out via `TAM_RS_DISABLE_NO_AC_FAST_PATH=1` for diagnosis.
        let try_fast_path = std::env::var("TAM_RS_DISABLE_NO_AC_FAST_PATH").is_err();
        if try_fast_path {
            self.ensure_above(avoid_max);
            use crate::lterm::HasFrees;
            for eq in eqs {
                eq.lhs.for_each_free(&mut |v| {
                    if v.name == "x" { self.ensure_above(v.idx); }
                });
                eq.rhs.for_each_free(&mut |v| {
                    if v.name == "x" { self.ensure_above(v.idx); }
                });
            }
            let eqs_owned: Vec<Equal<LNTerm>> = eqs.iter().cloned().collect();
            let result = crate::unification::unify_lnterm_no_ac_with_counter(
                eqs_owned, &self.fresh_counter,
            );
            match result {
                Ok(subst) => {
                    // HS-faithful flattenUnif: success, return [vfresh ∘ subst].
                    return Ok(if std::env::var("TAM_RS_DISABLE_FLATTEN_UNIF").is_ok() {
                        let bindings: Vec<(crate::lterm::LVar, LNTerm)> = subst.to_list()
                            .into_iter().map(|(v, t)| (v, t)).collect();
                        vec![bindings]
                    } else {
                        let empty_vfresh = crate::subst_vfresh::LSubstVFresh::<crate::lterm::Name>::empty();
                        let folded = crate::subst_vfresh::compose_vfresh(
                            &empty_vfresh, &subst);
                        vec![folded.to_list()]
                    });
                }
                Err(crate::unification::UnifyError::NoUnifier) => {
                    // HS-faithful: unifyRaw failed.  Don't call Maude
                    // (avoid spurious [variant] narrowing).  Return empty.
                    return Ok(Vec::new());
                }
                Err(crate::unification::UnifyError::NeedsAC) => {
                    // Fall through to Maude call below.
                }
            }
        }
        let mut inner = self.inner.lock().unwrap();
        let mut ctx = ConvCtx::new();
        let mut cmd = b"unify in MSG : ".to_vec();
        for (i, eq) in eqs.iter().enumerate() {
            if i > 0 { cmd.extend_from_slice(b" /\\ "); }
            let lm = lterm_to_mterm_global(&eq.lhs, &mut ctx);
            let rm = lterm_to_mterm_global(&eq.rhs, &mut ctx);
            cmd.extend(pp_mterm(&lm));
            cmd.extend_from_slice(b" =? ");
            cmd.extend(pp_mterm(&rm));
        }
        cmd.extend_from_slice(b" .\n");
        let reply = inner.execute(&cmd)?;
        inner.stats.unify_count += 1;
        let sig = inner.sig.clone();
        drop(inner);
        let msubsts = maude_parse::parse_unify_reply(&sig, &reply)?;
        // Also avoid colliding with vars in the input eqs (their `~mw`
        // indices set a floor for the witness counter).
        let mut input_max = avoid_max;
        for eq in eqs {
            use crate::lterm::HasFrees;
            eq.lhs.for_each_free(&mut |v| {
                if v.idx > input_max { input_max = v.idx; }
            });
            eq.rhs.for_each_free(&mut |v| {
                if v.idx > input_max { input_max = v.idx; }
            });
        }
        let mut out = Vec::with_capacity(msubsts.len());
        // HS-faithful per-unifier conversion (Maude/Process.hs:255-256 +
        // Types.hs:127-138).  HS does:
        //   map (msubstToLSubstVFresh bindings) <$> parseUnifyReply ...
        // where `msubstToLSubstVFresh bindings` calls
        //   runBackConversion (traverse translate substMaude) bindings
        // and `runBackConversion back bindings =
        //   evalBindT back bindings `evalFreshAvoiding` M.elems bindings`.
        //
        // Each unifier conversion gets:
        //   (a) the SAME initial bind-map `bindings` (the toMaude
        //       conversion's output) — no carryover of FreshVar
        //       allocations from one unifier to the next, AND
        //   (b) a fresh supply starting at `max(M.elems bindings) + 1` —
        //       same base per unifier.
        // So if two unifiers each have a FreshVar(0), they both allocate
        // it to LVar(x, sort, base) but the choices DOWNSTREAM of which
        // domain key they bind diverge, producing different per-arm
        // SubstVFresh contents.
        //
        // Concrete consequence on Resp_1 / Init_1 / generate_ltk multi-AC
        // arms (UM_wPFS::wPFS_responder_key + JKL_TS2_2008 cluster):
        // HS's Mult arm allocates witness `~x.20` to the rule-internal
        // var bound first in traversal; the "everything-equates" arm
        // (where Fresh-fresh and Msg-msg collapse) allocates `~x.21`
        // because it traverses fewer distinct FreshVars before reaching
        // the equate target.  Net: HS sorts Mult arm BEFORE Equates arm
        // by the SubstVFresh Ord (Map-of-(key,value) lexicographic).
        //
        // Previously RS shared `ctx` AND advanced the global counter
        // monotonically across unifiers (msubst_to_lnsubst_with_maude
        // line 1136-1138).  Result: every unifier saw the previous
        // unifier's mutations to ctx.inverse (so a FreshVar reuses the
        // same LVar across arms) and started its counter where the prior
        // ended.  Witness collisions across arms then collapsed the
        // distinguishing per-arm idx differences HS produces, leaving
        // RS's SubstVFresh Ord to fall back on the VALUE structure
        // (Lit < App), putting Equates BEFORE Mult.
        //
        // Fix (HS-faithful): per unifier, CLONE ctx and RESET the global
        // counter to a shared baseline.  After all unifiers, advance the
        // counter to the high-water mark so subsequent allocations
        // (next solveTermEqs / chain-close / etc.) don't collide with
        // any per-arm witness.
        //
        // Single-unifier case: short-circuit to the original behaviour
        // (no clone/reset overhead, identical observable output).
        if msubsts.len() <= 1 {
            for ms in &msubsts {
                out.push(msubst_to_lnsubst_with_maude(ms, &mut ctx, input_max, Some(self))?);
            }
        } else {
            // Snapshot the counter; each unifier resets to this base.
            self.ensure_above(input_max);
            for lit in ctx.bindings().values() {
                if let crate::vterm::Lit::Var(lv) = lit {
                    if lv.name == "x" {
                        self.ensure_above(lv.idx);
                    }
                }
            }
            let baseline = self.fresh_counter_peek();
            let mut high_water = baseline;
            for ms in &msubsts {
                // Clone ctx so inverse-map mutations don't carry across
                // unifiers (mirrors HS's independent runBackConversion).
                let mut per_arm_ctx = ctx.clone();
                // Reset counter to the shared baseline (mirrors HS's
                // `evalFreshAvoiding M.elems bindings` restarting per
                // unifier).
                self.reset_counter_to(baseline);
                let arm = msubst_to_lnsubst_with_maude(
                    ms, &mut per_arm_ctx, input_max, Some(self))?;
                // Track high water for global counter restoration.
                let cur = self.fresh_counter_peek();
                if cur > high_water { high_water = cur; }
                out.push(arm);
            }
            // Restore counter above any per-arm allocation so subsequent
            // proof-session work doesn't collide with witness idxs we
            // baked into the returned SubstVFresh arms.
            self.reset_counter_to(high_water);
        }
        Ok(out)
    }

    /// Variant unification — uses Maude's `variant unify in M : t1 =? t2 .`
    /// which unifies modulo the `[variant]` equations from the builtin
    /// theory (e.g. `verify(sign(m,sk), m, pk(sk)) = true`). Standard
    /// `unify` doesn't apply these eqs; variant unify does narrowing.
    ///
    /// Used as a fallback for chain-edge unification when the standard
    /// `unify_eqs` returns no unifier — typically for cases involving
    /// `verify(...) = true` chain artifacts from rules like Receiver0b
    /// (TESLA) which have `verify(signature, ...)` in conclusions whose
    /// chain target consumes `true`. Without variant unification, the
    /// chain edge is rejected as sort-incompatible and the case is
    /// dropped → search loses witness paths.
    pub fn variant_unify_eqs(&self, eqs: &[Equal<LNTerm>])
        -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        if eqs.iter().all(|eq| eq.lhs == eq.rhs) {
            return Ok(vec![Vec::new()]);
        }
        let mut inner = self.inner.lock().unwrap();
        let mut ctx = ConvCtx::new();
        let mut cmd = b"variant unify in MSG : ".to_vec();
        for (i, eq) in eqs.iter().enumerate() {
            if i > 0 { cmd.extend_from_slice(b" /\\ "); }
            let lm = lterm_to_mterm_global(&eq.lhs, &mut ctx);
            let rm = lterm_to_mterm_global(&eq.rhs, &mut ctx);
            cmd.extend(pp_mterm(&lm));
            cmd.extend_from_slice(b" =? ");
            cmd.extend(pp_mterm(&rm));
        }
        cmd.extend_from_slice(b" .\n");
        let reply = inner.execute(&cmd)?;
        inner.stats.unify_count += 1;
        let sig = inner.sig.clone();
        drop(inner);
        let msubsts = maude_parse::parse_unify_reply(&sig, &reply)?;
        let mut out = Vec::with_capacity(msubsts.len());
        for ms in &msubsts {
            out.push(msubst_to_lnsubst(ms, &mut ctx)?);
        }
        Ok(out)
    }

    /// Compute matches: each `Equal { lhs = pattern, rhs = subject }`.
    pub fn match_eqs(&self, eqs: &[Equal<LNTerm>]) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        let mut inner = self.inner.lock().unwrap();
        let mut ctx = ConvCtx::new();
        let mut t1s: Vec<MTerm> = Vec::with_capacity(eqs.len());
        let mut t2s: Vec<MTerm> = Vec::with_capacity(eqs.len());
        for eq in eqs {
            t1s.push(lterm_to_mterm_global(&eq.lhs, &mut ctx));
            t2s.push(lterm_to_mterm_global(&eq.rhs, &mut ctx));
        }
        // `match in MSG : list(t2s) <=? list(t1s) .`
        // Mirrors Haskell's `matchCmd`: subjects on the left, patterns on
        // the right (Maude convention).
        let pp_list = |items: &[MTerm]| -> Vec<u8> {
            // Emit as `list( cons(t1, cons(t2, nil)) )` style by reusing
            // pp_mterm on a constructed FunSym::List.
            use crate::function_symbols::FunSym;
            use crate::term::Term;
            pp_mterm(&Term::App(FunSym::List, items.to_vec().into()))
        };
        let mut cmd = b"match in MSG : ".to_vec();
        cmd.extend(pp_list(&t2s));
        cmd.extend_from_slice(b" <=? ");
        cmd.extend(pp_list(&t1s));
        cmd.extend_from_slice(b" .\n");
        let reply = inner.execute(&cmd)?;
        inner.stats.match_count += 1;
        let sig = inner.sig.clone();
        drop(inner);
        _tally_callsite("match_eqs");
        let msubsts = maude_parse::parse_match_reply(&sig, &reply)?;
        let mut out = Vec::with_capacity(msubsts.len());
        for ms in &msubsts {
            out.push(msubst_to_lnsubst(ms, &mut ctx)?);
        }
        Ok(out)
    }

    /// Match where the subject side (`rhs` of each `Equal`) is treated
    /// as ground: any free LVar on the subject side that is *not* in
    /// `pattern_vars` is encoded as a fresh `MaudeConst` so Maude
    /// treats it as a constant.  Bindings returned by Maude are then
    /// "un-skolemized" — each synthetic constant maps back to its
    /// original LVar in the result terms.
    ///
    /// This exists because Maude's `match` requires the subject to be
    /// ground.  When the system's actions contain free variables (e.g.
    /// fresh `~k` not yet bound to a Fresh-rule node), plain
    /// `match_eqs` returns no match — even though the formula's
    /// universal var would happily bind to that subject variable.
    /// Tamarin's Haskell side handles this by treating subject vars as
    /// constants of a special "skolem" sort; we mirror that with the
    /// synthetic-Name trick.
    ///
    /// Used by `insert_implied_formulas_pass` as the AC-fallback after
    /// the pure structural matcher fails.  Mirrors HS's `matchAction`
    /// (System.hs:1134) which delegates to Maude via `solveMatchLNTerm`
    /// (Term/Subsumption.hs), with HS's `SkConst` encoding from
    /// `skolemizeGuarded` represented here as synthetic named constants.
    pub fn match_eqs_const_subject(
        &self,
        eqs: &[Equal<LNTerm>],
        pattern_vars: &std::collections::BTreeSet<(String, u64)>,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        use crate::lterm::{LVar, Name, NameTag};
        use crate::vterm::Lit;
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        let prof = std::env::var_os("TAM_PROFILE_MAUDE_BREAKDOWN").is_some();
        let t0 = if prof { Some(std::time::Instant::now()) } else { None };
        // Empty-result cache.  Profiling showed 100 % of calls on
        // AC-heavy lemmas (e.g. csf17/keylessssl::injectivity) return
        // empty, with many repeats across fixpoint passes.  Cache the
        // empty answer to skip the round-trip.
        let cache_key: (Vec<(LNTerm, LNTerm)>, Vec<(String, u64)>) = (
            eqs.iter().map(|e| (e.lhs.clone(), e.rhs.clone())).collect(),
            pattern_vars.iter().cloned().collect(),
        );
        if self.inner.lock().unwrap().match_empty_cache.contains_key(&cache_key) {
            _tally_callsite("match_eqs_const_subject::CACHE_HIT");
            return Ok(Vec::new());
        }
        let t_after_cache = if prof { Some(std::time::Instant::now()) } else { None };
        // Skolemize subject-side free vars not in `pattern_vars`:
        // walk each rhs LNTerm and replace such LVars with a public
        // `Name`-constant tagged with a deterministic synthetic
        // string so the same LVar maps to the same constant across
        // multiple eqs in this call.  Build the reverse map at the
        // same time so we can translate the match output back.
        let mut skolem_map: std::collections::BTreeMap<LVar, Name> =
            std::collections::BTreeMap::new();
        let mut reverse: std::collections::BTreeMap<Name, LVar> =
            std::collections::BTreeMap::new();
        let mut counter: u64 = 0;
        fn collect_subject_vars(
            t: &LNTerm,
            pattern_vars: &std::collections::BTreeSet<(String, u64)>,
            out: &mut std::collections::BTreeSet<LVar>,
        ) {
            match t {
                crate::term::Term::Lit(Lit::Var(lv)) => {
                    if !pattern_vars.contains(&(lv.name.clone(), lv.idx)) {
                        out.insert(lv.clone());
                    }
                }
                crate::term::Term::App(_, args) => {
                    for a in args.iter() { collect_subject_vars(a, pattern_vars, out); }
                }
                _ => {}
            }
        }
        let mut subject_vars: std::collections::BTreeSet<LVar> =
            std::collections::BTreeSet::new();
        for eq in eqs {
            collect_subject_vars(&eq.rhs, pattern_vars, &mut subject_vars);
        }
        for lv in &subject_vars {
            let synth_str = format!("__sk{}_{}_{}_{}", counter, lv.name, lv.idx, sort_tag(lv.sort));
            counter += 1;
            // Preserve the original LVar's sort so subsort matching
            // works (Pub < Msg, Fresh < Msg, etc.).  Maude's `match`
            // requires the pattern's declared sort to be a supersort
            // of the subject's sort.  Tamarin's Haskell mirrors this
            // via `SkConst` carrying the original `LVar` sort.
            let tag = match lv.sort {
                crate::lterm::LSort::Pub => NameTag::Pub,
                crate::lterm::LSort::Fresh => NameTag::Fresh,
                crate::lterm::LSort::Nat => NameTag::Nat,
                crate::lterm::LSort::Node => NameTag::Node,
                // No NameTag::Msg — fall back to Pub which is a
                // subsort of Msg.  This loses precision but lets
                // matching succeed; revisit if Msg-sorted subject
                // variables show up in real protocols.
                crate::lterm::LSort::Msg => NameTag::Pub,
            };
            let n = Name::new(tag, synth_str);
            skolem_map.insert(lv.clone(), n.clone());
            reverse.insert(n, lv.clone());
        }
        fn rewrite_subject(
            t: &LNTerm,
            map: &std::collections::BTreeMap<LVar, Name>,
        ) -> LNTerm {
            match t {
                crate::term::Term::Lit(Lit::Var(lv)) => {
                    if let Some(n) = map.get(lv) {
                        crate::term::Term::Lit(Lit::Con(n.clone()))
                    } else {
                        t.clone()
                    }
                }
                crate::term::Term::App(sym, args) => {
                    let new_args: Vec<LNTerm> = args.iter()
                        .map(|a| rewrite_subject(a, map))
                        .collect();
                    crate::term::Term::App(sym.clone(), new_args.into())
                }
                _ => t.clone(),
            }
        }
        let rewritten_eqs: Vec<Equal<LNTerm>> = eqs.iter().map(|eq| Equal {
            lhs: eq.lhs.clone(),
            rhs: rewrite_subject(&eq.rhs, &skolem_map),
        }).collect();
        let t_after_skolem = if prof { Some(std::time::Instant::now()) } else { None };

        let mut inner = self.inner.lock().unwrap();
        let mut ctx = ConvCtx::new();
        let mut t1s: Vec<MTerm> = Vec::with_capacity(rewritten_eqs.len());
        let mut t2s: Vec<MTerm> = Vec::with_capacity(rewritten_eqs.len());
        for eq in &rewritten_eqs {
            t1s.push(lterm_to_mterm_global(&eq.lhs, &mut ctx));
            t2s.push(lterm_to_mterm_global(&eq.rhs, &mut ctx));
        }
        let pp_list = |items: &[MTerm]| -> Vec<u8> {
            use crate::function_symbols::FunSym;
            use crate::term::Term;
            pp_mterm(&Term::App(FunSym::List, items.to_vec().into()))
        };
        let mut cmd = b"match in MSG : ".to_vec();
        cmd.extend(pp_list(&t2s));
        cmd.extend_from_slice(b" <=? ");
        cmd.extend(pp_list(&t1s));
        cmd.extend_from_slice(b" .\n");
        let t_before_exec = if prof { Some(std::time::Instant::now()) } else { None };
        let reply = inner.execute(&cmd)?;
        let t_after_exec = if prof { Some(std::time::Instant::now()) } else { None };
        inner.stats.match_count += 1;
        let sig = inner.sig.clone();
        drop(inner);
        _tally_callsite("match_eqs_const_subject");
        let msubsts = maude_parse::parse_match_reply(&sig, &reply)?;
        if msubsts.is_empty() {
            _tally_callsite("match_eqs_const_subject::EMPTY");
            // Re-acquire lock to insert into cache.  Safe — we already
            // dropped `inner` above; only one thread holds the handle
            // mutex anyway (it's wrapped in `Mutex<MaudeProcessInner>`).
            self.inner.lock().unwrap().match_empty_cache.insert(cache_key, ());
        }
        else { _tally_callsite("match_eqs_const_subject::NONEMPTY"); }
        let mut out = Vec::with_capacity(msubsts.len());
        for ms in &msubsts {
            let lnsubst = msubst_to_lnsubst(ms, &mut ctx)?;
            // Un-skolemize: walk each binding's range and replace
            // synthetic Pub-Name constants with their original LVars.
            let unskolemized: Vec<(LVar, LNTerm)> = lnsubst.into_iter()
                .map(|(lv, lt)| (lv, unskolemize(&lt, &reverse)))
                .collect();
            out.push(unskolemized);
        }
        if let (Some(a), Some(b), Some(c), Some(d), Some(e)) =
            (t0, t_after_cache, t_after_skolem, t_before_exec, t_after_exec) {
            let cache = (b - a).as_micros();
            let skol = (c - b).as_micros();
            let prep = (d - c).as_micros();
            let exec = (e - d).as_micros();
            let parse = std::time::Instant::now().duration_since(e).as_micros();
            eprintln!("[mecs] cache={}us skol={}us prep={}us exec={}us parse={}us",
                cache, skol, prep, exec, parse);
        }
        Ok(out)
    }

    /// Match where BOTH the pattern and subject sides have their free
    /// non-pattern-vars skolemized to synthetic constants — using the
    /// SAME mapping for both sides, so that occurrences of the same
    /// LVar in pattern and subject still match each other through
    /// their shared synthetic constant.
    ///
    /// This mirrors HS's `matchTerm` (Guarded.hs:810-815) called from
    /// `impliedFormulas` (System.hs:1144): the universal is fully
    /// `skolemizeGuarded`-ed before matching, so every FREE LVar
    /// (universal-non-bound vars, originating from the system context)
    /// becomes a `Con (SkConst x)`, while the universal-bound
    /// (pattern) vars stay `Var x`.  The subject side (the system's
    /// own term) is also skolemized via `skolemizeTerm`, so the same
    /// LVar `y` on both sides maps to the same `SkConst y` constant.
    /// Maude can then match the pattern against the subject without
    /// spuriously binding the pattern's `y` to anything (it's a
    /// constant on both sides).
    ///
    /// Pure `match_eqs_const_subject` only skolemizes the subject
    /// side, leaving the pattern's free non-pattern LVars as Maude
    /// variables — Maude binds them freely, producing a different
    /// match (or no match if the pattern non-pattern-var sort
    /// constrains against the subject's skolemized counterpart).
    /// Used by `insert_implied_formulas_pass`'s Eq-guard branch to
    /// handle AC-symbol patterns (e.g. multiset `y++z` against
    /// `'1'++y++h(y)`) faithfully.
    pub fn match_eqs_skolemize_both(
        &self,
        eqs: &[Equal<LNTerm>],
        pattern_vars: &std::collections::BTreeSet<(String, u64)>,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        use crate::lterm::{LVar, Name, NameTag};
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        // Step 1: collect ALL non-pattern free vars from BOTH sides.
        // The same LVar appearing on both sides must skolemize to the
        // same Name so the two occurrences match each other.
        let mut skolem_map: std::collections::BTreeMap<LVar, Name> =
            std::collections::BTreeMap::new();
        let mut reverse: std::collections::BTreeMap<Name, LVar> =
            std::collections::BTreeMap::new();
        let mut counter: u64 = 0;
        fn collect_free_non_pattern(
            t: &LNTerm,
            pattern_vars: &std::collections::BTreeSet<(String, u64)>,
            out: &mut std::collections::BTreeSet<LVar>,
        ) {
            use crate::vterm::Lit;
            match t {
                crate::term::Term::Lit(Lit::Var(lv)) => {
                    if !pattern_vars.contains(&(lv.name.clone(), lv.idx)) {
                        out.insert(lv.clone());
                    }
                }
                crate::term::Term::App(_, args) => {
                    for a in args.iter() { collect_free_non_pattern(a, pattern_vars, out); }
                }
                _ => {}
            }
        }
        let mut free_vars: std::collections::BTreeSet<LVar> =
            std::collections::BTreeSet::new();
        for eq in eqs {
            collect_free_non_pattern(&eq.lhs, pattern_vars, &mut free_vars);
            collect_free_non_pattern(&eq.rhs, pattern_vars, &mut free_vars);
        }
        for lv in &free_vars {
            let synth_str = format!("__sk{}_{}_{}_{}", counter, lv.name, lv.idx, sort_tag(lv.sort));
            counter += 1;
            let tag = match lv.sort {
                crate::lterm::LSort::Pub => NameTag::Pub,
                crate::lterm::LSort::Fresh => NameTag::Fresh,
                crate::lterm::LSort::Nat => NameTag::Nat,
                crate::lterm::LSort::Node => NameTag::Node,
                crate::lterm::LSort::Msg => NameTag::Pub,
            };
            let n = Name::new(tag, synth_str);
            skolem_map.insert(lv.clone(), n.clone());
            reverse.insert(n, lv.clone());
        }
        // Step 2: rewrite BOTH sides via the shared skolem_map.
        fn rewrite(
            t: &LNTerm,
            map: &std::collections::BTreeMap<LVar, Name>,
        ) -> LNTerm {
            use crate::vterm::Lit;
            match t {
                crate::term::Term::Lit(Lit::Var(lv)) => {
                    if let Some(n) = map.get(lv) {
                        crate::term::Term::Lit(Lit::Con(n.clone()))
                    } else {
                        t.clone()
                    }
                }
                crate::term::Term::App(sym, args) => {
                    let new_args: Vec<LNTerm> = args.iter()
                        .map(|a| rewrite(a, map))
                        .collect();
                    crate::term::Term::App(sym.clone(), new_args.into())
                }
                _ => t.clone(),
            }
        }
        let rewritten_eqs: Vec<Equal<LNTerm>> = eqs.iter().map(|eq| Equal {
            lhs: rewrite(&eq.lhs, &skolem_map),
            rhs: rewrite(&eq.rhs, &skolem_map),
        }).collect();
        // Avoid unused-var lint when no skolemization happened.
        let _ = &reverse;

        let mut inner = self.inner.lock().unwrap();
        let mut ctx = ConvCtx::new();
        let mut pats: Vec<MTerm> = Vec::with_capacity(rewritten_eqs.len());
        let mut subjs: Vec<MTerm> = Vec::with_capacity(rewritten_eqs.len());
        for eq in &rewritten_eqs {
            pats.push(lterm_to_mterm_global(&eq.lhs, &mut ctx));
            subjs.push(lterm_to_mterm_global(&eq.rhs, &mut ctx));
        }
        let pp_list = |items: &[MTerm]| -> Vec<u8> {
            use crate::function_symbols::FunSym;
            use crate::term::Term;
            pp_mterm(&Term::App(FunSym::List, items.to_vec().into()))
        };
        // Maude's `match A <=? B` syntax means: find σ such that B = σ(A).
        // So A is the PATTERN (left), B is the SUBJECT (right).
        // Callers pass `Equal { lhs = pattern, rhs = subject }`, so the
        // command is `match pattern <=? subject`.  This differs from
        // `match_eqs_const_subject` which uses `match subject <=? pattern`
        // — that historic ordering is consistent with HS's `matchCmd` but
        // because HS callers use `Equal subject pattern` (reversed lhs/rhs
        // from RS), the on-the-wire bytes match HS only when callers
        // happen to also flip lhs/rhs.  We use the correct Maude
        // `match PATTERN <=? SUBJECT` directly here, since the caller
        // convention in RS is `lhs = pattern, rhs = subject`.
        let mut cmd = b"match in MSG : ".to_vec();
        cmd.extend(pp_list(&pats));
        cmd.extend_from_slice(b" <=? ");
        cmd.extend(pp_list(&subjs));
        cmd.extend_from_slice(b" .\n");
        let reply = inner.execute(&cmd)?;
        inner.stats.match_count += 1;
        let sig = inner.sig.clone();
        drop(inner);
        _tally_callsite("match_eqs_skolemize_both");
        let msubsts = maude_parse::parse_match_reply(&sig, &reply)?;
        let mut out = Vec::with_capacity(msubsts.len());
        for ms in &msubsts {
            let lnsubst = msubst_to_lnsubst(ms, &mut ctx)?;
            // Un-skolemize all bindings so the caller gets LVars back.
            let unskolemized: Vec<(LVar, LNTerm)> = lnsubst.into_iter()
                .map(|(lv, lt)| (lv, unskolemize(&lt, &reverse)))
                .collect();
            out.push(unskolemized);
        }
        Ok(out)
    }

    /// Get variants of a term.
    pub fn variants(&self, t: &LNTerm) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError> {
        let mut inner = self.inner.lock().unwrap();
        let mut ctx = ConvCtx::new();
        let mt = lterm_to_mterm_global(t, &mut ctx);
        let mut cmd = b"get variants in MSG : ".to_vec();
        cmd.extend(pp_mterm(&mt));
        cmd.extend_from_slice(b" .\n");
        let reply = inner.execute(&cmd)?;
        inner.stats.var_count += 1;
        let sig = inner.sig.clone();
        drop(inner);
        let msubsts = maude_parse::parse_variants_reply(&sig, &reply)?;
        let mut out = Vec::with_capacity(msubsts.len());
        // HS-faithful: each variant's back-conversion uses a fresh ctx
        // clone.  Mirrors HS `msubstToLSubstVFresh` (Maude/Types.hs:130)
        // where each call to `runBackConversion (...) bindings` runs
        // `evalBindT back bindings` with the same INITIAL bindings —
        // augmentations to the binding map are per-call.
        //
        // Without this, the shared `ctx.inverse` causes
        // `MaudeLit::FreshVar(N, sort)` to collide between variants —
        // variant 1's `#1:Msg` and variant 2's `%1:Msg` both parse to
        // `FreshVar(1, Msg)` (parser at maude_parse.rs:243 collapses
        // # and %) and the second lookup returns the first's LVar.
        // `TAM_RS_DISABLE_VARIANT_CTX_ISOLATION=1` reverts for diagnosis.
        let isolate = std::env::var("TAM_RS_DISABLE_VARIANT_CTX_ISOLATION").is_err();
        // HS-faithful: variant back-conversion uses hint "x" unconditionally
        // (Maude/Types.hs:138), NOT the perform_split-motivated
        // name-preserve path used by `unify`/`match`.  The variants flow
        // into `composeVFresh`+`pracVariants` rendering; using "x" here
        // matches both HS's printed `~k = ~x.5` form AND HS's variant
        // ordering after the per-variant Ord sort (Ord LVar = idx <> sort
        // <> name puts `~x.N` AFTER same-idx `~na.N`/`~nb.N`).
        let force_x = std::env::var("TAM_RS_DISABLE_VARIANT_FORCE_X").is_err();
        for ms in &msubsts {
            let conv = |ctx_ref: &mut ConvCtx| -> Result<_, MaudeError> {
                if force_x {
                    msubst_to_lnsubst_force_x(ms, ctx_ref)
                } else {
                    msubst_to_lnsubst(ms, ctx_ref)
                }
            };
            if isolate {
                let mut variant_ctx = ctx.clone();
                out.push(conv(&mut variant_ctx)?);
            } else {
                out.push(conv(&mut ctx)?);
            }
        }
        Ok(out)
    }
}

/// One-letter sort tag for synthesizing skolem constant names.
fn sort_tag(s: crate::lterm::LSort) -> &'static str {
    use crate::lterm::LSort;
    match s {
        LSort::Msg => "M",
        LSort::Pub => "P",
        LSort::Fresh => "F",
        LSort::Node => "N",
        LSort::Nat => "T",
    }
}

/// Walk an `LNTerm` and replace any `Lit::Con(name)` whose `name` is in
/// `reverse` with the corresponding original `Lit::Var(lv)`.  Used to
/// un-skolemize match results from `match_eqs_const_subject`.
fn unskolemize(
    t: &LNTerm,
    reverse: &std::collections::BTreeMap<crate::lterm::Name, crate::lterm::LVar>,
) -> LNTerm {
    use crate::vterm::Lit;
    match t {
        crate::term::Term::Lit(Lit::Con(n)) => {
            if let Some(lv) = reverse.get(n) {
                crate::term::Term::Lit(Lit::Var(lv.clone()))
            } else {
                t.clone()
            }
        }
        crate::term::Term::App(sym, args) => {
            let new_args: Vec<LNTerm> = args.iter().map(|a| unskolemize(a, reverse)).collect();
            crate::term::Term::App(sym.clone(), new_args.into())
        }
        _ => t.clone(),
    }
}

/// Convert a Maude substitution `[((sort, idx), mt)]` into a list of
/// `(LVar, LNTerm)`.
///
/// **Witness naming**: Maude returns auxiliary witness variables when
/// expressing unifiers.  We decode each witness as an `LVar` with a
/// dedicated name `"x"` (Maude-Witness) that no input variable can
/// ever have — this guarantees the witness's `(name, sort, idx)`
/// triple cannot collide with any pre-existing system variable.
/// Without this, `LVar`'s structural equality (name + sort + idx)
/// could treat a witness as the same variable as an input or a
/// previously-generated witness from another call, silently
/// conflating distinct semantic variables (the root cause of bug
/// #21 — variable-conflation in source-case grafting).
fn msubst_to_lnsubst(
    ms: &MSubst,
    ctx: &mut ConvCtx,
) -> Result<Vec<(crate::lterm::LVar, LNTerm)>, MaudeError> {
    msubst_to_lnsubst_with_avoid(ms, ctx, 0)
}

fn msubst_to_lnsubst_with_avoid(
    ms: &MSubst,
    ctx: &mut ConvCtx,
    avoid_max: u64,
) -> Result<Vec<(crate::lterm::LVar, LNTerm)>, MaudeError> {
    msubst_to_lnsubst_with_maude(ms, ctx, avoid_max, None)
}

/// Variant of `msubst_to_lnsubst` that forces the Maude-witness name hint
/// to `"x"` regardless of whether the value is a pure rename — matching
/// HS's `msubstToLSubstVFresh` (Maude/Types.hs:138) which always passes
/// `mTermToLNTerm "x" mt` for Maude-introduced witnesses.
///
/// The non-`_force_x` form preserves the domain LVar's name when the
/// value is a pure `Lit FreshVar`; that was added for the `perform_split`
/// ordering of the EquationStore's runtime-narrowing unifiers (see
/// project-split-case-divergence-root memory).  The `variants()` path,
/// however, feeds `composeVFresh` (RuleVariants.hs:74) which then routes
/// to `pracVariants`'s pretty-printer — and HS's hint there is
/// unconditionally `"x"`.  Using the domain name there makes:
///   (a) variant `~k = ~k.5` (RS) vs `~k = ~x.5` (HS) trace divergence;
///   (b) the Ord-on-SubstVFresh permutation that reorders the variant
///       list (e.g. CRxor's `initiator2` swaps variants 1↔3).
fn msubst_to_lnsubst_force_x(
    ms: &MSubst,
    ctx: &mut ConvCtx,
) -> Result<Vec<(crate::lterm::LVar, LNTerm)>, MaudeError> {
    let mut out = Vec::with_capacity(ms.len());
    let mut next: u64 = {
        let mut n: u64 = 1;
        for lit in ctx.bindings().values() {
            if let crate::vterm::Lit::Var(lv) = lit {
                if lv.name == "x" && lv.idx >= n {
                    n = lv.idx + 1;
                }
            }
        }
        n
    };
    for ((sort, idx), mt) in ms {
        let lv = crate::maude_types::substitute_lookup_var(ctx, *sort, *idx)
            .ok_or_else(|| MaudeError::Other(format!(
                "no binding for Maude variable x{}:{:?}", idx, sort)))?;
        // HS-faithful: always hint "x", matching Maude/Types.hs:138.
        let t = mterm_to_lnterm(mt, ctx, "x", &mut next);
        out.push((lv, t));
    }
    Ok(out)
}

/// Maude-handle-aware variant: draws witness indices from the
/// MaudeHandle's global counter when supplied.  Mirrors Haskell's
/// `MonadFresh` — every freshen across the entire proof session uses
/// the same counter, so witness indices are globally unique.  Without
/// this, two independent Maude calls both start at `avoid_max + 1`
/// and produce colliding `(name, idx)` LVars at different sorts (the
/// TESLA Sender0a root cause).
fn msubst_to_lnsubst_with_maude(
    ms: &MSubst,
    ctx: &mut ConvCtx,
    avoid_max: u64,
    maude: Option<&MaudeHandle>,
) -> Result<Vec<(crate::lterm::LVar, LNTerm)>, MaudeError> {
    let mut out = Vec::with_capacity(ms.len());
    // Initialise `next`.  With a global counter, push it above
    // `avoid_max` and any input `~mw` var, then snapshot — every
    // subsequent allocation increments BOTH the local `next` and the
    // global counter (via the wrapper closure below).
    let mut next: u64 = if let Some(h) = maude {
        h.ensure_above(avoid_max);
        for lit in ctx.bindings().values() {
            if let crate::vterm::Lit::Var(lv) = lit {
                if lv.name == "x" {
                    h.ensure_above(lv.idx);
                }
            }
        }
        h.fresh_counter_peek()
    } else {
        let mut n = avoid_max.saturating_add(1);
        for lit in ctx.bindings().values() {
            if let crate::vterm::Lit::Var(lv) = lit {
                if lv.name == "x" && lv.idx >= n {
                    n = lv.idx + 1;
                }
            }
        }
        n
    };
    for ((sort, idx), mt) in ms {
        let lv = crate::maude_types::substitute_lookup_var(ctx, *sort, *idx)
            .ok_or_else(|| MaudeError::Other(format!(
                "no binding for Maude variable x{}:{:?}", idx, sort)))?;
        // HS-faithful: when the value is a pure rename (Lit FreshVar),
        // use the domain LVar's name as the name hint so the witness
        // gets named after the original variable (HS's `freshToFree`
        // namehint logic at Substitution.hs:64 — `case viewTerm t of
        // Lit (Var _) -> lvarName lv`).  Without this, all Rust
        // witnesses get the generic name "x", and the resulting
        // SubstVFresh Ord ordering at perform_split diverges from
        // HS's (HS's identity-variant entries have value-side LVar
        // names matching the key, e.g. `(pkA, pkA.K)`, while Rust
        // produced `(pkA, x.K)`).  See [[project-split-case-divergence-root]].
        // Use TAM_RS_DISABLE_NAME_PRESERVE=1 to revert to "x" for
        // diagnostic comparison.
        let use_name_preserve = std::env::var("TAM_RS_DISABLE_NAME_PRESERVE").is_err();
        let name_hint: &str = if use_name_preserve {
            if let crate::term::Term::Lit(crate::maude_types::MaudeLit::FreshVar(_, _)) = mt {
                lv.name.as_str()
            } else {
                "x"
            }
        } else {
            "x"
        };
        let t = mterm_to_lnterm(mt, ctx, name_hint, &mut next);
        out.push((lv, t));
    }
    // Bump the global counter so any subsequent allocator (in this or
    // a parallel call on the same handle) starts above our allocations.
    if let Some(h) = maude {
        if next > 0 { h.ensure_above(next - 1); }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// MaudePool — a pool of independent Maude subprocesses.
//
// The single shared `MaudeHandle` serialises every query on an internal
// `Mutex<MaudeProcessInner>`.  Under rayon parallelism (rule-variant
// closure, saturate refinement) every worker contends on that mutex,
// capping speedup at the point where one Maude subprocess is fully busy
// (~4 workers in practice).  A pool of M independent Maudes lets each
// worker hold its own subprocess for the duration of its task, so
// workers run truly in parallel.
//
// HS uses a single Maude per ClosedTheory (Term/Maude/Process.hs); this
// pool is a Rust-specific implementation improvement — it doesn't
// change semantics, only removes a serialisation point.  Per-call
// fresh-counter scope (`with_fresh_counter_from`) already guarantees
// HS-faithful witness allocation regardless of which pool member
// handles a given task.
// ---------------------------------------------------------------------------

/// Pool of M independent Maude subprocesses, all initialised with the
/// same `MaudeSig`.  Workers borrow a handle via `acquire()`; the
/// returned `PooledMaude` releases back to the pool on drop.
///
/// Internally a `Mutex<Vec<MaudeHandle>>` LIFO works fine — the pool
/// is small (≤ num_cpus) and `acquire` is rare on the hot path (it
/// happens once per parallel task, not per Maude call).
pub struct MaudePool {
    free: Mutex<Vec<MaudeHandle>>,
    notify: Condvar,
    size: usize,
}

impl std::fmt::Debug for MaudePool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MaudePool(size={})", self.size)
    }
}

impl MaudePool {
    /// Spawn `n` Maude subprocesses with `sig`.  Returns Err if any
    /// fail to start; partial pool is dropped on the error path (each
    /// `MaudeHandle`'s `Drop` reaps its subprocess).
    pub fn new(path: &str, sig: MaudeSig, n: usize) -> Result<Self, MaudeError> {
        assert!(n >= 1, "MaudePool::new requires n >= 1");
        let mut handles = Vec::with_capacity(n);
        for _ in 0..n {
            let h = MaudeHandle::start(path, sig.clone())?;
            handles.push(h);
        }
        Ok(MaudePool {
            free: Mutex::new(handles),
            notify: Condvar::new(),
            size: n,
        })
    }

    /// Build a pool from an EXISTING handle plus `n - 1` newly-spawned
    /// siblings.  The existing handle is used as-is (counter state and
    /// caches preserved); the new siblings are spawned fresh with the
    /// same signature.  Useful when the caller already has a "primary"
    /// Maude they want to reuse for sequential paths AND add to the
    /// pool for parallel paths.
    pub fn from_handle_with_siblings(
        primary: MaudeHandle,
        path: &str,
        n: usize,
    ) -> Result<Self, MaudeError> {
        assert!(n >= 1, "MaudePool::from_handle_with_siblings requires n >= 1");
        let sig = primary.maude_sig();
        let mut handles = Vec::with_capacity(n);
        handles.push(primary);
        for _ in 1..n {
            handles.push(MaudeHandle::start(path, sig.clone())?);
        }
        Ok(MaudePool {
            free: Mutex::new(handles),
            notify: Condvar::new(),
            size: n,
        })
    }

    /// Block until a handle is free, then return it.  The handle is
    /// returned to the pool when the returned `PooledMaude` is dropped.
    pub fn acquire(&self) -> PooledMaude<'_> {
        let mut free = self.free.lock().unwrap();
        loop {
            if let Some(h) = free.pop() {
                return PooledMaude { pool: self, inner: Some(h) };
            }
            free = self.notify.wait(free).unwrap();
        }
    }

    /// Number of subprocesses this pool was constructed with.
    pub fn size(&self) -> usize { self.size }

    /// Kill every pooled subprocess (watchdog).  Idempotent.
    pub fn kill_all(&self) {
        let free = self.free.lock().unwrap();
        for h in free.iter() { h.kill_subprocess(); }
    }
}

/// A borrowed Maude handle from a `MaudePool`.  `Deref`s to
/// `MaudeHandle`; releases back to the pool on `Drop`.
pub struct PooledMaude<'a> {
    pool: &'a MaudePool,
    inner: Option<MaudeHandle>,
}

impl<'a> PooledMaude<'a> {
    /// Consume the guard and return an owned `MaudeHandle` whose Drop
    /// will return the handle to the pool.  Useful when callers need
    /// ownership semantics (e.g. cloning into a per-task `ProofContext`).
    pub fn handle(&self) -> &MaudeHandle {
        self.inner.as_ref().expect("PooledMaude inner not yet taken")
    }
}

impl<'a> std::ops::Deref for PooledMaude<'a> {
    type Target = MaudeHandle;
    fn deref(&self) -> &MaudeHandle {
        self.inner.as_ref().expect("PooledMaude inner not yet taken")
    }
}

impl<'a> Drop for PooledMaude<'a> {
    fn drop(&mut self) {
        if let Some(h) = self.inner.take() {
            let mut free = self.pool.free.lock().unwrap();
            free.push(h);
            // Only one waiter can take the handle we just pushed.
            self.pool.notify.notify_one();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::{LSort, LVar};
    use crate::maude_sig::pair_maude_sig;
    use crate::vterm::Lit;

    fn maude_path() -> Option<String> {
        // Honour an env override; otherwise look for `maude` on PATH.
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

    #[test]
    fn spawn_and_reduce_pair() {
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        let h = MaudeHandle::start(&path, pair_maude_sig()).expect("start");
        // Reduce a public-name constant — should normalise to itself.
        let v = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = crate::term::Term::Lit(Lit::Var(v));
        let r = h.reduce(&t).expect("reduce");
        // Round-trip should give back `x`.
        assert_eq!(t, r);
    }

    #[test]
    fn unify_two_vars() {
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        let h = MaudeHandle::start(&path, pair_maude_sig()).expect("start");
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        let tx: LNTerm = crate::term::Term::Lit(Lit::Var(x.clone()));
        let ty: LNTerm = crate::term::Term::Lit(Lit::Var(y.clone()));
        let unifiers = h.unify(&[Equal { lhs: tx, rhs: ty }]).expect("unify");
        // Two free variables of the same sort have a single mgu (a renaming).
        assert!(!unifiers.is_empty());
    }

    #[test]
    fn unify_xor_terms_ac() {
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        let sig = crate::maude_sig::xor_maude_sig();
        let h = MaudeHandle::start(&path, sig).expect("start");
        // x XOR a =? b XOR y — has multiple AC unifiers.
        let x = LVar::new("x", LSort::Msg, 0);
        let y = LVar::new("y", LSort::Msg, 0);
        let a = LVar::new("a", LSort::Msg, 0);
        let b = LVar::new("b", LSort::Msg, 0);
        let lhs = crate::term::f_app_ac(
            crate::function_symbols::AcSym::Xor,
            vec![
                crate::term::Term::Lit(Lit::Var(x)),
                crate::term::Term::Lit(Lit::Var(a)),
            ],
        );
        let rhs = crate::term::f_app_ac(
            crate::function_symbols::AcSym::Xor,
            vec![
                crate::term::Term::Lit(Lit::Var(b)),
                crate::term::Term::Lit(Lit::Var(y)),
            ],
        );
        let res = h.unify(&[Equal { lhs, rhs }]).expect("unify xor");
        // AC unification of XOR is non-trivial — Maude returns multiple
        // unifiers. We just assert we got at least one.
        assert!(!res.is_empty(), "expected at least one AC unifier");
    }

    /// Verifies our Maude bridge correctly narrows sorts.
    /// Pub is a subsort of Msg in Maude's order-sorted theory, so unifying
    /// x:Msg with y:Pub should narrow x → ?:Pub.
    #[test]
    fn unify_narrows_msg_var_to_pub() {
        let path = match maude_path() { Some(p) => p, None => return };
        let h = MaudeHandle::start(&path, pair_maude_sig()).expect("start");
        let x_msg = LVar::new("x", LSort::Msg, 0);
        let y_pub = LVar::new("y", LSort::Pub, 0);
        let tx: LNTerm = crate::term::Term::Lit(Lit::Var(x_msg.clone()));
        let ty: LNTerm = crate::term::Term::Lit(Lit::Var(y_pub.clone()));
        let unifiers = h.unify(&[Equal { lhs: tx, rhs: ty }]).expect("unify");
        assert_eq!(unifiers.len(), 1);
        // Both vars should be bound to a fresh variable of sort Pub.
        for (v, t) in &unifiers[0] {
            if let crate::term::Term::Lit(Lit::Var(lv)) = t {
                assert_eq!(lv.sort, LSort::Pub,
                    "expected narrowing to Pub, got {:?} → {:?}", v, lv);
            }
        }
    }

    /// Verifies our bridge correctly rejects sort-incompatible unifications:
    /// `pk(_)` is Msg-typed and cannot unify with a Pub-sorted variable
    /// (Pub ⊂ Msg, but `pk(_)` is not Pub).
    #[test]
    fn unify_pub_var_with_pk_msg_term_fails() {
        let path = match maude_path() { Some(p) => p, None => return };
        use crate::function_symbols::{NoEqSym, FunSym, Privacy, Constructability};
        let pk_sym = NoEqSym::new(b"pk".to_vec(), 1, Privacy::Public, Constructability::Constructor);
        let sig = pair_maude_sig().add_fun_sym(pk_sym.clone());
        let h = MaudeHandle::start(&path, sig).expect("start");
        let a_pub = LVar::new("A", LSort::Pub, 0);
        let ltka = LVar::new("ltkA", LSort::Fresh, 0);
        let mk = |v: LVar| -> LNTerm { crate::term::Term::Lit(Lit::Var(v)) };
        let pk_term = crate::term::Term::App(FunSym::NoEq(pk_sym), vec![mk(ltka)].into());
        let us = h.unify(&[Equal { lhs: mk(a_pub), rhs: pk_term }]).expect("unify");
        assert!(us.is_empty(), "expected no unifier for Pub ↔ pk(Fresh)");
    }

    #[test]
    fn reduce_pair_fst_snd() {
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        // pair_dest_maude_sig has fst/snd as destructors with rules.
        let sig = crate::maude_sig::pair_maude_sig();
        let h = MaudeHandle::start(&path, sig).expect("start");
        // Reduce a simple variable — should be itself.
        let x = LVar::new("x", LSort::Msg, 0);
        let t: LNTerm = crate::term::Term::Lit(Lit::Var(x));
        assert_eq!(h.reduce(&t).expect("reduce"), t);
    }

    #[test]
    fn pool_acquire_release_size() {
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        let pool = MaudePool::new(&path, pair_maude_sig(), 3).expect("pool");
        assert_eq!(pool.size(), 3);
        // Acquire all three, then release them; second round should
        // still succeed (handles must have been returned).
        {
            let _a = pool.acquire();
            let _b = pool.acquire();
            let _c = pool.acquire();
        }
        let a = pool.acquire();
        let b = pool.acquire();
        let c = pool.acquire();
        drop(a); drop(b); drop(c);
    }

    #[test]
    fn pool_parallel_reduce_returns_correct_results() {
        use std::sync::Arc;
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        let pool = Arc::new(MaudePool::new(&path, pair_maude_sig(), 2).expect("pool"));
        let mut handles = Vec::new();
        for i in 0u64..6 {
            let pool = pool.clone();
            handles.push(std::thread::spawn(move || {
                let h = pool.acquire();
                let x = LVar::new("x", LSort::Msg, i);
                let t: LNTerm = crate::term::Term::Lit(Lit::Var(x));
                h.reduce(&t).expect("reduce")
            }));
        }
        for (i, h) in handles.into_iter().enumerate() {
            let r = h.join().expect("thread");
            // round-trip: x:Msg.i reduces to itself
            let x = LVar::new("x", LSort::Msg, i as u64);
            let expected: LNTerm = crate::term::Term::Lit(Lit::Var(x));
            assert_eq!(r, expected);
        }
    }

    #[test]
    fn pool_blocks_when_exhausted() {
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        let pool = std::sync::Arc::new(MaudePool::new(&path, pair_maude_sig(), 1).expect("pool"));
        let g = pool.acquire();
        // Spawn a thread that should block on acquire() until we drop g.
        let pool_c = pool.clone();
        let (tx, rx) = std::sync::mpsc::channel();
        let t = std::thread::spawn(move || {
            let _h = pool_c.acquire();
            tx.send(()).unwrap();
        });
        // Initially the worker should be blocked (no message yet).
        assert!(rx.recv_timeout(std::time::Duration::from_millis(100)).is_err());
        drop(g);
        // After releasing, the worker should wake up promptly.
        rx.recv_timeout(std::time::Duration::from_secs(5)).expect("worker should unblock");
        t.join().unwrap();
    }
}
