//! Port of `Term.Maude.Process` — a subprocess driver for Maude.
//!
//! Spawns `maude -interactive -no-tecla -no-banner -no-wrap -batch`,
//! feeds it a `fmod MSG ... endfm` module describing the term algebra,
//! and exposes `unify`, `match`, `variants`, and `reduce` operations.
//!
//! The protocol is line-oriented: every command ends with `.\n` and
//! Maude's response ends with the prompt `Maude> `.

use std::io::{Read, Write};
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
        = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
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

/// Cached `TAM_DBG_MAUDE_IO` / `TAM_DBG_MAUDE_IO_FILTER` configuration.
/// Both env vars are constant for the process; `execute()` is the single
/// chokepoint for every Maude IPC round-trip, so read them once instead
/// of per call.  Returns `(trace_enabled, trace_full, filter)` preserving
/// the exact 3-way `TAM_DBG_MAUDE_IO` semantics (`""` / `"full"` / other)
/// and the substring `filter` value.
fn maude_io_trace_config() -> &'static (bool, bool, String) {
    static CFG: std::sync::OnceLock<(bool, bool, String)> = std::sync::OnceLock::new();
    CFG.get_or_init(|| {
        let trace_mode = std::env::var("TAM_DBG_MAUDE_IO").unwrap_or_default();
        let trace_enabled = !trace_mode.is_empty();
        let trace_full = trace_mode == "full";
        let filter = std::env::var("TAM_DBG_MAUDE_IO_FILTER").unwrap_or_default();
        (trace_enabled, trace_full, filter)
    })
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
            // The prompt can only straddle the boundary between bytes read
            // before this iteration and the newly-appended chunk, so scan
            // only `buf[start..]` (keeping `PROMPT.len()-1` bytes of overlap)
            // instead of re-scanning the whole accumulated buffer each read
            // — O(N) total rather than O(N^2).  Result is identical because
            // `find_subseq` returns the first match and earlier prefixes
            // were already scanned (and rejected) on prior iterations.
            let start = buf.len().saturating_sub(PROMPT.len() - 1);
            let n = self.stdout.read(&mut tmp)?;
            if n == 0 {
                return Err(MaudeError::Other(
                    "Maude exited unexpectedly".into()));
            }
            buf.extend_from_slice(&tmp[..n]);
            if let Some(rel) = find_subseq(&buf[start..], PROMPT) {
                let pos = start + rel;
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
        let &(trace_enabled, trace_full, ref filter) = maude_io_trace_config();
        // Only materialise the full command string when something will
        // actually read it — i.e. tracing is on, or a non-empty filter
        // needs the `contains` check.  In the common untraced path this
        // skips a heap allocation + byte-for-byte copy of the command.
        let cmd_keep = if trace_enabled || !filter.is_empty() {
            let cmd_str_full: String = cmd.iter().map(|&b| b as char).collect();
            let keep = filter.is_empty() || cmd_str_full.contains(filter.as_str());
            if trace_enabled && keep {
                let cmd_str = if trace_full { cmd_str_full }
                    else { cmd_str_full.chars().take(200).collect() };
                eprintln!("[maude>] {}", cmd_str.replace('\n', "\\n"));
            }
            keep
        } else {
            true
        };
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
        // stderr: INHERIT, not pipe.  HS uses `runInteractiveCommand`
        // (System.Process) at Process.hs:109, which opens a PIPE for
        // stderr too — the returned `herr` (captured into the `MP` record
        // at Process.hs:115) is a real stderr pipe handle.  HS simply
        // never reads/drains that pipe.  We deliberately INHERIT stderr
        // instead, because an undrained stderr pipe would deadlock us:
        // if we pipe stderr but never drain it,
        // Maude eventually fills the ~64KB stderr pipe buffer (e.g.
        // bilinear-pairing examples like `ake/bilinear/Scott.spthy`
        // trigger Maude diagnostic chatter), then blocks in `write(2)`
        // on stderr.  Our reader thread is meanwhile blocked in
        // `read(2)` on stdout waiting for the prompt that Maude will
        // never reach.  Classic pipe-buffer deadlock — verified on
        // Scott.spthy::key_secrecy where the RS process sat at 0% CPU
        // for 55s of a 60s timeout while Maude's wchan was
        // `anon_pipe_write` and the RS reader was `anon_pipe_read`.
        let mut child = Command::new(maude_path)
            .arg("-interactive")
            .arg("-no-tecla")
            .arg("-no-banner")
            .arg("-no-wrap")
            .arg("-batch")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
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
            // The global fresh counter starts at 0 (HS-faithful: HS's
            // `MonadFresh` global counter starts at 0).
            fresh_counter: Arc::new(AtomicU64::new(0)),
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
            let eqs_owned: Vec<Equal<LNTerm>> = eqs.to_vec();
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

    /// True when the local Robinson unifier is complete for this
    /// signature, so every Maude unifiability query can be answered
    /// locally.  Requires: no AC operators (DH/XOR/multiset/nat/BP)
    /// AND no user-defined `[variant]` equations (`sig.st_rules` empty).
    ///
    /// When user equations are present (e.g.
    /// `check_getmsg(pk(x), sign(x,m)) = m`, `convertpcs(...) = sign(...)`,
    /// `checkpcs(...) = true`), Maude's `unify in MSG` narrows via the
    /// `[variant]`-attributed equations (see ppTheory in HS's
    /// Term.Maude.Parser, mirrored by Rust's maude_print.rs) — the local
    /// fast path is incomplete because Robinson unification can't narrow
    /// different-App-head equations like `true =? checkpcs(...)`.
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
        // NOTE: no syntactic-equality fast path here.  HS's `unifyRaw`
        // (Unification.hs:265-270) delays AC-headed and C-headed pairs
        // to Maude UNCONDITIONALLY — even when lhs == rhs syntactically.
        // Maude's complete unifier set for a self-equal AC/C term is
        // NOT just the identity: e.g. `em(hp(a),hp(b)) =? em(hp(a),hp(b))`
        // (C/comm) also has the "diagonal" unifier a=b, and
        // `mult(x,y) =? mult(x,y)` has the x=y merge.  RS previously
        // short-circuited `all(lhs == rhs)` to `[identity]`, dropping
        // these diagonal arms — observable on Scott::key_secrecy where
        // HS's refineSubst fan-out at /case_2/Init_2/Init_1/c_kdf/
        // split_case_3 yields 4 unifier arms for em/Mult-headed source
        // cases (the surviving Resp_1_case_01/06/09/10 arms) while RS
        // yielded only 2.  Self-equal NON-AC eq sets still avoid the
        // Maude round-trip via the local `unify_lnterm_no_ac_with_counter`
        // fast path below (HS-faithful: unifyRaw solves them locally).
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
        // RS shouldn't have asked about.
        {
            let eqs_owned: Vec<Equal<LNTerm>> = eqs.to_vec();
            let result = crate::unification::unify_lnterm_no_ac_with_counter(
                eqs_owned, &self.fresh_counter,
            );
            match result {
                Ok(subst) => {
                    // HS-faithful flattenUnif: success, return [vfresh ∘ subst].
                    let empty_vfresh = crate::subst_vfresh::LSubstVFresh::<crate::lterm::Name>::empty();
                    let folded = crate::subst_vfresh::compose_vfresh(
                        &empty_vfresh, &subst);
                    return Ok(vec![folded.to_list()]);
                }
                Err(crate::unification::UnifyError::NoUnifier) => {
                    // HS-faithful: unifyRaw failed.  Don't call Maude
                    // (avoid spurious [variant] narrowing).  Return empty.
                    return Ok(Vec::new());
                }
                Err(crate::unification::UnifyError::NeedsAC) => {
                    // Fall through to the Maude call below.
                    //
                    // Counter bookkeeping lives HERE (not before the
                    // local unify attempt): `unify_lnterm_no_ac_with_counter`
                    // does NOT read the global fresh counter (unification.rs:
                    // `_counter` is unused — no witnesses are minted), and the
                    // two terminating branches above return via `compose_vfresh`
                    // / empty, neither of which reads the counter.  So the
                    // counter only needs raising on the AC fall-through, where
                    // the Maude witness allocator consumes it.  Floor it above
                    // `avoid_max` and any input `~mw` (`name == "x"`) var here;
                    // the residual-only `input_max` walk below additionally
                    // covers the AC residuals' vars.
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
                }
            }
        }
        // HS-faithful `unifyLTermFactored` (Unification.hs:107-120):
        //
        //   unif = sequence [ unifyRaw t p | Equal t p <- eqs ]
        //   solve h (Just (m, leqs)) =
        //       (subst, unifyViaMaude h sortOf $ map (applyVTerm subst <$>) leqs)
        //     where subst = substFromMap m
        //
        // i.e. run the LOCAL non-AC unifier first to extract a non-AC
        // substitution `m` and the residual AC equations `leqs`, then send
        // ONLY the residuals (with `m` applied) to Maude.  Finally
        // `flattenUnif (subst, substs) = map (`composeVFresh` subst) substs`
        // (Unification.hs:144-147) composes each Maude arm with `subst = m`.
        //
        // Previously RS sent the FULL `eqs` to Maude and composed each arm
        // with the EMPTY substitution.  That left `m`'s non-AC bindings
        // (e.g. `X.18 → em(...)`, `~ey.16 → ~ey.11`) to be re-derived by
        // Maude per arm, with witness idxs allocated against the full input
        // var set rather than just the AC residual's vars.
        let (factored_m, residual_eqs): (
            crate::subst::Subst<crate::lterm::Name, crate::lterm::LVar>,
            Vec<Equal<LNTerm>>,
        ) = match crate::unification::unify_lnterm_factored(
            eqs.to_vec(),
        ) {
            Some((m, leqs)) => (m, leqs),
            // unifyRaw failed during factoring → no unifier (HS `solve _
            // Nothing = (emptySubst, [])` → flattenUnif maps over []).
            None => return Ok(Vec::new()),
        };
        // If factoring already solved everything (no AC residual), HS returns
        // `(substFromMap m, [emptySubstVFresh])`; flattenUnif then yields
        // `[emptyVFresh `composeVFresh` m]`.  Mirror that without a Maude
        // round-trip.
        if residual_eqs.is_empty() {
            let empty_vfresh =
                crate::subst_vfresh::LSubstVFresh::<crate::lterm::Name>::empty();
            let composed = crate::subst_vfresh::compose_vfresh(&empty_vfresh, &factored_m);
            return Ok(vec![composed.to_list()]);
        }
        // The equations actually sent to Maude are the AC residuals.
        let maude_eqs: &[Equal<LNTerm>] = &residual_eqs;
        let mut inner = self.inner.lock().unwrap();
        let mut ctx = ConvCtx::new();
        let mut cmd = b"unify in MSG : ".to_vec();
        for (i, eq) in maude_eqs.iter().enumerate() {
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
        for eq in maude_eqs {
            use crate::lterm::HasFrees;
            eq.lhs.for_each_free(&mut |v| {
                if v.idx > input_max { input_max = v.idx; }
            });
            eq.rhs.for_each_free(&mut |v| {
                if v.idx > input_max { input_max = v.idx; }
            });
        }
        let mut out = Vec::with_capacity(msubsts.len());
        // HS-faithful per-unifier conversion (Maude/Process.hs:218 +
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
        // HS-faithful `removeRenamings` (Maude/Types.hs:130): HS's
        // `msubstToLSubstVFresh bindings substMaude` ends with
        // `removeRenamings $ substFromListVFresh slist` — drops every
        // entry whose image is just a Var with no role elsewhere in
        // the substitution (`isRenamedVar` in SubstVFresh.hs:140-145).
        // RS's `msubst_to_lnsubst_with_maude` returns the raw slist
        // without this filter, so trivial rename entries leak into the
        // disjunction's substs.  At Scott's
        // `/case_2/Init_2/Init_1/c_kdf/split_case_3` these renames
        // become extra node-id bindings that drive `setNodes` collisions
        // → 14 spurious `shape_mismatch` drops.
        out = out.into_iter()
            .map(|arm| {
                let vfresh = crate::subst_vfresh::LSubstVFresh::
                    <crate::lterm::Name>::from_list(arm);
                vfresh.remove_renamings().to_list()
            })
            .collect();
        // HS-faithful `flattenUnif (subst, substs) = map (composeVFresh _ subst) substs`
        // (Unification.hs:147).  For the AC path, RS sends the FULL eqs to
        // Maude (HS sends only AC residuals after applying local non-AC subst),
        // so `subst` from the local non-AC factored unification is effectively
        // empty here.  We then need `composeVFresh empty_subst arm` — which
        // RENAMES the witnesses (the arm's range vars) via HS's
        // `freshToFreeAvoidingFast` uniform shift seeded by
        // `succ (max idx in (s2=empty, s1_0=arm) domain)`.  Without this step,
        // RS preserves the raw Maude-allocated witness idxs (e.g. ~x.39..~x.43
        // because the per-call counter was advanced via `ensure_above(input_max)`
        // to clear the input vars), while HS sees witnesses re-based to
        // `~x.10..~x.14` (small idxs above just the arm's domain).
        //
        // Concrete divergence (LAK06::noninjectiveagreementTAG):
        //   - HS apply_eq_store call producing 9 substs uses witness idxs
        //     ~x.10..~x.14 for first applyBound batch (6 unifiers) and
        //     ~x.27..~x.31 for second batch (1 unifier with different eqs).
        //   - RS produces the same 9 substs but with witnesses ~x.39..~x.43
        //     uniformly — because the local Maude counter was ensure_above
        //     to clear x.38 in the input eqs.
        //   - The resulting BTreeSet sort order of these alpha-equivalent
        //     substs DIFFERS, flipping the perform_split case order
        //     downstream → different `case_xor` chosen at split_case_N.
        //
        // HS `flattenUnif (subst, substs) = map (`composeVFresh` subst) substs`
        // (Unification.hs:147) composes each Maude arm with `subst = m`, the
        // non-AC factored substitution.  Previously RS composed with the
        // empty substitution because it sent the full eqs to Maude; now that
        // we factor and send only AC residuals, `factored_m` carries the
        // non-AC bindings and MUST be the second argument to composeVFresh.
        let renamed: Vec<Vec<(crate::lterm::LVar, LNTerm)>> = out.into_iter().map(|arm| {
            let arm_vfresh = crate::subst_vfresh::LSubstVFresh::<crate::lterm::Name>::from_list(arm);
            let composed = crate::subst_vfresh::compose_vfresh(&arm_vfresh, &factored_m);
            composed.to_list()
        }).collect();
        Ok(renamed)
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
    ///
    /// NOTE: this is a public-API entry point for the variant-unification
    /// path that the (not-yet-ported) `Term.Narrowing.*` machinery needs
    /// (see the crate-level "Not yet ported" note in `lib.rs`).  It has no
    /// in-crate caller today and is intentionally kept wired so the entry
    /// point is ready when narrowing lands; do not remove it as "dead code"
    /// without also dropping the `lib.rs` doc reference.
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
            // VFresh (unify) path → canonical domain sort.
            out.push(msubst_to_lnsubst_unify(ms, &mut ctx)?);
        }
        Ok(out)
    }

    /// Compute AC matchers for a batch of `(subject, pattern)` problems.
    ///
    /// **Convention — faithful to Haskell.** Each `Equal { lhs, rhs }`
    /// has `lhs = subject` (term to be matched, treated ground) and
    /// `rhs = pattern` (vars bind). This mirrors HS exactly:
    /// `matchWith t p = DelayedMatches [(t, p)]` is `(subject, pattern)`
    /// (`Term/Rewriting/Definitions.hs:90-93`), and `matchViaMaude`
    /// turns each pair into `Equal subject pattern` via
    /// `uncurry Equal <$> ms` (`Term/Maude/Process.hs:246`). The
    /// emitted Maude command is then `match PATTERN <=? SUBJECT`,
    /// i.e. `matchCmd`'s `ppTerms t2s <> " <=? " <> ppTerms t1s` where
    /// `(t1s, t2s) = unzip [(a, b) | Equal a b <- eqs]` so `t2s = b =
    /// pattern` lands on Maude's LEFT (pattern slot) and `t1s = a =
    /// subject` on the RIGHT (subject slot) — `Process.hs:227-229`.
    ///
    /// Maude's `match A <=? B` binds vars in **A (PATTERN, left)** and
    /// treats **B (SUBJECT, right)** as ground (empirically confirmed;
    /// see the `match_eqs_const_subject` fix in eadeb1c4 and the twin
    /// fix to this function). So pattern must go LEFT — which is why
    /// `pp_list(&pats)` (= `t2s` = each `eq.rhs`) is emitted first.
    ///
    /// NOTE the opposite field order from `Equal` as used by callers
    /// that pass `Equal { lhs = pattern, rhs = subject }`: HS's `Equal`
    /// holds `(subject, pattern)`, and so does this routine. Callers
    /// constructed from `matchFact`/`matchWith` (e.g. `sources.rs`,
    /// `subsumption.rs::compare_term_subs`) MUST therefore put the
    /// subject in `lhs` and the pattern in `rhs`.
    pub fn match_eqs(&self, eqs: &[Equal<LNTerm>]) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        if eqs.is_empty() {
            return Ok(vec![Vec::new()]);
        }
        let mut inner = self.inner.lock().unwrap();
        let mut ctx = ConvCtx::new();
        // `subjs` ← each `eq.lhs` (HS `t1s = a = subject`);
        // `pats`  ← each `eq.rhs` (HS `t2s = b = pattern`).
        let mut subjs: Vec<MTerm> = Vec::with_capacity(eqs.len());
        let mut pats: Vec<MTerm> = Vec::with_capacity(eqs.len());
        for eq in eqs {
            subjs.push(lterm_to_mterm_global(&eq.lhs, &mut ctx));
            pats.push(lterm_to_mterm_global(&eq.rhs, &mut ctx));
        }
        // `match in MSG : list(pats) <=? list(subjs) .`
        // Mirrors HS `matchCmd` (`Process.hs:227-229`): PATTERN on the
        // left (vars bind), SUBJECT on the right (ground).
        let pp_list = |items: &[MTerm]| -> Vec<u8> {
            // Emit as `list( cons(t1, cons(t2, nil)) )` style by reusing
            // pp_mterm on a constructed FunSym::List.
            use crate::function_symbols::FunSym;
            use crate::term::Term;
            pp_mterm(&Term::App(FunSym::List, items.to_vec().into()))
        };
        let mut cmd = b"match in MSG : ".to_vec();
        cmd.extend(pp_list(&pats));
        cmd.extend_from_slice(b" <=? ");
        cmd.extend(pp_list(&subjs));
        cmd.extend_from_slice(b" .\n");
        if std::env::var_os("TAM_DBG_MATCH_EQS_RAW").is_some() {
            eprintln!("[match_eqs RAW] {}", String::from_utf8_lossy(&cmd).trim_end());
        }
        let reply = inner.execute(&cmd)?;
        inner.stats.match_count += 1;
        let sig = inner.sig.clone();
        drop(inner);
        if std::env::var_os("TAM_DBG_MATCH_EQS_RAW").is_some() {
            eprintln!("[match_eqs REPLY] {}", String::from_utf8_lossy(&reply).trim_end());
        }
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
    /// NOT currently wired into any production path: its former
    /// `insert_implied_formulas_pass` AC-fallback use was replaced by
    /// `match_eqs_skolemize_both` (which skolemizes BOTH sides) to fix a
    /// DH/STS over-match regression; the only remaining callers are this
    /// file's in-module tests.  Kept because it mirrors a real HS
    /// distinction: HS's `matchAction`/`matchTerm` (Guarded.hs:803-815)
    /// delegate to Maude via `solveMatchLTerm`, with HS's `SkConst`
    /// encoding from `skolemizeGuarded` represented here as synthetic
    /// named constants.
    pub fn match_eqs_const_subject(
        &self,
        eqs: &[Equal<LNTerm>],
        pattern_vars: &std::collections::BTreeSet<(String, u64)>,
    ) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        use crate::lterm::{LVar, Name};
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
            let n = skolem_name(counter, lv);
            counter += 1;
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
        // Maude's `match A <=? B` finds σ with `B == σ(A)`: A is the
        // PATTERN (whose vars get bound), B is the SUBJECT (treated as
        // ground).  Callers pass `Equal { lhs = pattern, rhs = subject }`
        // (see `match_atom_via_maude` in simplify.rs, which builds the
        // guard-fact pattern as `lhs` and the system action term as
        // `rhs`), and this routine already skolemizes the SUBJECT side
        // (`eq.rhs`) into ground constants above.  So the command must be
        //   match  <pattern = t1s = lhs>  <=?  <subject = t2s = rhs>.
        //
        // PREVIOUSLY this emitted the two sides SWAPPED — `match t2s <=?
        // t1s` — which placed the (ground, skolemized) subject in the
        // pattern slot and the pattern (with its universal-bound vars) in
        // the subject slot.  Maude then treated the pattern's vars as
        // opaque constants, so any AC match where a pattern var must
        // ABSORB a sub-multiset failed: e.g. matching the guard
        //   BB_Cs(BB, <'codes', codeOther ++ <cp(..),cp(..)>>)
        // against a system action with a 3-element multiset
        //   <'codes', code2 ++ x ++ <cp(..),cp(..)>>
        // needs `codeOther → code2 ++ x`, which Maude only does when
        // `codeOther` sits on the PATTERN side.  With the swap it
        // returned "No match", `insertImpliedFormulas` never derived
        // gfalse for that case, and alethea `indivVerif` was FALSIFIED
        // (false attack) where Haskell VERIFIES it.  HS sends
        // `match pattern <=? subject` (Term/Maude.hs matchCmd); we now do
        // the same.  Sibling `match_eqs_skolemize_both` already had the
        // correct order.
        let mut cmd = b"match in MSG : ".to_vec();
        cmd.extend(pp_list(&t1s));
        cmd.extend_from_slice(b" <=? ");
        cmd.extend(pp_list(&t2s));
        cmd.extend_from_slice(b" .\n");
        let t_before_exec = if prof { Some(std::time::Instant::now()) } else { None };
        let reply = inner.execute(&cmd)?;
        if std::env::var_os("TAM_DBG_MECS_RAW").is_some() {
            eprintln!("[MECS_RAW] cmd={}", String::from_utf8_lossy(&cmd));
            eprintln!("[MECS_RAW] reply={}", String::from_utf8_lossy(&reply));
        }
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
        use crate::lterm::{LVar, Name};
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
            let n = skolem_name(counter, lv);
            counter += 1;
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
        // Callers of THIS routine pass `Equal { lhs = pattern, rhs =
        // subject }`, so the command is `match pattern(lhs) <=?
        // subject(rhs)`.  CONVENTION WARNING: `match_eqs_const_subject`
        // (post-eadeb1c4) ALSO uses `Equal { lhs = pattern, rhs =
        // subject }` and emits `match pattern <=? subject` — same as
        // here.  But the plain `match_eqs` uses the OPPOSITE `Equal`
        // field order (`lhs = subject, rhs = pattern`, faithful to HS's
        // `Equal a b = Equal subject pattern`); it still emits
        // `match PATTERN <=? SUBJECT` on the wire, just sourced from the
        // flipped fields.  So all three matchers emit pattern-on-the-left,
        // which is what Maude requires (vars bind in the left operand).
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
        // `FreshVar(1, Msg)` (parser at maude_parse.rs:293-297 collapses
        // # and %) and the second lookup returns the first's LVar.
        //
        // HS-faithful: variant back-conversion uses hint "x" unconditionally
        // (Maude/Types.hs:138), NOT the perform_split-motivated
        // name-preserve path used by `unify`/`match`.  The variants flow
        // into `composeVFresh`+`pracVariants` rendering; using "x" here
        // matches both HS's printed `~k = ~x.5` form AND HS's variant
        // ordering after the per-variant Ord sort (Ord LVar = idx <> sort
        // <> name puts `~x.N` AFTER same-idx `~na.N`/`~nb.N`).
        for ms in &msubsts {
            let mut variant_ctx = ctx.clone();
            out.push(msubst_to_lnsubst_force_x(ms, &mut variant_ctx)?);
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

/// Build the synthetic skolem-constant `Name` for a free/subject `LVar`
/// `lv`, using `counter` to keep the id unique across one match call.
///
/// The constant must round-trip through Maude with the SAME order-sorted
/// behaviour HS gives a `SkConst`, whose sort is `lvarSort v`
/// (Guarded.hs:805-808) — i.e. the variable's *own* sort, which may be
/// `Msg`.  Maude's `match A <=? B` requires the pattern's declared sort
/// to be a supersort of the subject's, so encoding a `Msg`-sorted
/// subject variable as `Pub` (a strict subsort of `Msg`) would let it
/// match a `Msg` pattern position that HS would reject — an over-match
/// that can change `--prove` results.
///
/// `NameTag` has no `Msg` variant, and adding one would break the many
/// exhaustive `match`es on it across other crates.  Instead we carry a
/// `Msg`-sorted skolem as a `NameTag::Pub` `Name` whose id begins with
/// `maude_types::SKOLEM_MSG_PREFIX`; `maude_types::sort_of_name`
/// recognises that sentinel and reports `LSort::Msg`, so the emitted
/// Maude constant is `c(i)` (op `c : Nat -> Msg`) rather than `p(i)`.
/// For every other sort the matching `NameTag` already yields the right
/// Maude sort directly.
fn skolem_name(counter: u64, lv: &crate::lterm::LVar) -> crate::lterm::Name {
    use crate::lterm::{LSort, Name, NameTag};
    match lv.sort {
        LSort::Msg => {
            // Sentinel-prefixed id; the rest mirrors the historical
            // synthetic-string layout so distinct LVars stay distinct.
            let id = format!(
                "{}{}_{}_{}_{}",
                crate::maude_types::SKOLEM_MSG_PREFIX,
                counter, lv.name, lv.idx, sort_tag(lv.sort)
            );
            Name::new(NameTag::Pub, id)
        }
        sort => {
            let tag = match sort {
                LSort::Pub => NameTag::Pub,
                LSort::Fresh => NameTag::Fresh,
                LSort::Nat => NameTag::Nat,
                LSort::Node => NameTag::Node,
                LSort::Msg => unreachable!(),
            };
            let id = format!("__sk{}_{}_{}_{}", counter, lv.name, lv.idx, sort_tag(sort));
            Name::new(tag, id)
        }
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
///
/// **Domain order**: entries are converted in Maude's RAW returned
/// order (`0..ms.len()`).  Current HS `msubstToLSubstVFresh`
/// (Maude/Types.hs:127-138) does NO sort either — upstream `c9d456b8`
/// ("More general fix for substitution canonicalisation") REMOVED the old
/// `sortBy (comparing (snd . fst))` from both the VFresh (unify/variants)
/// and VFree (match) conversions, moving the split-disjunction
/// canonicalisation into `performSplit` (`sortOnMemo
/// dropNameHintsLNSubstVFresh`, EquationStore.hs; mirrored in RS
/// `perform_split`, 631e0a85).  RS's Maude command stream is already
/// aligned to HS, so the raw orders coincide.
///
/// Match-path conversion (HS `msubstToLSubstVFree`).
fn msubst_to_lnsubst(
    ms: &MSubst,
    ctx: &mut ConvCtx,
) -> Result<Vec<(crate::lterm::LVar, LNTerm)>, MaudeError> {
    msubst_to_lnsubst_with_avoid(ms, ctx, 0)
}

/// Unify/variants-path conversion (HS `msubstToLSubstVFresh`).  Identical
/// to `msubst_to_lnsubst` now that neither path sorts the domain (see the
/// `msubst_to_lnsubst` doc); kept as a separate name to mark the
/// VFresh-vs-VFree call sites.
fn msubst_to_lnsubst_unify(
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
    // HS-faithful: variants use `msubstToLSubstVFresh`, which converts in
    // Maude's raw returned order (no domain sort; Maude/Types.hs:127-138).
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
    // HS-faithful: both the unify/variants path (`msubstToLSubstVFresh`)
    // and the match path (`msubstToLSubstVFree`) convert in Maude's raw
    // returned order — neither sorts the domain (Maude/Types.hs:127-138;
    // the old `sortBy` was removed upstream in `c9d456b8`).
    for ((sort, idx), mt) in ms {
        let lv = crate::maude_types::substitute_lookup_var(ctx, *sort, *idx)
            .ok_or_else(|| MaudeError::Other(format!(
                "no binding for Maude variable x{}:{:?}", idx, sort)))?;
        // HS-faithful: HS's `msubstToLSubstVFresh` (Maude/Types.hs:138)
        // UNCONDITIONALLY uses `"x"` as the name hint for Maude-introduced
        // witnesses inside `eqsConj` substitutions.  The commented-out
        // alternative branch at Maude/Types.hs:134-137 (preserve domain
        // name for `xi → xj` renames) is explicitly marked "seems wrong".
        let name_hint: &str = "x";
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
}

/// A borrowed Maude handle from a `MaudePool`.  `Deref`s to
/// `MaudeHandle`; releases back to the pool on `Drop`.
pub struct PooledMaude<'a> {
    pool: &'a MaudePool,
    inner: Option<MaudeHandle>,
}

impl<'a> PooledMaude<'a> {
    /// Borrow the underlying `MaudeHandle` for the lifetime of this guard.
    /// Does NOT consume the guard or transfer ownership: the returned
    /// reference is valid only while the `PooledMaude` lives, and the
    /// handle is released back to the pool in `PooledMaude::drop`.  This
    /// is the same accessor as the `Deref` impl; callers that need an
    /// owned handle (e.g. to clone into a per-task `ProofContext`) should
    /// `.clone()` the returned `&MaudeHandle`.
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

    // Regression (alethea `indivVerif` false-attack, fixed by emitting
    // `match PATTERN <=? SUBJECT` in the right order):
    // pattern multiset `codeOther ++ <a,b>` (codeOther is the only
    // pattern var) must AC-match subject `code2 ++ x ++ <a,b>` by
    // binding `codeOther -> code2 ++ x`.  HS's Maude matchAction does
    // this; `match_eqs_const_subject` previously swapped pattern/subject
    // and returned "No match", which left `insertImpliedFormulas` from
    // deriving gfalse and FALSIFIED a true lemma.
    #[test]
    fn match_eqs_const_subject_mset_var_to_submultiset() {
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        use crate::function_symbols::{AcSym, NoEqSym, FunSym, Privacy, Constructability};
        let pair_sym = NoEqSym::new(b"pair".to_vec(), 2, Privacy::Public, Constructability::Constructor);
        let sig = crate::maude_sig::mset_maude_sig().add_fun_sym(pair_sym.clone());
        let h = MaudeHandle::start(&path, sig).expect("start");
        let mk = |v: LVar| -> LNTerm { crate::term::Term::Lit(Lit::Var(v)) };
        // ground "pair" payload a,b -> use public name constants
        let a = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(crate::lterm::NameTag::Pub, "a")));
        let b = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(crate::lterm::NameTag::Pub, "b")));
        let payload = crate::term::Term::App(FunSym::NoEq(pair_sym.clone()), vec![a, b].into());
        // pattern var codeOther:Msg idx 89 (the universal-bound var)
        let code_other = LVar::new("codeOther", LSort::Msg, 89);
        let pat = crate::term::f_app_ac(AcSym::Union, vec![mk(code_other.clone()), payload.clone()]);
        // subject: code2:Msg, x:Msg (free system vars, skolemized by the fn)
        let code2 = LVar::new("code2", LSort::Msg, 8);
        let xv = LVar::new("x", LSort::Msg, 9);
        let subj = crate::term::f_app_ac(AcSym::Union, vec![mk(code2.clone()), mk(xv.clone()), payload.clone()]);
        let mut pattern_vars = std::collections::BTreeSet::new();
        pattern_vars.insert(("codeOther".to_string(), 89u64));
        let res = h.match_eqs_const_subject(
            &[Equal { lhs: pat, rhs: subj }], &pattern_vars).expect("match");
        eprintln!("[REPRO] match result count = {}", res.len());
        for m in &res {
            for (lv, lt) in m {
                eprintln!("[REPRO]   {}#{} -> {:?}", lv.name, lv.idx, lt);
            }
        }
        assert!(!res.is_empty(),
            "expected codeOther to AC-match a 2-element sub-multiset");
    }

    // Regression (DH key-exchange over-match, fixed by routing the
    // `insertImpliedFormulas` Action-guard AC-fallback through
    // `match_eqs_skolemize_both` instead of `match_eqs_const_subject`).
    //
    // HS's `impliedFormulas` runs `skolemizeGuarded` over the WHOLE
    // clause (`System.hs:1122`): every FREE (non-universal) LVar of the
    // guard pattern becomes a Maude *constant* (`MaudeConst`), only the
    // universal-bound vars stay bindable Maude variables.  So a guard
    // pattern position holding a free system var must match the system
    // action's corresponding position as CONSTANT-vs-CONSTANT.
    //
    // Mirrors the real STS_MAC_fix2 `AcceptedR` guard match (sent as
    // per-argument equations, one for each fact position).  The guard
    // pattern has ONE universal-bound var `kpartner` and several FREE
    // system vars (`ekI`,`ekR`) that, after a prior guard's binding,
    // occupy positions whose subject counterparts are DIFFERENT free
    // system vars (`x`,`tid`).  Two equations:
    //   eq1:  exp(g, ekI)  <=?  exp(g, x)     (pattern free ekI vs x)
    //   eq2:  exp(g, ekR)  <=?  exp(g, tid)   (pattern free ekR vs tid)
    // With `match_eqs_const_subject` the pattern's `ekI`,`ekR` are Maude
    // VARIABLES, so Maude binds `ekI->x`, `ekR->tid` and the match
    // SUCCEEDS — the spurious match that fired `gfalse` one step early.
    // With `match_eqs_skolemize_both` every free var is a distinct
    // CONSTANT, so `exp(g,c_ekI)` != `exp(g,c_x)` and the match FAILS,
    // exactly as HS's `skolemizeGuarded`-then-`matchAction` does.
    #[test]
    fn impl_guard_match_skolemizes_pattern_free_vars() {
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        use crate::function_symbols::{FunSym, exp_sym};
        let sig = crate::maude_sig::dh_maude_sig();
        let h = MaudeHandle::start(&path, sig).expect("start");
        let mk = |v: LVar| -> LNTerm { crate::term::Term::Lit(Lit::Var(v)) };
        let g = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(crate::lterm::NameTag::Pub, "g")));
        let exp = |base: LNTerm, e: LNTerm|
            crate::term::Term::App(FunSym::NoEq(exp_sym()), vec![base, e].into());
        // free (non-universal) system vars — NONE of these is in
        // `pattern_vars`, so HS skolemizes them all to constants.
        let ek_i = LVar::new("ekI", LSort::Fresh, 0);
        let ek_r = LVar::new("ekR", LSort::Fresh, 0);
        let xv   = LVar::new("x",   LSort::Fresh, 21);
        let tid  = LVar::new("tid", LSort::Fresh, 15);
        let eqs = vec![
            Equal { lhs: exp(g.clone(), mk(ek_i.clone())), rhs: exp(g.clone(), mk(xv.clone())) },
            Equal { lhs: exp(g.clone(), mk(ek_r.clone())), rhs: exp(g.clone(), mk(tid.clone())) },
        ];
        // No universal-bound vars in these positions.
        let pattern_vars: std::collections::BTreeSet<(String, u64)> =
            std::collections::BTreeSet::new();
        // const_subject (the OLD Action-guard path) OVER-MATCHES: the
        // pattern's free `ekI`,`ekR` are Maude variables binding to x,tid.
        let over = h.match_eqs_const_subject(&eqs, &pattern_vars).expect("m1");
        eprintln!("[REPRO] const_subject matches = {} (over-match expected: >=1)", over.len());
        assert!(!over.is_empty(),
            "sanity: const_subject is expected to OVER-match here (the bug)");
        // skolemize_both (the FIX): ekI,ekR,x,tid are distinct constants,
        // so neither equation can be satisfied → NO match, matching HS.
        let fixed = h.match_eqs_skolemize_both(&eqs, &pattern_vars).expect("m2");
        eprintln!("[REPRO] skolemize_both matches = {} (HS-faithful: 0)", fixed.len());
        assert!(fixed.is_empty(),
            "skolemize_both must NOT over-match: pattern-side free system \
             vars (ekI,ekR) are CONSTANTS and cannot bind to the subject's \
             different free vars (x,tid); got {:?}", fixed);
    }

    /// Directional regression for the `match_eqs` / `compare_term_subs`
    /// flipped-`Equal`-convention bug.
    ///
    /// HS `compareTermSubs t1 t2` (`Subsumption.hs:37-45`) returns `GT`
    /// when `t1` is strictly MORE SPECIFIC than `t2`, `LT` when more
    /// general. With `t1 = h(x)` (general) and `t2 = h(a)` (ground,
    /// specific):
    ///   - arm A = `t1 matchWith t2` = subject h(x) vs pattern h(a):
    ///     h(x)'s free var sits in the SUBJECT (ground) slot, h(a) is
    ///     the pattern with no vars ⇒ No match (empty).
    ///   - arm B = `t2 matchWith t1` = subject h(a) vs pattern h(x):
    ///     x --> a ⇒ matches.
    ///   - check [] (_:_) = LT ⇒ `compareTermSubs(h(x),h(a)) = Just LT`
    ///     and symmetrically `compareTermSubs(h(a),h(x)) = Just GT`.
    ///
    /// Before the fix, `compare_term_subs` constructed `Equal { lhs:
    /// t2, rhs: t1 }` for arm A (mistaking RS's `Equal` for the
    /// `pattern,subject` order used by the const_subject sibling),
    /// which SWAPPED the result: it returned `Greater` for `(h(x),h(a))`
    /// and `Less` for `(h(a),h(x))` — the inverse of HS. (Latent
    /// because the sole consumer `eq_term_subs` tests only `Equal`.)
    #[test]
    fn compare_term_subs_direction_matches_hs() {
        let path = match maude_path() { Some(p) => p, None => { eprintln!("skipping: no maude"); return; } };
        use crate::function_symbols::{NoEqSym, FunSym, Privacy, Constructability};
        let h_sym = NoEqSym::new(b"h".to_vec(), 1, Privacy::Public, Constructability::Constructor);
        let sig = pair_maude_sig().add_fun_sym(h_sym.clone());
        let hnd = MaudeHandle::start(&path, sig).expect("start");
        let mk = |v: LVar| -> LNTerm { crate::term::Term::Lit(Lit::Var(v)) };
        let x = LVar::new("x", LSort::Msg, 0);
        let a = crate::term::Term::Lit(Lit::Con(crate::lterm::Name::new(crate::lterm::NameTag::Pub, "a")));
        let t_gen = crate::term::Term::App(FunSym::NoEq(h_sym.clone()), vec![mk(x)].into()); // h(x) general
        let t_spec = crate::term::Term::App(FunSym::NoEq(h_sym.clone()), vec![a].into());    // h(a) specific
        // general vs specific => general is LESS specific => Less.
        assert_eq!(
            crate::subsumption::compare_term_subs(&hnd, &t_gen, &t_spec).expect("cmp"),
            Some(std::cmp::Ordering::Less),
            "h(x) is more general than h(a); HS compareTermSubs gives Less");
        // specific vs general => specific is MORE specific => Greater.
        assert_eq!(
            crate::subsumption::compare_term_subs(&hnd, &t_spec, &t_gen).expect("cmp"),
            Some(std::cmp::Ordering::Greater),
            "h(a) is more specific than h(x); HS compareTermSubs gives Greater");
        // Identical (modulo renaming) terms compare Equal (invariant).
        let y = LVar::new("y", LSort::Msg, 1);
        let t_gen2 = crate::term::Term::App(FunSym::NoEq(h_sym.clone()), vec![mk(y)].into());
        assert_eq!(
            crate::subsumption::compare_term_subs(&hnd, &t_gen, &t_gen2).expect("cmp"),
            Some(std::cmp::Ordering::Equal),
            "h(x) and h(y) are equal modulo renaming => Equal");
    }
}
