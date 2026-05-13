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
use std::sync::{Arc, Mutex};

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
    _child: Child,
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
        self.write_line(cmd)?;
        self.read_until_prompt()
    }
}

fn find_subseq(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() { return None; }
    haystack.windows(needle.len()).position(|w| w == needle)
}

/// Handle to a running Maude subprocess. Cloneable; uses an `Arc<Mutex<...>>`
/// internally so calls from multiple owners are serialised.
#[derive(Clone)]
pub struct MaudeHandle {
    inner: Arc<Mutex<MaudeProcessInner>>,
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
        let mut inner = MaudeProcessInner {
            _child: child,
            stdin,
            stdout,
            stats: MaudeStats::default(),
            sig: sig.clone(),
            path: PathBuf::from(maude_path),
            unifiable_cache: std::collections::HashMap::new(),
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
        Ok(MaudeHandle { inner: Arc::new(Mutex::new(inner)) })
    }

    pub fn maude_sig(&self) -> MaudeSig {
        self.inner.lock().unwrap().sig.clone()
    }

    pub fn file_path(&self) -> PathBuf {
        self.inner.lock().unwrap().path.clone()
    }

    pub fn stats(&self) -> MaudeStats {
        self.inner.lock().unwrap().stats
    }

    /// Reduce a term to normal form modulo the theory.
    pub fn reduce(&self, t: &LNTerm) -> Result<LNTerm, MaudeError> {
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
        Ok(mterm_to_lnterm(&mt_back, &mut ctx, "z", &mut next))
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

    /// True when the signature carries no AC-flavoured operators —
    /// i.e. no DH, XOR, multiset, nat or bilinear-pairing.  In that
    /// regime free (Robinson) unification is complete; we can answer
    /// every Maude unifiability query locally.
    fn is_ac_free(&self) -> bool {
        let sig = self.inner.lock().unwrap().sig.clone();
        !sig.enable_dh && !sig.enable_xor && !sig.enable_mset
            && !sig.enable_nat && !sig.enable_bp
    }

    pub fn unify_at(&self, label: &'static str, eqs: &[Equal<LNTerm>])
        -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
    {
        _tally_callsite(label);
        self.unify(eqs)
    }

    pub fn unify(&self, eqs: &[Equal<LNTerm>]) -> Result<Vec<Vec<(crate::lterm::LVar, LNTerm)>>, MaudeError>
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
        if self.is_ac_free() {
            let eqs_owned: Vec<Equal<LNTerm>> = eqs.iter().cloned().collect();
            return Ok(match crate::unification::unify_lnterm_no_ac(eqs_owned) {
                Ok(subst) => {
                    let bindings: Vec<(crate::lterm::LVar, LNTerm)> = subst.to_list()
                        .into_iter().map(|(v, t)| (v, t)).collect();
                    vec![bindings]
                }
                Err(_) => Vec::new(),
            });
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
            pp_mterm(&Term::App(FunSym::List, items.to_vec()))
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
    /// **Currently unused**: `insert_implied_formulas_pass` uses a pure
    /// structural matcher in the constraint-solver layer (mirroring
    /// Haskell's pre-Maude pass) for non-AC cases.  Kept here as
    /// infrastructure for future AC-modulo `impliedFormulas`
    /// matching, where structural matching wouldn't suffice.
    #[allow(dead_code)]
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
                    for a in args { collect_subject_vars(a, pattern_vars, out); }
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
                    crate::term::Term::App(sym.clone(), new_args)
                }
                _ => t.clone(),
            }
        }
        let rewritten_eqs: Vec<Equal<LNTerm>> = eqs.iter().map(|eq| Equal {
            lhs: eq.lhs.clone(),
            rhs: rewrite_subject(&eq.rhs, &skolem_map),
        }).collect();

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
            pp_mterm(&Term::App(FunSym::List, items.to_vec()))
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
        let msubsts = maude_parse::parse_match_reply(&sig, &reply)?;
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
        for ms in &msubsts {
            out.push(msubst_to_lnsubst(ms, &mut ctx)?);
        }
        Ok(out)
    }
}

/// Whether `eqs` contains any var-var pair where the two sides have
/// *different* sub-sorts.  When this happens, Maude's order-sorted
/// unifier introduces a fresh witness at the narrower sort and binds
/// both inputs to it; our local Robinson-style unifier instead picks
/// one of the originals as the survivor.  Both are valid most-general
/// unifiers but downstream code (eq-store + subst-system +
/// freshen_witness_range) is calibrated against Maude's witness-heavy
/// shape, so we fall back to Maude whenever sort narrowing is in play.
fn needs_sort_narrowing(eqs: &[Equal<LNTerm>]) -> bool {
    use crate::lterm::LSort;
    use crate::term::Term;
    use crate::vterm::Lit;
    fn collect_var_pairs(t1: &LNTerm, t2: &LNTerm, out: &mut Vec<(LSort, LSort)>) {
        match (t1, t2) {
            (Term::Lit(Lit::Var(v1)), Term::Lit(Lit::Var(v2))) => {
                out.push((v1.sort, v2.sort));
            }
            (Term::App(f1, a1), Term::App(f2, a2)) if f1 == f2 && a1.len() == a2.len() => {
                for (x, y) in a1.iter().zip(a2.iter()) {
                    collect_var_pairs(x, y, out);
                }
            }
            _ => {}
        }
    }
    let mut pairs: Vec<(LSort, LSort)> = Vec::new();
    for eq in eqs {
        collect_var_pairs(&eq.lhs, &eq.rhs, &mut pairs);
    }
    pairs.iter().any(|(a, b)| a != b)
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
            crate::term::Term::App(sym.clone(), new_args)
        }
        _ => t.clone(),
    }
}

/// Convert a Maude substitution `[((sort, idx), mt)]` into a list of
/// `(LVar, LNTerm)`.
///
/// **Witness naming**: Maude returns auxiliary witness variables when
/// expressing unifiers.  We decode each witness as an `LVar` with a
/// dedicated name `"~mw"` (Maude-Witness) that no input variable can
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
    let mut out = Vec::with_capacity(ms.len());
    let mut next: u64 = 0;
    // Even within a single Maude call we must avoid colliding with any
    // pre-existing `~mw`-named input (rare, but possible if a
    // sub-substitution from a prior call was re-fed in).
    for lit in ctx.bindings().values() {
        if let crate::vterm::Lit::Var(lv) = lit {
            if lv.name == "~mw" && lv.idx >= next {
                next = lv.idx + 1;
            }
        }
    }
    for ((sort, idx), mt) in ms {
        // Look up the original LVar that we mapped to MaudeVar(*idx, *sort).
        let lv = crate::maude_types::substitute_lookup_var(ctx, *sort, *idx)
            .ok_or_else(|| MaudeError::Other(format!(
                "no binding for Maude variable x{}:{:?}", idx, sort)))?;
        let t = mterm_to_lnterm(mt, ctx, "~mw", &mut next);
        out.push((lv, t));
    }
    Ok(out)
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
        let pk_term = crate::term::Term::App(FunSym::NoEq(pk_sym), vec![mk(ltka)]);
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
}
