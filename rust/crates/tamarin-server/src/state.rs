//! In-memory store of loaded theories, mirroring Haskell `TheoryMap`.
//!
//! Indexed by integer (1-based, matching Haskell's behaviour) — the
//! frontend reads/writes these indices in URLs like
//! `/thy/trace/<idx>/main/...`.
//!
//! We keep both the parser AST and the elaborated typed theory.  The
//! parser AST is needed by `prove_lemma`; the elaborated theory is
//! used for accessor helpers (lemma list, restriction count, …).
//!
//! Concurrency: `parking_lot::Mutex` — interactive single-user UI, no
//! need for an async lock.  Only the autoprover (`autoprove` /
//! `autoprove_all`) offloads its work onto `tokio::task::spawn_blocking`;
//! interactive single-step applies and proof-state materialization run
//! inline on the async handler thread.

use parking_lot::Mutex;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;

use chrono::{DateTime, Local};

use tamarin_parser::ast as p;
use tamarin_theory::theory::Theory as TypedTheory;

use crate::handlers::proof_tree::ProofState;

/// One loaded theory with bookkeeping.
#[derive(Clone)]
pub struct TheoryEntry {
    /// Stable index used in URLs.  Set by `TheoryStore::insert`.
    pub idx: usize,
    /// Theory name from the `.spthy` source.
    pub name: String,
    /// Parser AST — kept verbatim so `prove_lemma` has the same shape
    /// it was elaborated from.
    pub parser_theory: Arc<p::Theory>,
    /// Elaborated, typed theory — used for accessor helpers.  Wrapped
    /// in `Arc` so we can clone the entry cheaply.
    pub typed_theory: Arc<TypedTheory>,
    /// Where the theory came from.
    pub origin: TheoryOrigin,
    /// Load time for the UI.
    pub loaded_at: DateTime<Local>,
    /// True for the originally loaded copy (vs. ones produced by edits).
    pub primary: bool,
    /// HTML for the wellformedness warning banner shown in the theory
    /// page header (HS `errorsHtml`, rendered raw via
    /// `preEscapedToMarkup info.errorsHtml` at `src/Web/Theory.hs`).
    /// HS populates it from `makeWfErrorsHtml`
    /// (`src/Web/Handler.hs`), which wraps
    /// `renderHtmlDoc (htmlDoc $ prettyWfErrorReport report)` of the
    /// *closed* theory's wellformedness report in a `<div class="wf-warning">`.
    /// This is an unported interactive-web-UI feature: the Rust load path
    /// leaves it `String::new()` and no handler renders it, so the warning
    /// banner is not surfaced. It does not affect `--prove` output (the CLI
    /// reports wf errors via its own path). Populating it byte-for-byte
    /// requires the close-time (Maude-dependent) wf report plus matching
    /// HS `htmlDoc` escaping, so it is deferred rather than partially faked.
    pub errors_html: String,
    /// Live proof state — built lazily on first request that needs it
    /// (theory load → only kept-around-but-empty until `ensure_proof_state`
    /// is asked for).  `None` here means "not yet built"; on first
    /// access we boot Maude and precompute the per-lemma initial
    /// systems.  Building this eagerly at load time would cost ~1s
    /// per theory for Maude startup + source precompute, which is
    /// fine but pushes start-of-server latency.
    pub proof_state: Option<Arc<ProofState>>,
}

#[derive(Clone, Debug)]
pub enum TheoryOrigin {
    /// Loaded from a path on disk.
    Local(PathBuf),
    /// Uploaded via POST `/`.
    Upload(String),
    /// Generated interactively (e.g. by an edit). Currently never
    /// constructed — placeholder for the unported interactive-edit
    /// path (HS `Interactive`).
    Interactive,
}

impl TheoryOrigin {
    pub fn label(&self) -> String {
        match self {
            TheoryOrigin::Local(p) => p.display().to_string(),
            TheoryOrigin::Upload(n) => n.clone(),
            TheoryOrigin::Interactive => "(interactively created)".into(),
        }
    }
}

#[derive(Default, Clone)]
pub struct TheoryStore {
    inner: Arc<Mutex<TheoryStoreInner>>,
}

#[derive(Default)]
struct TheoryStoreInner {
    by_idx: BTreeMap<usize, TheoryEntry>,
}

impl TheoryStore {
    /// Insert a new theory and return the freshly assigned index.
    pub fn insert(&self, mut entry: TheoryEntry) -> usize {
        let mut inner = self.inner.lock();
        // Match Haskell's `M.findMax + 1` (BTreeMap max key); empty → 1.
        let idx = inner.by_idx.keys().next_back().map_or(1, |k| k + 1);
        entry.idx = idx;
        inner.by_idx.insert(idx, entry);
        idx
    }

    pub fn get(&self, idx: usize) -> Option<TheoryEntry> {
        self.inner.lock().by_idx.get(&idx).cloned()
    }

    pub fn list(&self) -> Vec<TheoryEntry> {
        self.inner.lock().by_idx.values().cloned().collect()
    }

    pub fn remove(&self, idx: usize) -> Option<TheoryEntry> {
        self.inner.lock().by_idx.remove(&idx)
    }

    /// Clone the entry at `src_idx` into a fresh `idx`, marking the
    /// clone as non-primary (Haskell `primary = False` for modified
    /// theories — see `putTheory` in `src/Web/Handler.hs`).  Updates
    /// the clone's `loaded_at`.  Returns the new idx.
    ///
    /// Used by `autoprove`, `autoproveAll`, `del/path` — mirrors
    /// Haskell's `modifyTheory` which always allocates a new idx.
    ///
    /// The `proof_state` is dropped on clone: each idx version should
    /// have its own proof tree so mutations on one don't leak to the
    /// other (Haskell's `IncrementalProof` is value-typed, not shared).
    /// The new idx rebuilds proof state on first `ensure_proof_state`
    /// — that's a ~1s cost (Maude boot + source precompute) but
    /// preserves the version-fork semantics.
    pub fn clone_at_new_idx(&self, src_idx: usize) -> Option<usize> {
        let mut inner = self.inner.lock();
        let mut clone = inner.by_idx.get(&src_idx).cloned()?;
        let new_idx = inner.by_idx.keys().last().copied().unwrap_or(0) + 1;
        clone.idx = new_idx;
        clone.primary = false;
        clone.loaded_at = Local::now();
        // Drop the shared proof state — clone gets its own (rebuilt
        // lazily).  See doc comment above.
        clone.proof_state = None;
        inner.by_idx.insert(new_idx, clone);
        Some(new_idx)
    }

    /// Like [`clone_at_new_idx`] but, when the source idx has a
    /// materialised `proof_state`, also fork it into the clone — share
    /// the `ProofContext` (Maude handle + precomputed sources) but
    /// deep-copy the per-lemma trees so subsequent mutations on the
    /// clone don't leak back into the source.  Used by the method-apply
    /// route so the post-step proof tree contains the SAME tree shape
    /// as the source idx (i.e. retains all children produced by prior
    /// applied steps), rather than rebuilding a bare initial-state
    /// tree.  This mirrors Haskell's `modifyTheory` semantics, where
    /// `putTheory` puts the *modified* `ClosedTheory` (with its full
    /// `IncrementalProof`) at the new idx — not a fresh one.
    pub fn clone_at_new_idx_forking_proof_state(&self, src_idx: usize) -> Option<usize> {
        let mut inner = self.inner.lock();
        let mut clone = inner.by_idx.get(&src_idx).cloned()?;
        let new_idx = inner.by_idx.keys().last().copied().unwrap_or(0) + 1;
        clone.idx = new_idx;
        clone.primary = false;
        clone.loaded_at = Local::now();
        // Fork the proof state if present — preserves the source tree's
        // shape under a new Arc.  If the source never materialised a
        // proof state, the clone starts from scratch (`None`).
        clone.proof_state = clone.proof_state.as_ref().map(|ps| Arc::new(ps.fork()));
        inner.by_idx.insert(new_idx, clone);
        Some(new_idx)
    }

    /// Replace the entry at `idx` in place, keeping the idx the same.
    /// Mirrors Haskell `replaceTheory` (`src/Web/Handler.hs` —
    /// used by `reload` and `editProof`).  Like `replaceTheory`'s
    /// `M.insert idx newThy theories`, this inserts unconditionally
    /// (creating the entry if `idx` is currently absent), and forces
    /// `primary = false` to match `replaceTheory`'s hard-coded `False`
    /// for the `primary` field (so a reloaded theory shows as
    /// "Modified", not "Original").  Always returns `Some(idx)`.
    pub fn replace_at(&self, idx: usize, mut entry: TheoryEntry) -> Option<usize> {
        let mut inner = self.inner.lock();
        entry.idx = idx;
        entry.primary = false;
        inner.by_idx.insert(idx, entry);
        Some(idx)
    }

    /// Get-or-build the live [`ProofState`] for `idx`. Builds it
    /// lazily on first call and stores it in the entry so subsequent
    /// requests reuse the same proof tree.
    pub fn ensure_proof_state(
        &self,
        idx: usize,
        maude_path: &str,
    ) -> Result<Arc<ProofState>, String> {
        // Fast path: already materialised.  Clone out the `Arc<Theory>`
        // we need, then release the store lock before the ~1s
        // `ProofState::new` (Maude boot + source precompute) so unrelated
        // handlers — and other tokio workers — aren't blocked for its
        // duration.
        let parser_theory = {
            let inner = self.inner.lock();
            let entry = inner.by_idx.get(&idx)
                .ok_or_else(|| format!("theory index {} not found", idx))?;
            if let Some(ps) = &entry.proof_state {
                return Ok(ps.clone());
            }
            entry.parser_theory.clone()
        };
        let ps = Arc::new(ProofState::new(&parser_theory, maude_path)?);
        // Re-lock and double-check: another thread may have built (and
        // stored) the proof state while we held no lock.  If so, prefer
        // the already-stored one so all callers share a single instance.
        let mut inner = self.inner.lock();
        let entry = inner.by_idx.get_mut(&idx)
            .ok_or_else(|| format!("theory index {} not found", idx))?;
        if let Some(existing) = &entry.proof_state {
            return Ok(existing.clone());
        }
        entry.proof_state = Some(ps.clone());
        Ok(ps)
    }
}

/// App-wide state, used by every handler.
pub struct AppState {
    pub cfg: crate::ServerConfig,
    pub store: TheoryStore,
}
