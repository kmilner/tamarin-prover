//! Global, write-once intern pools for symbol and variable *names*.
//!
//! Function-symbol names (`NoEqSym.name`) and variable-name roots
//! (`LVar.name`, `FactTag::Proto` name) are drawn from a *bounded* set — the
//! theory's signature plus a fixed handful of generated roots (`vk`, `vr`,
//! `z`, …).  By interning each distinct name once and handing out a
//! `&'static` reference, we get the best of every representation:
//!
//!   * **clone is a pointer copy** — no heap allocation (unlike owned
//!     `String`/`Vec`) and no atomic refcount (unlike `Arc<…>`);
//!   * **drop is a no-op** — no refcount decrement;
//!   * **one shared copy** — minimal memory, like `Arc`'s shared buffer but
//!     without the refcount that made it a contention point under the
//!     16-way-parallel proof search.
//!
//! `&'static` is a *concrete* lifetime, so the name fields stay plain
//! (non-generic) structs — no lifetime parameter threads through `Term`.
//!
//! Interning happens only when a name is first built from raw bytes/chars
//! (parsing, Maude-reply decoding, fresh-symbol creation) — NOT on the hot
//! clone/drop path, where a `&'static` is simply `Copy`.  After warm-up every
//! distinct name is present, so interning is a read-locked lookup; inserts
//! (which leak a boxed copy) are rare.  The leak is bounded by the number of
//! distinct names in the run.
//!
//! Equality/ordering/hashing are unchanged vs the previous owned/`Arc`
//! representations: `&[u8]`/`&str` deref to their contents, so `Ord`/`Eq`/
//! `Hash` remain content-based (byte-/char-lexicographic) — byte-identical
//! `--prove` output.

use std::sync::{OnceLock, RwLock};
use tamarin_utils::FastSet;

fn byte_pool() -> &'static RwLock<FastSet<&'static [u8]>> {
    static P: OnceLock<RwLock<FastSet<&'static [u8]>>> = OnceLock::new();
    P.get_or_init(|| RwLock::new(FastSet::default()))
}

fn str_pool() -> &'static RwLock<FastSet<&'static str>> {
    static P: OnceLock<RwLock<FastSet<&'static str>>> = OnceLock::new();
    P.get_or_init(|| RwLock::new(FastSet::default()))
}

/// Intern raw bytes (a function-symbol name), returning the canonical
/// `&'static [u8]` for that content.  Equal content always yields the same
/// pointer.
pub fn intern_bytes(b: &[u8]) -> &'static [u8] {
    // Fast path: already interned → shared read lock + lookup.
    if let Some(&s) = byte_pool().read().unwrap().get(b) {
        return s;
    }
    // Slow path: insert under the write lock, double-checking for a racing
    // insert of the same content first.
    let mut w = byte_pool().write().unwrap();
    if let Some(&s) = w.get(b) {
        return s;
    }
    let leaked: &'static [u8] = Box::leak(b.to_vec().into_boxed_slice());
    w.insert(leaked);
    leaked
}

/// Intern a string (a variable-name root / fact name), returning the
/// canonical `&'static str` for that content.
pub fn intern_str(s: &str) -> &'static str {
    if let Some(&v) = str_pool().read().unwrap().get(s) {
        return v;
    }
    let mut w = str_pool().write().unwrap();
    if let Some(&v) = w.get(s) {
        return v;
    }
    let leaked: &'static str = Box::leak(s.to_owned().into_boxed_str());
    w.insert(leaked);
    leaked
}
