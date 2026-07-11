//! Utility library for the Tamarin prover (Rust port).
//!
//! Modules ported from `lib/utils/src/` of the upstream Haskell tree.
//!
//! Some modules mirror their upstream Haskell counterparts in full for
//! fidelity and are not all exercised by the prover itself (for example the
//! `env_tracer` and `timing` debug/diagnostic helpers). Their module docs
//! note when this is the case.

pub mod bind;
pub mod color;
pub mod cow;
pub mod dag;
pub mod dot;
/// The `env_gate!` macro is exported at the crate root via
/// `#[macro_export]`; this (private) module just holds its definition.
mod env_gate;
pub mod env_tracer;
pub mod fresh;
pub mod logic;
pub mod misc;
pub mod prelude_ext;
pub mod pretty;
pub mod pretty_html;
pub mod timing;
pub mod unicode;

/// Fast non-cryptographic hash map for internal *lookup-only* uses
/// (membership tests / order-independent grouping / memo caches).  Uses
/// `rustc_hash::FxBuildHasher`, which is `Default`, so this is a drop-in
/// replacement for `std::collections::HashMap` at call sites that never
/// iterate the map into observable output or into an ordering decision.
pub type FastMap<K, V> = std::collections::HashMap<K, V, rustc_hash::FxBuildHasher>;
/// Fast non-cryptographic hash set — see [`FastMap`].
pub type FastSet<K> = std::collections::HashSet<K, rustc_hash::FxBuildHasher>;

/// Hash one value with the same `FxBuildHasher` the [`FastMap`]/[`FastSet`]
/// aliases use.  For hash-prefilter patterns over deep ASTs: `Hash`/`Eq`
/// consistency guarantees equal values hash equal, so
/// `fx_hash_one(a) != fx_hash_one(b)` proves `a != b` and the deep equality
/// walk only runs on hash agreement.  The hash itself must never reach
/// observable output — it is a filter, not an ordering key.
pub fn fx_hash_one<T: std::hash::Hash + ?Sized>(value: &T) -> u64 {
    use std::hash::BuildHasher as _;
    rustc_hash::FxBuildHasher.hash_one(value)
}
