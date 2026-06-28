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
