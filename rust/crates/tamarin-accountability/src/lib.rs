//! Accountability extension for the Tamarin prover (Rust port).
//!
//! **Status:** scaffolded but not yet ported. The Haskell crate is just
//! `Accountability.Generation` (352 lines), which generates accountability
//! lemmas from a high-level specification. It depends on
//! `Theory.Model.{Formula, Restriction}` and `Theory.Sapic`, none of
//! which are fully ported yet.
//!
//! When resuming: port `Generation.hs` directly — there are no internal
//! sub-modules.
