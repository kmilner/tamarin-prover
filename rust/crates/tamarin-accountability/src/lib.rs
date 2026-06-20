//! Accountability extension for the Tamarin prover (Rust port).
//!
//! **Status:** scaffolded but not yet ported. The Haskell crate has two
//! modules:
//! - `Accountability.Generation` (352 lines): generates accountability
//!   lemmas from a high-level specification (`generateAccountabilityLemmas`,
//!   plus well-formedness checks and quantifier merging).
//! - `Accountability` (58 lines): the public surface and `translate` entry
//!   point, which wires the generated lemmas/predicates into the theory and
//!   raises `AccException`/`CaseTestsUndefined` (via `undefinedCaseTests`).
//!
//! Both depend on `Theory.Model.{Formula, Restriction}` and `Theory.Sapic`,
//! none of which are fully ported yet.
//!
//! When resuming: port both `Generation.hs` (lemma generation) and
//! `Accountability.hs` (the `translate` integration) — porting `Generation.hs`
//! alone would miss the top-level `translate` wiring.
