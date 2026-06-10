//! Constraint solver data layer (port of `Theory.Constraint.System.*`).
//!
//! The Haskell tree splits the constraint system into:
//! - `Theory.Constraint.System.Guarded`     — guarded formulas (already
//!   ported in [`crate::guarded`])
//! - `Theory.Constraint.System.Constraints` — graph constraints, lessAtoms,
//!   goals (this module: [`mod@constraints`])
//! - `Theory.Constraint.System`             — the `System` sequent (the
//!   solver's working state)
//! - `Theory.Constraint.Solver.*`           — the actual proof-search loop
//!
//! For now we expose only the data layer needed to hand the solver
//! something it can work on.

pub mod constraints;
pub mod solver;
pub mod system;

pub use constraints::*;
pub use solver::*;
pub use system::System;
