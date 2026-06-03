//! Theory representation for the Tamarin prover (Rust port).
//!
//! Modules ported (mapping to Haskell):
//! - [`signature`] ← `Theory.Model.Signature`
//! - [`fact`] ← `Theory.Model.Fact`
//! - [`atom`] ← `Theory.Model.Atom`
//! - [`formula`] ← `Theory.Model.Formula` (data type + builders)
//! - [`restriction`] ← `Theory.Model.Restriction` (data type only)
//! - [`rule`] ← `Theory.Model.Rule` (data layer + indices + info types)
//! - [`sapic`] ← `Theory.Sapic.{Position, Term, Annotation, Process, Pattern}`
//! - [`intruder_rules`] ← `Theory.Tools.IntruderRules` (special intruder rules)
//! - [`predicate`] ← `Theory.Syntactic.Predicate` (data + lookup; expansion deferred)
//!
//! Not yet ported:
//! - `Theory.Model.Rule`: instantiation (`someRuleACInst*`), AC unification
//!   over rules, pretty/dot rendering
//! - `Theory.Constraint.*` (~10k LOC — the constraint solver)
//! - Most of `Theory.Tools.*` (well-formedness, equation store, subterm
//!   store, abstract interpretation, loop breakers, message-derivation
//!   checks, rule-variants computation, partial evaluation)
//! - `Theory.Text.Parser.*` (~3k LOC — `.spthy` parser)
//! - Remaining `Theory.Sapic.*` (Substitution, Print)
//! - Top-level `Theory` module (open/closed theories)

pub mod atom;
pub mod fact;
pub mod formula;
pub mod intruder_rules;
pub mod intruder_variants;
pub mod predicate;
pub mod pretty_formula;
pub mod pretty_system;
pub mod restriction;
pub mod rule;
pub mod constraint;
pub mod elaborate;
pub mod guarded;
pub mod guarded_types;
pub mod predicate_expand;
pub mod proof_skeleton;
pub mod prove;
pub mod replay;
pub mod state_trace;
pub mod sapic;
pub mod signature;
pub mod theory;
pub mod tools;
