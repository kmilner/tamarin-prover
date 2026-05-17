//! Term language for the Tamarin prover (Rust port).
//!
//! Modules ported (mapping to Haskell):
//! - [`function_symbols`] ← `Term.Term.FunctionSymbols`
//! - [`term`] ← `Term.Term.Raw` (raw term type + AC-normalising smart constructors)
//! - [`vterm`] ← `Term.VTerm` (`Lit<C, V>` and helpers)
//! - [`lterm`] ← `Term.LTerm` (sorts, names, LVar, BVar, HasFrees, rename)
//! - [`subst`] ← `Term.Substitution.SubstVFree` (generic free substitution)
//! - [`subst_vfresh`] ← `Term.Substitution.SubstVFresh` (fresh-range substitution)
//! - [`rewriting`] ← `Term.Rewriting.Definitions` (Equal, Match, RRule)
//! - [`builtin`] ← `Term.Builtin.{Signature, Convenience, Rules}`
//! - [`subterm_rule`] ← `Term.SubtermRule`
//! - [`positions`] ← `Term.Positions` (AC-aware position math)
//! - [`maude_sig`] ← `Term.Maude.Signature`
//! - [`maude`] ← `Term.Maude.{Process, Parser, Types}` — **stub**, see module docs
//! - [`unification`] ← `Term.Unification` — **non-AC fragment only**
//!
//! Not yet ported:
//! - `Term.Macro` (trivial after `Substitution`)
//! - `Term.Subsumption` (depends on full unification)
//! - `Term.Rewriting.Norm` (uses Maude)
//! - `Term.Narrowing.{Variants, Variants.Check, Variants.Compute, Narrow}`
//! - `Term.Maude.{Process, Parser, Types}` proper implementations
//! - AC unification / matching (needs Maude subprocess driver)

pub mod builtin;
pub mod function_symbols;
pub mod lterm;
pub mod macro_expand;
pub mod maude;
pub mod maude_parse;
pub mod maude_print;
pub mod maude_proc;
pub mod maude_sig;
pub mod maude_types;
pub mod norm;
pub mod pretty;
pub mod subsumption;
pub mod positions;
pub mod rewriting;
pub mod subst;
pub mod subst_vfresh;
pub mod subterm_rule;
pub mod term;
pub mod unification;
pub mod vterm;
