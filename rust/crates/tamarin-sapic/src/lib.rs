//! SAPIC process calculus for the Tamarin prover (Rust port).
//!
//! The data layer (Process, SapicAction, SapicLVar, ProcessParsedAnnotation,
//! ProcessPosition) lives in `tamarin_theory::sapic` because Haskell places
//! it under `lib/theory/src/Theory/Sapic/`. This crate hosts the
//! transformation passes from `lib/sapic/src/Sapic/`.
//!
//! Modules ported:
//! - [`bindings`] ← `Sapic.Bindings`
//! - [`annotation`] ← `Sapic.Annotation`
//! - [`secret_channels`] ← `Sapic.SecretChannels`
//! - [`facts`] ← `Sapic.Facts`
//! - [`typing`] ← `Sapic.Typing`
//! - [`locks`] ← `Sapic.Locks` (lock annotation; `checkLocks` not ported)
//! - [`base_translation`] ← `Sapic.Basetranslation` (linear + state + locks)
//! - [`translate`] / [`apply`] ← top-level `Sapic`
//!
//! Not yet ported (later phases):
//! `Sapic.Exceptions`, `Sapic.LetDestructors`,
//! `Sapic.States` (pure-state detection passes — the `pure_state`/`L_PureState`
//! translation paths exist but the `annotatePureStates` detector is not wired),
//! `Sapic.Compression`, `Sapic.ProgressFunction`,
//! `Sapic.ProgressTranslation`, `Sapic.Report`,
//! `Sapic.ReliableChannelTranslation`, `Sapic.Warnings`,
//! plus secret/private channels, process-calls and `let`-with-destructor
//! in `convert`/`base_translation`.

pub mod annotation;
pub mod apply;
pub mod base_translation;
pub mod bindings;
pub mod convert;
pub mod facts;
pub mod locks;
pub mod secret_channels;
pub mod translate;
pub mod typing;
