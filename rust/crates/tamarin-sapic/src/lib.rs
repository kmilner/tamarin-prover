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
//!
//! Not yet ported (~2700 LOC remaining):
//! `Sapic.Exceptions`, `Sapic.Facts`, `Sapic.Typing`,
//! `Sapic.LetDestructors`, `Sapic.Locks`, `Sapic.States`,
//! `Sapic.Compression`, `Sapic.ProgressFunction`,
//! `Sapic.ProgressTranslation`, `Sapic.Report`,
//! `Sapic.ReliableChannelTranslation`, `Sapic.Basetranslation`,
//! `Sapic.Warnings`, top-level `Sapic`.

pub mod annotation;
pub mod bindings;
pub mod secret_channels;
