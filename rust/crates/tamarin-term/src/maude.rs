//! Stub for Maude integration.
//!
//! The Haskell port (`Term.Maude.Process`, `Term.Maude.Parser`,
//! `Term.Maude.Types`) spawns a `maude` subprocess and exchanges
//! S-expression-style messages over stdio for AC unification, matching,
//! and normalisation.
//!
//! For now we expose a `MaudeHandle` type that documents the design but
//! does not actually run a subprocess. Callers wanting AC unification
//! must currently use the no-AC path in [`crate::unification`].

use std::path::PathBuf;

use crate::maude_sig::MaudeSig;

/// Handle to a running Maude subprocess.
///
/// **Not yet implemented.** Contains only metadata; constructing one with
/// [`MaudeHandle::stub`] is fine, but invoking AC operations on it will
/// `unimplemented!()`.
#[derive(Debug, Clone)]
pub struct MaudeHandle {
    sig: MaudeSig,
    file_path: PathBuf,
}

impl MaudeHandle {
    /// Build a stub handle without actually starting Maude. Useful for
    /// tests and downstream code that only inspects the signature.
    pub fn stub(sig: MaudeSig) -> Self {
        MaudeHandle { sig, file_path: PathBuf::from("<not-started>") }
    }

    pub fn maude_sig(&self) -> &MaudeSig { &self.sig }
    pub fn file_path(&self) -> &PathBuf { &self.file_path }
}

/// Marker error type for unimplemented Maude operations.
#[derive(Debug)]
pub struct MaudeUnimplemented;

impl std::fmt::Display for MaudeUnimplemented {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Maude subprocess integration is not yet implemented in the Rust port")
    }
}

impl std::error::Error for MaudeUnimplemented {}
