//! Port of `Theory.Model.Signature` from
//! `lib/theory/src/Theory/Model/Signature.hs`.
//!
//! In Haskell the type is parameterised over the Maude attachment
//! (`Signature MaudeSig` vs `Signature MaudeHandle`). Until we have a
//! working Maude bridge (`tamarin_term::maude` is a stub), we expose only
//! the pure variant.

use tamarin_term::maude::MaudeHandle;
use tamarin_term::maude_sig::{minimal_maude_sig, MaudeSig};

/// A theory signature carrying a Maude signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignaturePure {
    pub maude_sig: MaudeSig,
}

impl SignaturePure {
    pub fn empty(diff: bool) -> Self {
        SignaturePure { maude_sig: minimal_maude_sig(diff) }
    }

    pub fn maude_sig(&self) -> &MaudeSig { &self.maude_sig }
}

/// `Signature` carrying a (stubbed) Maude handle.
#[derive(Debug, Clone)]
pub struct SignatureWithMaude {
    pub maude_handle: MaudeHandle,
}

impl SignatureWithMaude {
    /// Build a signature with a stub handle. Real implementation must
    /// spawn a Maude subprocess.
    pub fn from_pure(sig: SignaturePure) -> Self {
        SignatureWithMaude { maude_handle: MaudeHandle::stub(sig.maude_sig) }
    }

    pub fn to_pure(&self) -> SignaturePure {
        SignaturePure { maude_sig: self.maude_handle.maude_sig().clone() }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_signature_round_trip() {
        let s = SignaturePure::empty(false);
        let with_maude = SignatureWithMaude::from_pure(s.clone());
        assert_eq!(with_maude.to_pure(), s);
    }
}
