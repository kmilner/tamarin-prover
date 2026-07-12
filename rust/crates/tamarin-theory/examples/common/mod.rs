//! Shared setup for the dev example binaries: read → parse → elaborate a
//! theory file and boot a Maude handle on its full signature.
//!
//! Lives in `examples/common/` (a subdirectory, so cargo does not treat it
//! as an example target); each example pulls it in with `mod common;`.

use tamarin_term::maude_proc::MaudeHandle;

/// Read, parse, and elaborate `theory_path`, then start Maude on the
/// elaborated signature (`$MAUDE_PATH` overrides the binary, else `maude`
/// on `PATH`).  The elaborated signature carries the full `MaudeSig`
/// (aenc/pk/user-declared symbols); booting Maude on the default sig would
/// leave those symbols unparseable and corrupt any downstream unification.
pub fn load_theory_with_maude(
    theory_path: &str,
) -> (
    tamarin_parser::ast::Theory,
    tamarin_theory::theory::Theory,
    MaudeHandle,
) {
    let source = std::fs::read_to_string(theory_path).expect("read theory");
    let parsed = tamarin_parser::parse_theory(&source, &[]).expect("parse theory");
    let elaborated = tamarin_theory::elaborate::elaborate(&parsed).expect("elaborate");
    let maude_path = std::env::var("MAUDE_PATH").unwrap_or_else(|_| "maude".to_string());
    let maude = MaudeHandle::start(&maude_path, elaborated.signature.maude_sig.clone())
        .expect("start maude");
    (parsed, elaborated, maude)
}
