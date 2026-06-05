//! Quick proof-tree dumper for an HS-vs-Rust shape comparison.
//!
//! Usage: `cargo run --example dump_proof -- <theory.spthy> <lemma>`

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use tamarin_parser::parse_theory;
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::prove::prove_lemma;
use tamarin_theory::proof_skeleton::render;
use tamarin_term::maude_proc::MaudeHandle;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: dump_proof <theory.spthy> <lemma>");
        std::process::exit(2);
    }
    let theory_path = &args[1];
    let lemma = &args[2];

    let source = std::fs::read_to_string(theory_path).expect("read theory");
    let parsed = parse_theory(&source, &[]).expect("parse theory");
    // Need the elaborated theory to extract the full MaudeSig
    // (includes aenc/pk/etc.).  Using default sig means Maude won't
    // know the user-declared symbols, producing a wrong proof tree.
    let elaborated = elaborate(&parsed).expect("elaborate");

    let maude_path = "/home/linuxbrew/.linuxbrew/bin/maude";
    let maude_sig = elaborated.signature.maude_sig.clone();
    let maude = MaudeHandle::start(maude_path, maude_sig).expect("start maude");

    let root = prove_lemma(&parsed, lemma, maude, 500).expect("prove");
    let steps = count_steps(&root);
    eprintln!("=== {} proof tree (status={:?}, children={}, steps={}) ===",
        lemma, root.status, root.children.len(), steps);
    println!("{}", render(&root));
}

fn count_steps(node: &tamarin_theory::constraint::solver::search::ProofNode) -> usize {
    1 + node.children.values().map(count_steps).sum::<usize>()
}
