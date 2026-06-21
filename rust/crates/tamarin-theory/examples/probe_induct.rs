use tamarin_parser::ast::TheoryItem;
use tamarin_theory::guarded::{formula_to_guarded, ginduct};

fn corpus_root() -> std::path::PathBuf {
    std::env::var("CORPUS_ROOT").map(std::path::PathBuf::from).unwrap_or_else(|_| {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../examples")
    })
}

fn main() {
    let path = corpus_root().join("loops/Minimal_Loop_Example.spthy");
    let src = std::fs::read_to_string(&path).expect("read");
    let theory = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let lemma = theory.items.iter().find_map(|it| match it {
        TheoryItem::Lemma(l) if l.name == "Satisfied_by_empty_trace_only" => Some(l),
        _ => None,
    }).expect("lemma");
    let g = formula_to_guarded(&lemma.formula).expect("guarded");
    println!("formula: {:?}", g);
    let (b, s) = ginduct(&g).expect("ginduct");
    println!("\nbase: {:?}", b);
    println!("\nstep: {:?}", s);
}
