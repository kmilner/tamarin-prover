use tamarin_parser::parse_theory;
use tamarin_parser::ast as p;
use tamarin_theory::predicate_expand::expand_theory_formulas;

fn main() {
    let path = std::env::args().nth(1).expect("path");
    let src = std::fs::read_to_string(&path).expect("read");
    let mut thy = parse_theory(&src, &["diff"]).unwrap();
    let preds: Vec<_> = thy.items.iter().filter_map(|i| match i {
        p::TheoryItem::Predicates(ps) => Some(ps.clone()),
        _ => None,
    }).flatten().collect();
    println!("Found {} predicate definitions", preds.len());
    for pr in &preds {
        println!("  pred {}({} args)", pr.fact.name, pr.fact.args.len());
    }

    println!("\nLemmas before expansion:");
    for it in &thy.items {
        if let p::TheoryItem::Lemma(l) = it {
            println!("  {}: {:?}", l.name, l.formula);
        }
    }

    expand_theory_formulas(&mut thy).unwrap();

    println!("\nLemmas after expansion:");
    for it in &thy.items {
        if let p::TheoryItem::Lemma(l) = it {
            println!("  {}: {:?}", l.name, l.formula);
        }
    }
}
