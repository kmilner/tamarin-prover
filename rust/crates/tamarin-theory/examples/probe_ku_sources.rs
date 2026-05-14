use tamarin_theory::constraint::solver::context::ProofContext;
use tamarin_theory::constraint::constraints::Goal;
use tamarin_theory::fact::FactTag;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = &args[1];
    let src = std::fs::read_to_string(path).unwrap();
    let theory = tamarin_parser::parse_theory(&src, &[]).unwrap();
    let elab = tamarin_theory::elaborate::elaborate(&theory).unwrap();
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        "/home/linuxbrew/.linuxbrew/bin/maude",
        elab.signature.maude_sig.clone(),
    ).unwrap();
    let rules: Vec<_> = elab.rules().cloned().collect();
    let ctx = ProofContext::new(h, rules);
    println!("Full sources count: {}", ctx.full_sources.len());
    for src in &ctx.full_sources {
        if let Goal::Action(_, fa) = &src.goal {
            if matches!(fa.tag, FactTag::Ku) {
                println!("KU source: pattern = {:?}", fa.terms.first());
                for (name, _) in &src.cases {
                    println!("  case: {}", name);
                }
            }
        }
    }
}
