use tamarin_theory::constraint::solver::context::ProofContext;
use tamarin_theory::constraint::constraints::Goal;

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
    for (idx, src) in ctx.full_sources.iter().enumerate() {
        let goal_str = match &src.goal {
            Goal::Action(_, fa) => format!("Action({:?})", fa.tag),
            Goal::Premise(_, fa) => format!("Premise({:?})", fa.tag),
            other => format!("{:?}", other),
        };
        println!("[{}] {} -> {} cases:", idx, goal_str, src.cases.len());
        for (n, _) in &src.cases {
            println!("    {}", n);
        }
    }
}
