use tamarin_theory::constraint::solver::context::ProofContext;
use tamarin_theory::constraint::constraints::Goal;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = &args[1];
    let only_idx: Option<usize> = args.get(2).and_then(|s| s.parse().ok());
    let only_case: Option<String> = args.get(3).cloned();
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
        if let Some(k) = only_idx { if k != idx { continue; } }
        let goal_str = match &src.goal {
            Goal::Action(_, fa) => format!("Action({:?}, terms={:?})", fa.tag, fa.terms),
            Goal::Premise(_, fa) => format!("Premise({:?}, terms={:?})", fa.tag, fa.terms),
            other => format!("{:?}", other),
        };
        let cases = src.cases(&ctx);
        println!("[{}] cdGoal={} -> {} cases:", idx, goal_str, cases.len());
        for (n, sys) in &cases {
            if let Some(ref c) = only_case { if c != n { continue; } }
            println!("    --- case: {} ---", n);
            println!("    nodes: {}", sys.nodes.len());
            for (id, ru) in sys.nodes.iter() {
                let info = match &ru.info {
                    tamarin_theory::rule::RuleInfo::Proto(p) =>
                        format!("Proto({:?})", p.name),
                    tamarin_theory::rule::RuleInfo::Intr(i) =>
                        format!("Intr({:?})", i),
                };
                let p: Vec<_> = ru.premises.iter().map(|f| (f.tag.clone(), f.terms.clone())).collect();
                let c: Vec<_> = ru.conclusions.iter().map(|f| (f.tag.clone(), f.terms.clone())).collect();
                println!("      {:?} {} prems={:?} concs={:?}", id, info, p, c);
            }
            println!("    edges: {}", sys.edges.len());
            for e in &sys.edges {
                println!("      {:?} → {:?}", e.src, e.tgt);
            }
            println!("    eq_store.subst:");
            for (v, t) in sys.eq_store.subst.to_list() {
                println!("      {:?} → {:?}", v, t);
            }
            println!("    goals:");
            for (g, st) in sys.goals.iter() {
                let solved = if st.solved { "S" } else { "-" };
                println!("      [{}] {:?}", solved, g);
            }
        }
    }
}
