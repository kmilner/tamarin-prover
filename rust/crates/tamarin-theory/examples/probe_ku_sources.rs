use tamarin_theory::constraint::solver::context::ProofContext;
use tamarin_theory::constraint::constraints::Goal;
use tamarin_theory::fact::FactTag;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = &args[1];
    let want_case = args.get(2).cloned();
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
                for (name, sys) in &src.cases {
                    let unsolved_prem_goals: usize = sys.goals.iter()
                        .filter(|(g, st)| !st.solved && matches!(g,
                            tamarin_theory::constraint::constraints::Goal::Premise(_, _)))
                        .count();
                    let chains: usize = sys.goals.iter()
                        .filter(|(g, st)| !st.solved && matches!(g,
                            tamarin_theory::constraint::constraints::Goal::Chain(_, _)))
                        .count();
                    println!("  case: {} nodes={} edges={} open_prems={} chains={} eqs={}",
                        name, sys.nodes.len(), sys.edges.len(),
                        unsolved_prem_goals, chains,
                        sys.eq_store.subst.to_list().len());
                    if want_case.as_deref() == Some(name) {
                        println!("    -- subst entries --");
                        for (v, t) in sys.eq_store.subst.to_list().iter() {
                            println!("      {:?} → {:?}", v, t);
                        }
                        println!("    -- nodes --");
                        for (id, rule) in sys.nodes.iter() {
                            let name = tamarin_theory::constraint::solver::reduction::rule_case_name(rule);
                            println!("      {:?} = {}", id, name);
                        }
                        println!("    -- goals --");
                        for (g, st) in sys.goals.iter() {
                            let extra = match g {
                                tamarin_theory::constraint::constraints::Goal::Split(id) => {
                                    sys.eq_store.split_size(*id)
                                        .map(|sz| format!(" SIZE={}", sz))
                                        .unwrap_or_default()
                                }
                                _ => String::new(),
                            };
                            println!("      [{}] {:?}{}",
                                if st.solved { "S" } else { "-" },
                                g, extra);
                        }
                    }
                }
            }
        }
    }
}
