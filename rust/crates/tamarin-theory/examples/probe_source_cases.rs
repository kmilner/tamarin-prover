//! Dump the precomputed source-cases for a theory — useful for
//! inspecting what's still open after `precompute_full_sources` /
//! `saturate_sources_with_simp`.

use tamarin_theory::constraint::solver::context::ProofContext;

fn maude_path() -> String {
    for c in [
        "/home/linuxbrew/.linuxbrew/bin/maude",
        "/usr/local/bin/maude",
        "maude",
    ] {
        if std::path::Path::new(c).exists() {
            return c.to_string();
        }
    }
    "maude".to_string()
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: probe_source_cases <PATH>");
    let src = std::fs::read_to_string(&path).expect("read");
    let parser_thy = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let typed_thy = tamarin_theory::elaborate::elaborate(&parser_thy).expect("elab");

    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &maude_path(),
        typed_thy.signature.maude_sig.clone(),
    ).expect("maude");

    let rules: Vec<_> = typed_thy.rules().cloned().collect();
    let ctx = ProofContext::new(h, rules);

    println!("Full sources ({}):", ctx.full_sources.len());
    for src in &ctx.full_sources {
        println!("\n  Goal: {:?}", src.goal);
        let cases = src.cases(&ctx);
        println!("  Cases ({}):", cases.len());
        for (name, sys) in &cases {
            println!("    \"{}\":", name);
            println!("      nodes: {}, edges: {}, less: {}, formulas: {}",
                sys.nodes.len(), sys.edges.len(), sys.less_atoms.len(),
                sys.formulas.len());
            let open_goals: Vec<_> = sys.goals.iter()
                .filter(|(_, s)| !s.solved)
                .collect();
            if !open_goals.is_empty() {
                println!("      OPEN goals ({}):", open_goals.len());
                for (g, _) in open_goals {
                    println!("        {:?}", g);
                }
            }
        }
    }
}
