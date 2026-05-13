//! Dump system state after the initial simplify on a single lemma.
//! Useful for diagnosing why simplify isn't closing a lemma that
//! Haskell closes in `simplify / by contradiction`.
//!
//! Usage:
//!   cargo run --example probe_simplify_dump -- <PATH.spthy> <LEMMA>

use tamarin_parser::ast::TheoryItem;
use tamarin_theory::constraint::solver::context::ProofContext;
use tamarin_theory::constraint::solver::proof_method::{exec_proof_method, is_finished, ProofMethod};
use tamarin_theory::constraint::system::{formula_to_system, SourceKind};

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
    let path = std::env::args().nth(1).expect("usage: probe_simplify_dump <PATH.spthy> <LEMMA>");
    let lemma_name = std::env::args().nth(2).expect("usage: probe_simplify_dump <PATH.spthy> <LEMMA>");
    let src = std::fs::read_to_string(&path).expect("read");
    let parser_thy = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let typed_thy = tamarin_theory::elaborate::elaborate(&parser_thy).expect("elab");
    let lemma = parser_thy.items.iter().find_map(|it| match it {
        TheoryItem::Lemma(l) if l.name == lemma_name => Some(l),
        _ => None,
    }).expect("lemma");

    let g = tamarin_theory::guarded::formula_to_guarded(&lemma.formula).expect("guard");
    let mut restrictions: Vec<_> = Vec::new();
    for r in typed_thy.restrictions() {
        if let Ok(rg) = tamarin_theory::guarded::formula_to_guarded(&r.formula) {
            restrictions.push(rg);
        }
    }

    let mp = maude_path();
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &mp,
        typed_thy.signature.maude_sig.clone(),
    ).expect("maude");

    let sys0 = formula_to_system(
        restrictions,
        SourceKind::RawSources,
        lemma.trace_quantifier.clone(),
        false,
        &g,
    );
    let rules: Vec<_> = typed_thy.rules().cloned().collect();
    let ctx = ProofContext::new(h, rules);

    println!("--- Initial system (pre-simplify) ---");
    println!("formulas:  {}", sys0.formulas.len());
    println!("goals:     {}", sys0.goals.len());
    println!("nodes:     {}", sys0.nodes.len());
    println!("less:      {}", sys0.less_atoms.len());
    println!("edges:     {}", sys0.edges.len());

    let after = exec_proof_method(&ctx, &ProofMethod::Simplify, &sys0).expect("simplify");
    let s1 = after.into_iter().next().unwrap().1;

    println!("\n--- After simplify ---");
    println!("formulas:  {}", s1.formulas.len());
    for (i, f) in s1.formulas.iter().enumerate() {
        println!("  [{}] {:?}", i, f);
    }
    println!("\ngoals:");
    for (g, st) in &s1.goals {
        println!("  solved={} {:?}", st.solved, g);
    }
    println!("\nnodes ({}):", s1.nodes.len());
    for (id, r) in &s1.nodes {
        let prems: Vec<_> = r.premises.iter().map(|f|
            format!("{:?}({})", &f.tag,
                f.terms.iter().map(|t| format!("{:?}", t)).collect::<Vec<_>>().join(","))).collect();
        let acts: Vec<_> = r.actions.iter().map(|f|
            format!("{:?}({})", &f.tag,
                f.terms.iter().map(|t| format!("{:?}", t)).collect::<Vec<_>>().join(","))).collect();
        let concs: Vec<_> = r.conclusions.iter().map(|f|
            format!("{:?}({})", &f.tag,
                f.terms.iter().map(|t| format!("{:?}", t)).collect::<Vec<_>>().join(","))).collect();
        println!("  {:?}: [{}] -[{}]-> [{}]",
            id, prems.join(", "), acts.join(", "), concs.join(", "));
    }
    println!("\nless_atoms ({}):", s1.less_atoms.len());
    for l in &s1.less_atoms { println!("  {:?} < {:?} ({:?})", l.smaller, l.larger, l.reason); }
    println!("\nedges ({}):", s1.edges.len());
    for e in &s1.edges { println!("  {:?}@{:?} -> {:?}@{:?}", e.src.0, e.src.1, e.tgt.0, e.tgt.1); }
    println!("\nis_finished: {:?}", is_finished(&ctx, &s1));
    println!("contradictions: {:?}",
        tamarin_theory::constraint::solver::contradictions::contradictions(&ctx, &s1));

    // Idempotence check: a converged simplify should be a no-op.
    // Non-idempotence here indicates a non-progressing pass (e.g. a
    // ping-pong between two equivalent forms, or repeated push to
    // solved_formulas).  See project_rust_simplify_idempotence.md.
    let after2 = exec_proof_method(&ctx, &ProofMethod::Simplify, &s1);
    match after2 {
        None => println!("\n2nd simplify: None (idempotent ✓)"),
        Some(map) => {
            let s2 = map.into_iter().next().unwrap().1;
            if s2 == s1 {
                println!("\n2nd simplify: Some but identical");
            } else {
                println!("\n2nd simplify: CHANGED — non-idempotent!");
                println!("  solved_formulas: {} → {}",
                    s1.solved_formulas.len(), s2.solved_formulas.len());
                println!("  formulas: {} → {}, goals: {} → {}, nodes: {} → {}",
                    s1.formulas.len(), s2.formulas.len(),
                    s1.goals.len(), s2.goals.len(),
                    s1.nodes.len(), s2.nodes.len());
            }
        }
    }
}
