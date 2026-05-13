//! Drive a proof until it hits "no method", then dump the state and
//! show what goals exist but aren't picked.

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
    let path = std::env::args().nth(1).expect("usage: probe_no_method <PATH> <LEMMA>");
    let lemma_name = std::env::args().nth(2).expect("usage: probe_no_method <PATH> <LEMMA>");
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

    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &maude_path(),
        typed_thy.signature.maude_sig.clone(),
    ).expect("maude");

    let mut sys = formula_to_system(
        restrictions,
        SourceKind::RawSources,
        lemma.trace_quantifier.clone(),
        false,
        &g,
    );
    let rules: Vec<_> = typed_thy.rules().cloned().collect();
    let ctx = ProofContext::new(h, rules);

    // Drive: simplify, then keep solving the first ranked goal until
    // we either finish or get stuck.
    let step_limit: usize = std::env::args().nth(3).and_then(|s| s.parse().ok()).unwrap_or(20);
    // Try Induction first if the lemma demands it (use_induction
    // attribute or no rules match initial simplify).  For [sources]
    // typing lemmas this is mandatory.
    if let Some(map) = exec_proof_method(&ctx, &ProofMethod::Induction, &sys) {
        if let Some((_, step_sys)) = map.into_iter().find(|(k, _)| k == "non_empty_trace") {
            println!("Step pre: Induction → non_empty_trace");
            sys = step_sys;
        }
    }
    for step in 0..step_limit {
        if let Some(r) = is_finished(&ctx, &sys) {
            println!("Step {}: finished — {:?}", step, r);
            println!("  formulas remaining ({}):", sys.formulas.len());
            for (idx, f) in sys.formulas.iter().take(4).enumerate() {
                println!("    [{}] {:?}", idx, f);
            }
            println!("  unsolved goals: {}",
                sys.goals.iter().filter(|(_, s)| !s.solved).count());
            println!("  nodes: {}", sys.nodes.len());
            for (id, rule) in &sys.nodes {
                let rname = match &rule.info {
                    tamarin_theory::rule::RuleInfo::Proto(p) =>
                        format!("Proto({:?})", p.name),
                    tamarin_theory::rule::RuleInfo::Intr(i) =>
                        format!("Intr({:?})", i),
                };
                println!("    {:?} = {} prems={} acts={} concs={}",
                    id, rname, rule.premises.len(),
                    rule.actions.len(), rule.conclusions.len());
                for (i, p) in rule.premises.iter().enumerate() {
                    let t = p.terms.first().map(|x|
                        format!("{:?}", x).chars().take(60).collect::<String>())
                        .unwrap_or_default();
                    println!("      prem[{}] tag={:?} term={}", i, p.tag, t);
                }
                for (i, c) in rule.conclusions.iter().enumerate() {
                    let t = c.terms.first().map(|x|
                        format!("{:?}", x).chars().take(60).collect::<String>())
                        .unwrap_or_default();
                    println!("      conc[{}] tag={:?} term={}", i, c.tag, t);
                }
            }
            println!("  edges: {}", sys.edges.len());
            for e in &sys.edges {
                println!("    {:?}.{:?} → {:?}.{:?}",
                    e.src.0, e.src.1, e.tgt.0, e.tgt.1);
            }
            return;
        }

        // Try Simplify first.
        if let Some(map) = exec_proof_method(&ctx, &ProofMethod::Simplify, &sys) {
            let new_sys = map.into_iter().next().unwrap().1;
            println!("Step {}: Simplify", step);
            sys = new_sys;
            continue;
        }

        // Pick first open goal.
        let goal = tamarin_theory::constraint::solver::goals::rank_goals_with(&sys, Some(&ctx))
            .into_iter()
            .next()
            .map(|a| a.goal);
        let goal = match goal {
            Some(g) => g,
            None => {
                println!("Step {}: NO METHOD", step);
                println!("\n=== State at no-method point ===");
                println!("formulas: {}, goals: {}, nodes: {}, less: {}, edges: {}",
                    sys.formulas.len(), sys.goals.len(),
                    sys.nodes.len(), sys.less_atoms.len(), sys.edges.len());
                println!("\nAll goals:");
                for (g, st) in &sys.goals {
                    println!("  solved={} looping={} {:?}", st.solved, st.looping, g);
                }
                println!("\nOpen-goal filter (is_open + non-solved):");
                let opens = tamarin_theory::constraint::solver::goals::open_goals(&sys);
                println!("  count = {}", opens.len());
                for a in &opens {
                    println!("    seq={} usefulness={:?} goal={:?}",
                        a.seq, a.usefulness, a.goal);
                }
                return;
            }
        };
        // Brief goal summary.
        let goal_summary = match &goal {
            tamarin_theory::constraint::constraints::Goal::Action(n, fa) =>
                format!("Action({:?}({:?})@{:?})", fa.tag,
                    fa.terms.first().map(|t| format!("{:?}", t)).unwrap_or_default(),
                    n),
            tamarin_theory::constraint::constraints::Goal::Premise(p, fa) =>
                format!("Premise({:?}@{:?})", fa.tag, p.0),
            tamarin_theory::constraint::constraints::Goal::Chain(c, _) =>
                format!("Chain({:?})", c.0),
            other => format!("{:?}", other),
        };
        println!("Step {}: Solve {}", step, goal_summary);
        let method = ProofMethod::SolveGoal(goal);
        let map = exec_proof_method(&ctx, &method, &sys).expect("solve");
        // Always print cases (full distribution).
        println!("  {} cases: {:?}", map.len(), map.keys().collect::<Vec<_>>());
        // Take the first case (matches search's depth-first traversal).
        sys = map.into_iter().next().unwrap().1;
        // Print eq-store summary.
        if !sys.eq_store.subst.to_list().is_empty() {
            println!("  eq_store ({} entries):", sys.eq_store.subst.to_list().len());
            for (v, t) in sys.eq_store.subst.to_list().iter() {
                // Show just var name+idx → term-summary for brevity.
                let v_str = format!("{}#{}({:?})", v.name, v.idx, v.sort);
                println!("    {} → {:?}", v_str, t);
            }
        }
    }
    println!("Hit step limit");
}
