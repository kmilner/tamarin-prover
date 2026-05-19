use std::time::Instant;
use tamarin_parser::ast::TheoryItem;
use tamarin_theory::prove::prove_lemma;
use tamarin_theory::constraint::solver::search::NodeStatus;

fn maude_path() -> String {
    for c in ["/home/linuxbrew/.linuxbrew/bin/maude", "/usr/local/bin/maude", "maude"] {
        if std::path::Path::new(c).exists() { return c.to_string(); }
    }
    "maude".into()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = &args[1];
    let lemma_name = &args[2];
    let budget: usize = args.get(3).map(|s| s.parse().unwrap_or(500)).unwrap_or(500);
    let deadline_ms: u64 = std::env::var("TAM_PROVE_DEADLINE_MS").ok().and_then(|s| s.parse().ok()).unwrap_or(30000);
    std::env::set_var("TAM_PROVE_DEADLINE_MS", deadline_ms.to_string());

    let src = std::fs::read_to_string(path).expect("read");
    let theory = tamarin_parser::parse_theory(&src, &[]).expect("parse");
    let lemma = theory.items.iter().find_map(|it| match it {
        TheoryItem::Lemma(l) if l.name == *lemma_name => Some(l.clone()),
        _ => None,
    }).expect("lemma not found");

    let elab_sig = match tamarin_theory::elaborate::elaborate(&theory) {
        Ok(e) => Some(e.signature.maude_sig.clone()),
        Err(_) => None,
    };
    let h = tamarin_term::maude_proc::MaudeHandle::start(
        &maude_path(),
        elab_sig.unwrap_or_else(tamarin_term::maude_sig::pair_maude_sig),
    ).unwrap();

    let stats_handle = h.clone();
    let t = Instant::now();
    let root = prove_lemma(&theory, lemma_name, h, budget).expect("prove");
    println!("lemma={} budget={} deadline={}ms elapsed={}ms status={:?}",
        lemma_name, budget, deadline_ms, t.elapsed().as_millis(), root.status);
    let stats = stats_handle.stats();
    println!("maude_stats: unify={} match={} norm={} var={}",
        stats.unify_count, stats.match_count, stats.norm_count, stats.var_count);
    if std::env::var("TAM_DUMP_PROOF").is_ok() {
        println!("---");
        println!("{}", tamarin_theory::proof_skeleton::render(&root));
    }
    if std::env::var("TAM_DUMP_PATH").is_ok() {
        // Path follows the named children, defaulting to first.
        let path_str = std::env::var("TAM_DUMP_PATH").unwrap_or_default();
        let path: Vec<&str> = if path_str == "1" { Vec::new() } else { path_str.split(',').collect() };
        let dump_at_depth: Option<usize> = std::env::var("TAM_DUMP_AT").ok()
            .and_then(|s| s.parse().ok());
        fn dump_path(
            node: &tamarin_theory::constraint::solver::search::ProofNode,
            depth: usize,
            remaining_path: &[&str],
            dump_at_depth: Option<usize>,
        ) {
            let pad = "  ".repeat(depth);
            println!("{}--- depth {} status={:?} method={:?} ---", pad, depth, node.status, node.method);
            println!("{}nodes={} edges={} goals={} subst.len={} is_false={} children={}",
                pad, node.sys.nodes.len(), node.sys.edges.len(), node.sys.goals.len(),
                node.sys.eq_store.subst.to_list().len(),
                node.sys.eq_store.is_false(),
                node.children.len());
            for (name, c) in &node.children {
                println!("{}  child: {:?} status={:?}", pad, name, c.status);
            }
            if node.sys.eq_store.is_false() {
                println!("{}>>> is_false detected at this node", pad);
            }
            if dump_at_depth == Some(depth) {
                println!("{}=== FULL DUMP at depth {} ===", pad, depth);
                println!("{}-- nodes --", pad);
                for (id, ru) in &node.sys.nodes {
                    println!("{}  {:?} → {}", pad, id,
                        tamarin_theory::constraint::solver::reduction::rule_case_name(ru));
                    for (i, p) in ru.premises.iter().enumerate() {
                        println!("{}    prem[{}]: {:?} {:?}", pad, i, p.tag, p.terms);
                    }
                    for (i, a) in ru.actions.iter().enumerate() {
                        println!("{}    act[{}]:  {:?} {:?}", pad, i, a.tag, a.terms);
                    }
                    for (i, c) in ru.conclusions.iter().enumerate() {
                        println!("{}    conc[{}]: {:?} {:?}", pad, i, c.tag, c.terms);
                    }
                }
                println!("{}-- edges --", pad);
                for e in &node.sys.edges {
                    println!("{}  {:?} → {:?}", pad, e.src, e.tgt);
                }
                println!("{}-- less_atoms ({}) --", pad, node.sys.less_atoms.len());
                for l in &node.sys.less_atoms {
                    println!("{}  {:?} < {:?} ({:?})",
                        pad, l.smaller, l.larger, l.reason);
                }
                if let Some(la) = &node.sys.last_atom {
                    println!("{}-- last_atom: {:?} --", pad, la);
                }
                println!("{}-- goals --", pad);
                for (g, st) in &node.sys.goals {
                    println!("{}  solved={} loop={} {:?}", pad, st.solved, st.looping, g);
                }
                println!("{}-- subst --", pad);
                for (v, t) in node.sys.eq_store.subst.to_list().iter() {
                    println!("{}  {:?} → {:?}", pad, v, t);
                }
                println!("{}-- conj --", pad);
                for d in &node.sys.eq_store.conj {
                    println!("{}  disj id={:?} substs.len={}", pad, d.split_id, d.substs.len());
                }
                println!("{}-- formulas ({}) --", pad, node.sys.formulas.len());
                for f in &node.sys.formulas {
                    println!("{}  {:?}", pad,
                        format!("{:?}", f).chars().take(300).collect::<String>());
                }
                println!("{}-- solved_formulas ({}) --", pad,
                    node.sys.solved_formulas.len());
                for f in &node.sys.solved_formulas {
                    println!("{}  {:?}", pad,
                        format!("{:?}", f).chars().take(300).collect::<String>());
                }
            }
            // Pick next child by name from remaining_path, or first.
            // Solved-priority mode (TAM_DUMP_SOLVED=1) picks the first
            // Solved child instead, matching the renderer's traversal.
            let solved_priority = std::env::var("TAM_DUMP_SOLVED").is_ok();
            let next_child = if let Some((wanted, rest)) = remaining_path.split_first() {
                let found = node.children.iter().find(|(name, _)| name.as_str() == *wanted);
                if let Some((_, c)) = found {
                    Some((c, rest))
                } else {
                    println!("{}!! could not find child {:?} — stopping", pad, wanted);
                    None
                }
            } else if solved_priority {
                node.children.iter()
                    .find(|(_, c)| matches!(c.status, tamarin_theory::constraint::solver::search::NodeStatus::Solved))
                    .or_else(|| node.children.iter().next())
                    .map(|(_, c)| (c, &[][..]))
            } else if let Some((_, c)) = node.children.iter().next() {
                Some((c, &[][..]))
            } else {
                None
            };
            if let Some((c, rest)) = next_child {
                dump_path(c, depth + 1, rest, dump_at_depth);
            }
        }
        println!("--- PATH DUMP ---");
        dump_path(&root, 0, &path, dump_at_depth);
    }
    if std::env::var("TAM_DUMP_LEAF").is_ok() {
        // Walk to first Solved leaf and dump its system state.
        fn find_solved(node: &tamarin_theory::constraint::solver::search::ProofNode)
            -> Option<&tamarin_theory::constraint::solver::search::ProofNode>
        {
            if matches!(node.status, NodeStatus::Solved) && node.children.is_empty() {
                return Some(node);
            }
            for (_, c) in &node.children {
                if let Some(r) = find_solved(c) { return Some(r); }
            }
            None
        }
        if let Some(leaf) = find_solved(&root) {
            println!("--- SOLVED LEAF ---");
            println!("nodes ({}):", leaf.sys.nodes.len());
            for (id, ru) in &leaf.sys.nodes {
                println!("  {:?} -> {:?}", id, tamarin_theory::constraint::solver::reduction::rule_case_name(ru));
                for (i, p) in ru.premises.iter().enumerate() {
                    println!("    prem[{}]: {:?}({:?})", i, p.tag, p.terms);
                }
                for (i, a) in ru.actions.iter().enumerate() {
                    println!("    act[{}]:  {:?}({:?})", i, a.tag, a.terms);
                }
                for (i, c) in ru.conclusions.iter().enumerate() {
                    println!("    conc[{}]: {:?}({:?})", i, c.tag, c.terms);
                }
            }
            println!("edges ({}):", leaf.sys.edges.len());
            for e in &leaf.sys.edges {
                println!("  {:?} -> {:?}", e.src, e.tgt);
            }
            println!("goals ({}):", leaf.sys.goals.len());
            for (g, st) in &leaf.sys.goals {
                println!("  solved={} {:?}", st.solved, g);
            }
            println!("less_atoms ({}):", leaf.sys.less_atoms.len());
            for l in &leaf.sys.less_atoms {
                println!("  {:?}", l);
            }
            println!("eq_store: {:?}", leaf.sys.eq_store.subst);
        } else {
            println!("(no Solved leaf found)");
        }
    }
}
