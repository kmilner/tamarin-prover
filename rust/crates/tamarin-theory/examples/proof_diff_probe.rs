//! Cross-check our proof skeleton against `tamarin-prover`'s `--output=`.
//!
//! Usage:
//!   cargo run --example proof_diff_probe -- <PATH.spthy> [<LEMMA>]
//!
//! With no lemma name: dumps a one-line summary per lemma (match /
//! diff-line / our-status).
//!
//! With a lemma name: prints both skeletons + the first divergence.

use std::process::Command;
use tamarin_parser::ast::{TheoryItem, TraceQuantifier};
use tamarin_theory::proof_skeleton::{extract_from_haskell, first_divergence, render};
use tamarin_theory::prove::prove_lemma;

fn maude_path() -> String {
    if let Ok(p) = std::env::var("MAUDE_PATH") {
        return p;
    }
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
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: proof_diff_probe <PATH.spthy> [<LEMMA>]");
        std::process::exit(2);
    }
    let path = &args[1];
    let focus_lemma = args.get(2).cloned();

    let src = std::fs::read_to_string(path).expect("read source");
    let theory = tamarin_parser::parse_theory(&src, &[]).expect("parse");

    // 1) Run tamarin to get its proof skeleton.
    eprintln!("running tamarin --output=...");
    let tam_output_path = format!("/tmp/proof_diff_{}.spthy", std::process::id());
    let _ = Command::new("timeout")
        .args(["60s", "tamarin-prover", "--prove"])
        .arg(format!("--output={}", tam_output_path))
        .arg(path)
        .output()
        .expect("invoke tamarin-prover");
    let tam_text = std::fs::read_to_string(&tam_output_path).expect("read tamarin output");

    // 2) For each lemma (or just the focus lemma), run our prover and
    //    diff against the tamarin skeleton.
    let mp = maude_path();
    let elab_sig = match tamarin_theory::elaborate::elaborate(&theory) {
        Ok(e) => Some(e.signature.maude_sig.clone()),
        Err(_) => None,
    };

    let mut total = 0;
    let mut matched = 0;
    for it in &theory.items {
        let lemma = match it {
            TheoryItem::Lemma(l) => l,
            _ => continue,
        };
        if let Some(name) = &focus_lemma {
            if &lemma.name != name {
                continue;
            }
        }
        total += 1;

        let theirs = match extract_from_haskell(&tam_text, &lemma.name) {
            Some(s) => s,
            None => {
                eprintln!("[{}] tamarin produced no proof skeleton (skipping)", lemma.name);
                continue;
            }
        };

        // Run our prover.
        let h = match tamarin_term::maude_proc::MaudeHandle::start(
            &mp,
            elab_sig.clone().unwrap_or_else(tamarin_term::maude_sig::pair_maude_sig),
        ) {
            Ok(h) => h,
            Err(e) => {
                eprintln!("[{}] maude failed: {:?}", lemma.name, e);
                continue;
            }
        };
        std::env::set_var("TAM_PROVE_DEADLINE_MS", "3000");
        let root = match prove_lemma(&theory, &lemma.name, h, 300) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("[{}] prove failed: {:?}", lemma.name, e);
                continue;
            }
        };

        let ours = render(&root);
        let div = first_divergence(&ours, &theirs);

        let our_verdict = match (&lemma.trace_quantifier, &root.status) {
            (TraceQuantifier::ExistsTrace, tamarin_theory::constraint::solver::search::NodeStatus::Solved) => "verified",
            (TraceQuantifier::ExistsTrace, tamarin_theory::constraint::solver::search::NodeStatus::Contradictory) => "falsified",
            (TraceQuantifier::AllTraces, tamarin_theory::constraint::solver::search::NodeStatus::Contradictory) => "verified",
            (TraceQuantifier::AllTraces, tamarin_theory::constraint::solver::search::NodeStatus::Solved) => "falsified",
            (_, tamarin_theory::constraint::solver::search::NodeStatus::Sorry) => "sorry",
            (_, tamarin_theory::constraint::solver::search::NodeStatus::Unfinishable) => "unfinishable",
            (_, tamarin_theory::constraint::solver::search::NodeStatus::Open) => "open",
        };

        match (&focus_lemma, &div) {
            (Some(_), Some((line, ours_l, theirs_l))) => {
                println!("--- OURS ({}) ---", lemma.name);
                println!("{}", ours);
                println!("--- THEIRS ({}) ---", lemma.name);
                println!("{}", theirs);
                println!("--- FIRST DIVERGENCE at line {} ---", line);
                println!("  ours:   {:?}", ours_l);
                println!("  theirs: {:?}", theirs_l);
                println!("(verdict: {})", our_verdict);
            }
            (Some(_), None) => {
                println!("--- OURS ({}) ---", lemma.name);
                println!("{}", ours);
                println!("✓ skeletons match (verdict: {})", our_verdict);
            }
            (None, Some((line, ours_l, theirs_l))) => {
                println!(
                    "[{}] DIVERGE line {}: ours={:?} theirs={:?} (verdict: {})",
                    lemma.name, line, ours_l, theirs_l, our_verdict
                );
            }
            (None, None) => {
                matched += 1;
                println!("[{}] ✓ match (verdict: {})", lemma.name, our_verdict);
            }
        }
    }

    if focus_lemma.is_none() {
        println!("---");
        println!("skeleton-match: {}/{} lemmas", matched, total);
    }
}
