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

    let t = Instant::now();
    let root = prove_lemma(&theory, lemma_name, h, budget).expect("prove");
    println!("lemma={} budget={} deadline={}ms elapsed={}ms status={:?}",
        lemma_name, budget, deadline_ms, t.elapsed().as_millis(), root.status);
}
