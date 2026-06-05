//! Maude IO profiler - prints stats + per-callsite breakdown.
//! Set TAM_PROFILE_MAUDE=1 to enable callsite tallying.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use std::time::Instant;
use tamarin_parser::parse_theory;
use tamarin_theory::elaborate::elaborate;
use tamarin_theory::prove::prove_lemma;
use tamarin_term::maude_proc::{MaudeHandle, dump_callsite_profile};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let theory_path = &args[1];
    let lemma = &args[2];
    let source = std::fs::read_to_string(theory_path).expect("read theory");
    let parsed = parse_theory(&source, &[]).expect("parse theory");
    let elaborated = elaborate(&parsed).expect("elaborate");
    let maude = MaudeHandle::start("/home/linuxbrew/.linuxbrew/bin/maude", elaborated.signature.maude_sig.clone()).expect("start maude");
    let t0 = Instant::now();
    let _root = prove_lemma(&parsed, lemma, maude.clone(), 500).expect("prove");
    let elapsed = t0.elapsed();
    let stats = maude.stats();
    eprintln!("== total: {:.3}s | unify={} match={} norm={} var={}",
        elapsed.as_secs_f64(),
        stats.unify_count, stats.match_count, stats.norm_count, stats.var_count);
    let mut prof = dump_callsite_profile();
    prof.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (k, v) in prof.iter().take(15) {
        eprintln!("   {:>10}  {}", v, k);
    }
}
