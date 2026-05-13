//! Run our Rust wellformedness checker against the full upstream
//! examples corpus and count how many clean protocols (Tamarin reports
//! no warnings) we falsely flag. False positives indicate bugs in our
//! checker.
//!
//! Usage:  cargo run -p tamarin-parser --example wf_false_positives \
//!           --release [-- <root>]

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

use tamarin_parser::{parse_theory, wf};

fn main() {
    let root = env::args().nth(1).map(PathBuf::from).unwrap_or_else(|| {
        PathBuf::from("/home/parallels/tamarin-prover/examples")
    });
    let limit: Option<usize> = env::var("WF_LIMIT").ok().and_then(|s| s.parse().ok());

    let mut files: Vec<PathBuf> = walkdir::WalkDir::new(&root)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spthy"))
        .map(|e| e.path().to_path_buf())
        .collect();
    files.sort();
    if let Some(n) = limit { files.truncate(n); }

    let mut scanned = 0usize;
    let mut tamarin_clean = 0usize;
    let mut rust_flagged = 0usize;
    let mut false_positives: Vec<(PathBuf, BTreeSet<String>)> = Vec::new();

    for (i, path) in files.iter().enumerate() {
        let src = match fs::read_to_string(path) { Ok(s) => s, Err(_) => continue };
        let thy = match parse_theory(&src, &["diff"]) { Ok(t) => t, Err(_) => continue };
        scanned += 1;

        // Skip files Tamarin can't even handle.
        let tamarin_topics = match run_tamarin_topics(path) {
            Some(s) => s,
            None => continue,
        };
        if tamarin_topics.is_empty() { tamarin_clean += 1; }

        let rust_topics = wf::topics(&wf::check_theory(&thy));
        if !rust_topics.is_empty() { rust_flagged += 1; }

        // False positive: Tamarin had no warnings but our checker flagged something.
        let fp = tamarin_topics.is_empty() && !rust_topics.is_empty();
        if fp {
            false_positives.push((path.clone(), rust_topics.clone()));
        }
        if i % 5 == 0 || fp {
            eprintln!("[{:4}/{:4}] scanned={}, tam_clean={}, ours={}, fp={} ({})",
                i + 1, files.len(), scanned, tamarin_clean, rust_flagged,
                false_positives.len(),
                path.file_name().unwrap_or_default().to_string_lossy());
        }
    }

    println!("Scanned (parsed by both):  {}", scanned);
    println!("Tamarin clean:             {}", tamarin_clean);
    println!("Rust flagged:              {}", rust_flagged);
    println!("False positives:           {} ({:.1}%)",
        false_positives.len(),
        100.0 * false_positives.len() as f64 / tamarin_clean.max(1) as f64);

    if !false_positives.is_empty() {
        println!("\nFirst 10 false positives:");
        for (p, t) in false_positives.iter().take(10) {
            println!("  {}", p.display());
            println!("    {:?}", t);
        }

        // Bucket by topic to see what we're over-flagging.
        let mut by_topic: std::collections::BTreeMap<String, usize> = Default::default();
        for (_, ts) in &false_positives {
            for t in ts { *by_topic.entry(t.clone()).or_insert(0) += 1; }
        }
        let mut sorted: Vec<_> = by_topic.iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(a.1));
        println!("\nFalse-positive counts by topic:");
        for (t, n) in sorted.iter().take(15) {
            println!("  {:5}  {}", n, t);
        }
    }
}

fn run_tamarin_topics(path: &std::path::Path) -> Option<BTreeSet<String>> {
    let out = Command::new("tamarin-prover").arg(path).output().ok()?;
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Some(extract_topics(&combined))
}

fn extract_topics(s: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut prev: Option<&str> = None;
    for line in s.lines() {
        if !line.is_empty() && line.chars().all(|c| c == '=') {
            if let Some(p) = prev {
                let p = p.trim();
                if !p.is_empty()
                    && !p.starts_with("analyzed:")
                    && !p.starts_with("summary of summaries")
                    && !p.contains("Tamarin version")
                    && !p.contains("Maude version")
                    && !p.starts_with("theory ")
                    && !p.starts_with("Generated from:")
                    && !p.starts_with("Compiled at")
                {
                    out.insert(p.to_string());
                }
            }
        }
        prev = Some(line);
    }
    out
}
