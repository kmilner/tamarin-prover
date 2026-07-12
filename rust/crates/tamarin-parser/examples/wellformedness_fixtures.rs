//! Run the wellformedness fixture corpus against:
//!
//!   1. Our parser — every fixture must parse without error.
//!   2. Our Rust wellformedness checker — the topics it emits must
//!      include every expected topic from `expected.txt`.
//!   3. Tamarin (binary) — the expected topics must also be a subset of
//!      what `tamarin-prover` actually emits, confirming we're shooting
//!      at the right targets.
//!
//! Usage:  cargo run -p tamarin-parser --example wellformedness_fixtures \
//!           [-- <fixtures-dir>]
//!
//! Pass `--no-tamarin` to skip the Tamarin oracle pass (e.g. on systems
//! without the binary installed).

// Example/dev tool: prints fixture results to stdout by design; allow the
// `disallowed_macros` convention freeze for this example binary.
#![allow(clippy::disallowed_macros)]

use std::collections::BTreeSet;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;

use tamarin_parser::{parse_theory, wf};

fn main() {
    let args = env::args().skip(1);
    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent().unwrap()
        .parent().unwrap()
        .join("tests")
        .join("wellformedness_fixtures");
    let mut run_tamarin_oracle = true;
    let mut positional: Vec<String> = Vec::new();
    for a in args {
        match a.as_str() {
            "--no-tamarin" => run_tamarin_oracle = false,
            other => positional.push(other.to_string()),
        }
    }
    if let Some(a) = positional.into_iter().next() { dir = PathBuf::from(a); }
    let tamarin = env::var("TAMARIN").unwrap_or_else(|_| "tamarin-prover".into());

    let expected_path = dir.join("expected.txt");
    let expected = fs::read_to_string(&expected_path)
        .unwrap_or_else(|_| panic!("missing expected.txt at {}", expected_path.display()));

    let mut total = 0usize;
    let mut parser_ok = 0usize;
    let mut rust_wf_match = 0usize;
    let mut topics_match = 0usize;
    let mut fail_lines: Vec<String> = Vec::new();

    for line in expected.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') { continue; }
        let (lhs, rhs) = match line.split_once(':') { Some(p) => p, None => continue };
        let mut parts = lhs.split_whitespace();
        let name = match parts.next() { Some(n) => n, None => continue };
        let mut flags: Vec<String> = Vec::new();
        for f in parts { flags.push(f.to_string()); }
        let expected_topics: BTreeSet<String> = rhs
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();

        total += 1;

        let path = dir.join(format!("{}.spthy", name));
        let src = fs::read_to_string(&path).unwrap_or_else(|_| panic!("missing {}", path.display()));

        // 1. Our parser must accept the fixture.
        let mut thy = match parse_theory(&src, &["diff"]) {
            Ok(t) => { parser_ok += 1; t }
            Err(e) => {
                fail_lines.push(format!("PARSE  {}: {}", name, e));
                continue;
            }
        };
        // Override is_diff if the fixture is flagged --diff. Our parser
        // doesn't auto-detect diff mode (Tamarin uses a separate
        // entry point), so we surface it from the fixture metadata.
        if flags.iter().any(|f| f == "--diff") { thy.is_diff = true; }

        // 2. Our Rust wf checker must emit every expected topic.
        let rust_topics = wf::topics(&wf::check_theory(&thy));
        if expected_topics.is_subset(&rust_topics) {
            rust_wf_match += 1;
        } else {
            let missing: Vec<_> = expected_topics.difference(&rust_topics).collect();
            fail_lines.push(format!(
                "RUST   {}: missing {:?} (got: {:?})", name, missing, rust_topics));
        }

        // 3. (Optional) Tamarin must emit the expected topics.
        if run_tamarin_oracle {
            let actual = run_tamarin(&tamarin, &path, &flags).unwrap_or_default();
            if expected_topics.is_subset(&actual) {
                topics_match += 1;
            } else {
                let missing: Vec<_> = expected_topics.difference(&actual).collect();
                fail_lines.push(format!(
                    "TOPICS {}: missing {:?} (actual: {:?})", name, missing, actual));
            }
        }
    }

    println!("Fixtures total:   {}", total);
    println!("Parsed OK:        {} ({:.0}%)",
        parser_ok, 100.0 * parser_ok as f64 / total.max(1) as f64);
    println!("Rust wf match:    {} ({:.0}%)",
        rust_wf_match, 100.0 * rust_wf_match as f64 / total.max(1) as f64);
    if run_tamarin_oracle {
        println!("Tamarin match:    {} ({:.0}%)",
            topics_match, 100.0 * topics_match as f64 / total.max(1) as f64);
    }
    if !fail_lines.is_empty() {
        println!("\nFailures:");
        for l in fail_lines { println!("  {}", l); }
        std::process::exit(1);
    }
}

fn run_tamarin(bin: &str, path: &std::path::Path, flags: &[String]) -> Option<BTreeSet<String>> {
    let mut cmd = Command::new(bin);
    for f in flags { cmd.arg(f); }
    cmd.arg(path);
    let out = cmd.output().ok()?;
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    Some(extract_topics(&combined))
}

/// A wellformedness topic header is a line followed by a line of `=`
/// characters whose length equals (or exceeds) the topic name.
fn extract_topics(s: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut prev: Option<&str> = None;
    for line in s.lines() {
        if !line.is_empty() && line.chars().all(|c| c == '=') {
            if let Some(p) = prev {
                let p = p.trim();
                if !p.is_empty() {
                    // Filter banner lines that aren't actual topics.
                    if !p.starts_with("analyzed:")
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
        }
        prev = Some(line);
    }
    out
}
