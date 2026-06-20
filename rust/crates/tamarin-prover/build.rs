//! Embed git revision + build timestamp into the compiled binary so
//! `tamarin-prover --version` can mirror HS's `Generated from:` block.
//! Mirrors HS's Cabal-time TH that injects $(getGitDescribe) + $(getBuildTime).

use std::process::Command;

fn main() {
    // Git revision (full sha + branch).
    let rev = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());
    let branch = Command::new("git")
        .args(["rev-parse", "--abbrev-ref", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    // Build timestamp (UTC).  Avoid `Date.now()`-style nondeterminism
    // concerns — this runs at COMPILE time, not at proof time.
    let ts = Command::new("date")
        .args(["-u", "+%Y-%m-%d %H:%M:%S UTC"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string());

    println!("cargo:rustc-env=TAMARIN_GIT_REV={}", rev);
    println!("cargo:rustc-env=TAMARIN_GIT_BRANCH={}", branch);
    println!("cargo:rustc-env=TAMARIN_BUILD_TIMESTAMP={}", ts);
    // Retrigger the build when the recorded revision can change:
    //  - `.git/HEAD` covers a branch switch (and detached-HEAD moves).
    //  - the concrete ref file (`.git/refs/heads/<branch>`) covers a new
    //    commit on the current branch, which updates that file rather than
    //    `.git/HEAD`. Watching the file (not the `refs/heads` directory) is
    //    what reliably fires on a content change.
    //  - `.git/packed-refs` covers the case where the ref is packed and the
    //    loose ref file is absent (e.g. after `git gc`).
    let git_dir = "../../../.git";
    println!("cargo:rerun-if-changed={git_dir}/HEAD");
    // Resolve HEAD's symbolic ref target (e.g. "refs/heads/rust-port") and
    // watch that concrete file. If HEAD is detached or unreadable, the
    // HEAD/packed-refs watches still apply.
    if let Ok(head) = std::fs::read_to_string(format!("{git_dir}/HEAD")) {
        if let Some(ref_path) = head.trim().strip_prefix("ref: ") {
            println!("cargo:rerun-if-changed={git_dir}/{ref_path}");
        }
    }
    println!("cargo:rerun-if-changed={git_dir}/packed-refs");
}
