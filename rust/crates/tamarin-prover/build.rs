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
    // Re-run if .git/HEAD changes (branch switch / new commit).
    println!("cargo:rerun-if-changed=../../../.git/HEAD");
    println!("cargo:rerun-if-changed=../../../.git/refs/heads");
}
