//! Binary entry-point for the Rust `tamarin-prover` port.
//!
//! Stays small: parse argv → dispatch to [`tamarin_prover::run::run`]
//! → translate errors into a stderr message + non-zero exit code.

use std::process::ExitCode;

fn main() -> ExitCode {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let args = match tamarin_prover::parse_args(&raw) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error: {}\n", e);
            eprintln!("{}", tamarin_prover::cli::help_text());
            return ExitCode::from(2);
        }
    };
    match tamarin_prover::run(&args) {
        Ok(0) => ExitCode::SUCCESS,
        Ok(n) => ExitCode::from(n.try_into().unwrap_or(2)),
        Err(e) => {
            eprintln!("error: {}", e);
            ExitCode::from(2)
        }
    }
}
