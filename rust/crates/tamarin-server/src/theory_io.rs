//! Parse + elaborate a `.spthy` file into a [`TheoryEntry`].

use chrono::Local;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use tamarin_parser::parse_theory;
use tamarin_theory::elaborate::elaborate;

use crate::state::{TheoryEntry, TheoryOrigin};

#[derive(Debug)]
pub enum LoadError {
    Io(String),
    Parse(String),
    Elaborate(String),
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Io(s) => write!(f, "IO error: {}", s),
            LoadError::Parse(s) => write!(f, "parse error: {}", s),
            LoadError::Elaborate(s) => write!(f, "elaboration error: {}", s),
        }
    }
}
impl std::error::Error for LoadError {}

/// Read the file, parse it, elaborate it, and return a [`TheoryEntry`].
///
/// `entry.idx` is left as `0`; [`TheoryStore::insert`] assigns the
/// real index.
pub fn load_from_path(path: &Path) -> Result<TheoryEntry, LoadError> {
    let src = std::fs::read_to_string(path)
        .map_err(|e| LoadError::Io(format!("{}: {}", path.display(), e)))?;
    load_from_source(&src, TheoryOrigin::Local(PathBuf::from(path)))
}

/// Parse + elaborate from a string (for the upload path).
pub fn load_from_source(
    src: &str,
    origin: TheoryOrigin,
) -> Result<TheoryEntry, LoadError> {
    let parser_theory = parse_theory(src, &[])
        .map_err(|e| LoadError::Parse(format!("{:?}", e)))?;
    let typed = elaborate(&parser_theory)
        .map_err(|e| LoadError::Elaborate(e.message))?;
    Ok(TheoryEntry {
        idx: 0,
        name: typed.name.clone(),
        parser_theory: Arc::new(parser_theory),
        typed_theory: Arc::new(typed),
        origin,
        loaded_at: Local::now(),
        primary: true,
        errors_html: String::new(),
        proof_state: None,
    })
}
