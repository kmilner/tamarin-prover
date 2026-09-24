//! This crate provides Spthy language support for the [tree-sitter][] parsing library.
//!
//! Typically, you will use the [language][language func] function to add this language to a
//! tree-sitter [Parser][], and then use the parser to parse some code:
//!
//! ```
//! let code = "theory Example\nbegin\nrule Empty: [] --> [Out(<>) ]\nend";
//! let mut parser = tree_sitter::Parser::new();
//! let language = tree_sitter_spthy::LANGUAGE;
//! parser
//!     .set_language(&language.into())
//!     .expect("Error loading Spthy parser");
//! let tree = parser.parse(code, None).unwrap();
//! assert!(!tree.root_node().has_error());
//! ```
//!
//! [Language]: https://docs.rs/tree-sitter/*/tree_sitter/struct.Language.html
//! [language func]: fn.language.html
//! [Parser]: https://docs.rs/tree-sitter/*/tree_sitter/struct.Parser.html
//! [tree-sitter]: https://tree-sitter.github.io/

use tree_sitter_language::LanguageFn;

extern "C" {
    fn tree_sitter_spthy() -> *const ();
}

/// The tree-sitter [`LanguageFn`] for this grammar.
pub const LANGUAGE: LanguageFn = unsafe { LanguageFn::from_raw(tree_sitter_spthy) };

/// The content of the [`node-types.json`][] file for this grammar.
///
/// [`node-types.json`]: https://tree-sitter.github.io/tree-sitter/using-parsers#static-node-types
pub const NODE_TYPES: &str = include_str!("../../src/node-types.json");

// NOTE: uncomment these to include any queries that this grammar contains:

// pub const HIGHLIGHTS_QUERY: &str = include_str!("../../queries/highlights.scm");
// pub const INJECTIONS_QUERY: &str = include_str!("../../queries/injections.scm");
// pub const LOCALS_QUERY: &str = include_str!("../../queries/locals.scm");
// pub const TAGS_QUERY: &str = include_str!("../../queries/tags.scm");

#[cfg(test)]
mod tests {
    #[test]
    fn test_can_parse_grammar() {
        let mut parser = tree_sitter::Parser::new();
        parser
            .set_language(&super::LANGUAGE.into())
            .expect("Error loading Spthy parser");

        let source =
            "theory Example\nbegin\n/* scanner comment */\nrule Empty: [] --> [Out(<>) ]\nend";
        let tree = parser.parse(source, None).expect("Error parsing Spthy");
        assert!(
            !tree.root_node().has_error(),
            "Unexpected parse errors: {}",
            tree.root_node().to_sexp()
        );
    }

    #[test]
    fn test_global_heuristic_boundaries() {
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&super::LANGUAGE.into()).unwrap();

        // Use escaped bytes: the repository normalizes corpus files to LF.
        for boundary in ["\n", "\r\n    ", "\t", " /* boundary */", " // boundary\n"] {
            let source =
                format!("theory Test begin\nheuristic: s{boundary}s{{* comment *}}\nend\n");
            let tree = parser.parse(&source, None).unwrap();
            let root = tree.root_node();
            assert!(!root.has_error(), "{boundary:?}: {}", root.to_sexp());
            let mut cursor = root.walk();
            assert!(root
                .named_children(&mut cursor)
                .any(|node| node.kind() == "formal_comment"));
        }

        // Check native error flags too: CLI output can omit missing anonymous tokens.
        for source in [
            "theory Test begin\nheuristic: s\ni\nend\n",
            "theory Test begin\nheuristic: s text{* comment *}\nend\n",
            "theory Test begin\nheuristic: s",
        ] {
            let tree = parser.parse(source, None).unwrap();
            assert!(tree.root_node().has_error(), "{source:?}");
        }
    }

    #[test]
    fn test_incremental_heuristic_boundaries() {
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&super::LANGUAGE.into()).unwrap();
        let prefix = "theory Test begin\nheuristic: s";
        let suffix = "text{* comment *}\nend\n";
        let start = tree_sitter::Point::new(1, 12);
        let end_position = |separator: &str| {
            let mut point = start;
            for byte in separator.bytes() {
                if byte == b'\n' {
                    point.row += 1;
                    point.column = 0;
                } else {
                    point.column += 1;
                }
            }
            point
        };

        for (before, after, has_error) in [
            ("\n", " ", true),
            (" ", "\r\n", false),
            (" ", " /* boundary */", false),
            (" /* boundary */", " ", true),
        ] {
            let old_source = format!("{prefix}{before}{suffix}");
            let new_source = format!("{prefix}{after}{suffix}");
            let mut old_tree = parser.parse(&old_source, None).unwrap();
            old_tree.edit(&tree_sitter::InputEdit {
                start_byte: prefix.len(),
                old_end_byte: prefix.len() + before.len(),
                new_end_byte: prefix.len() + after.len(),
                start_position: start,
                old_end_position: end_position(before),
                new_end_position: end_position(after),
            });
            let incremental = parser.parse(&new_source, Some(&old_tree)).unwrap();
            let fresh = parser.parse(&new_source, None).unwrap();
            assert_eq!(
                incremental.root_node().has_error(),
                has_error,
                "{new_source:?}"
            );
            assert_eq!(fresh.root_node().has_error(), has_error, "{new_source:?}");
            assert_eq!(
                incremental.root_node().to_sexp(),
                fresh.root_node().to_sexp()
            );
        }
    }
}
