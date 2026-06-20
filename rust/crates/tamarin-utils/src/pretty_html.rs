//! Port of `Text.PrettyPrint.Html` from `lib/utils/src/Text/PrettyPrint/Html.hs`.
//!
//! We reuse the plain `Doc` from `pretty.rs`. Two helpers do the work:
//! [`escape_html_entities`] for safe text, and [`render_html_doc`] which calls
//! `Doc::render_with` to wrap highlight spans in `<span class="hl_...">` tags
//! and post-processes the output to convert newlines and leading whitespace.

use crate::pretty::{Doc, HighlightStyle};

/// Escape the five HTML metacharacters.
pub fn escape_html_entities(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '&' => out.push_str("&amp;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            x => out.push(x),
        }
    }
    out
}

fn class_name(s: HighlightStyle) -> &'static str {
    match s {
        HighlightStyle::Comment => "hl_comment",
        HighlightStyle::Keyword => "hl_keyword",
        HighlightStyle::Operator => "hl_operator",
    }
}

/// `withTag tag attrs inner`: wrap `inner` in `<tag …>…</tag>`. Attributes
/// values are HTML-escaped.
pub fn with_tag(tag: &str, attrs: &[(&str, &str)], inner: &str) -> String {
    let mut s = String::new();
    s.push('<');
    s.push_str(tag);
    for (k, v) in attrs {
        s.push(' ');
        s.push_str(k);
        s.push_str("=\"");
        s.push_str(&escape_html_entities(v));
        s.push('"');
    }
    s.push('>');
    s.push_str(inner);
    s.push_str("</");
    s.push_str(tag);
    s.push('>');
    s
}

/// `closedTag tag attrs` → `<tag k="v" />`.
pub fn closed_tag(tag: &str, attrs: &[(&str, &str)]) -> String {
    let mut s = String::new();
    s.push('<');
    s.push_str(tag);
    for (k, v) in attrs {
        s.push(' ');
        s.push_str(k);
        s.push_str("=\"");
        s.push_str(&escape_html_entities(v));
        s.push('"');
    }
    s.push_str("/>");
    s
}

/// Render a `Doc` to HTML: highlight spans → `<span class="hl_...">…</span>`,
/// newlines → `<br/>`, and leading whitespace per line → `&nbsp;`.
///
/// Note: this is HTML-escape-aware *only* for highlight bodies. The caller is
/// expected to either feed already-safe text, or use `Doc::text` of escaped
/// content when text might contain `< > & " '`.
pub fn render_html_doc(doc: &Doc) -> String {
    let body = doc.render_with(&|style, content| {
        with_tag("span", &[("class", class_name(style))], content)
    });
    postprocess(&body)
}

/// Convert line breaks to `<br/>` and replace leading whitespace per line
/// with `&nbsp;` runs.
///
/// Mirrors `postprocessHtmlDoc = unlines . map (addBreak . indent) . lines`
/// (Html.hs:157-162). Note both `lines` (treats `\n` as a terminator, so a
/// trailing `\n` does not yield an extra empty line) and `unlines` (appends
/// `\n` after *every* line, including the last) are matched here.
pub fn postprocess(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    // Haskell `lines`: split on '\n' where '\n' is a line terminator. An empty
    // input yields no lines; a trailing '\n' does not produce a trailing empty
    // segment (`lines "a\n" == ["a"]`).
    let mut rest = s;
    loop {
        let (line, tail, more) = match rest.find('\n') {
            Some(idx) => (&rest[..idx], &rest[idx + 1..], true),
            None => {
                if rest.is_empty() {
                    break;
                }
                (rest, "", false)
            }
        };
        let leading = line.chars().take_while(|c| c.is_whitespace()).count();
        for _ in 0..leading {
            out.push_str("&nbsp;");
        }
        out.push_str(
            &line[line
                .char_indices()
                .nth(leading)
                .map(|(i, _)| i)
                .unwrap_or(line.len())..],
        );
        // addBreak + unlines: `<br/>` then a trailing newline for every line.
        out.push_str("<br/>");
        out.push('\n');
        if !more {
            break;
        }
        rest = tail;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty::{keyword, Doc};

    #[test]
    fn escape_basics() {
        assert_eq!(
            escape_html_entities("<a href=\"x\">&'</a>"),
            "&lt;a href=&quot;x&quot;&gt;&amp;&#39;&lt;/a&gt;"
        );
    }

    #[test]
    fn with_tag_includes_attrs() {
        assert_eq!(
            with_tag("span", &[("class", "hl")], "x"),
            "<span class=\"hl\">x</span>"
        );
    }

    #[test]
    fn closed_tag_self_closes() {
        assert_eq!(
            closed_tag("img", &[("src", "a.png")]),
            "<img src=\"a.png\"/>"
        );
    }

    #[test]
    fn render_with_highlight_wraps_keyword() {
        let d = keyword(Doc::text("rule")).cat_with(Doc::text(" foo"));
        let html = render_html_doc(&d);
        assert_eq!(html, "<span class=\"hl_keyword\">rule</span> foo<br/>\n");
    }

    #[test]
    fn postprocess_handles_indent_and_newlines() {
        let s = "a\n  b\nc";
        let p = postprocess(s);
        assert_eq!(p, "a<br/>\n&nbsp;&nbsp;b<br/>\nc<br/>\n");
    }
}
