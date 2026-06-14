//! Port of `Text.PrettyPrint.Class` (and `Highlight`) from
//! `lib/utils/src/Text/PrettyPrint/Class.hs`.
//!
//! The Haskell version is a thin wrapper around `Text.PrettyPrint.HughesPJ`
//! plus a `Document` typeclass that lets the prover render to plain text or
//! to HTML via a different instance.
//!
//! We give up the full Hughes width-aware reflowing for now and provide a
//! line-based pretty-printer that supports the combinators the prover
//! actually uses: `text`, `<>`, `<+>` (`besides`), `$$` and `$-$`,
//! `hcat`/`hsep`/`vcat`, `nest`, and `caseEmpty`. Width-sensitive
//! `sep`/`cat` fall back to `vcat` (always-vertical) while `fsep`/`fcat` fall
//! back to `hsep`/`hcat` (always-horizontal); this is slightly verbose but
//! always correct. Improving them is a follow-up.
//!
//! Highlight styling (`Comment`/`Keyword`/`Operator`) is carried as an enum
//! tag on a `Doc` node; the plain-text renderer ignores it. The HTML renderer
//! lives in `pretty_html`.

use std::fmt::Write as _;

use crate::prelude_ext::flush_right;

/// Highlight style tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HighlightStyle {
    Keyword,
    Comment,
    Operator,
}

#[derive(Debug, Clone)]
enum Node {
    Empty,
    Text(String),
    /// Width-zero text. Renders normally but `width` reports 0 for it.
    ZeroWidth(String),
    Cat(Box<Node>, Box<Node>),
    /// Vertical concatenation: insert a newline between the two.
    Above(Box<Node>, Box<Node>),
    Nest(usize, Box<Node>),
    Highlight(HighlightStyle, Box<Node>),
}

/// A pretty-printable document.
#[derive(Debug, Clone)]
pub struct Doc(Node);

impl Default for Doc {
    fn default() -> Self { Doc::empty() }
}

impl Doc {
    pub fn empty() -> Self { Doc(Node::Empty) }
    pub fn text<S: Into<String>>(s: S) -> Self { Doc(Node::Text(s.into())) }
    pub fn char(c: char) -> Self { Doc(Node::Text(c.to_string())) }
    pub fn zero_width_text<S: Into<String>>(s: S) -> Self { Doc(Node::ZeroWidth(s.into())) }

    pub fn is_empty(&self) -> bool {
        fn check(n: &Node) -> bool {
            match n {
                Node::Empty => true,
                Node::Text(s) | Node::ZeroWidth(s) => s.is_empty(),
                Node::Cat(a, b) | Node::Above(a, b) => check(a) && check(b),
                Node::Nest(_, a) | Node::Highlight(_, a) => check(a),
            }
        }
        check(&self.0)
    }

    /// Render to a `String` ignoring highlight tags.
    pub fn render(&self) -> String {
        let lines = layout(&self.0, 0);
        let mut out = String::new();
        for (i, line) in lines.iter().enumerate() {
            if i > 0 { out.push('\n'); }
            for _ in 0..line.indent { out.push(' '); }
            out.push_str(&line.content);
        }
        out
    }

    /// Render to a `String` calling `wrap` to bracket each highlighted span.
    /// `wrap(style, body)` should return a wrapped form (e.g. with HTML tags).
    pub fn render_with<F: Fn(HighlightStyle, &str) -> String>(&self, wrap: &F) -> String {
        let lines = layout_with(&self.0, 0, wrap);
        let mut out = String::new();
        for (i, line) in lines.iter().enumerate() {
            if i > 0 { out.push('\n'); }
            for _ in 0..line.indent { out.push(' '); }
            out.push_str(&line.content);
        }
        out
    }

    /// `<>`: horizontal concatenation.
    pub fn cat_with(self, other: Doc) -> Doc {
        match (self.is_empty(), other.is_empty()) {
            (true, _) => other,
            (_, true) => self,
            _ => Doc(Node::Cat(Box::new(self.0), Box::new(other.0))),
        }
    }

    /// `<+>`: horizontal concatenation with a single space between.
    pub fn beside(self, other: Doc) -> Doc {
        if self.is_empty() { return other; }
        if other.is_empty() { return self; }
        self.cat_with(Doc::text(" ")).cat_with(other)
    }

    /// `$-$`: vertical concatenation, always inserting a newline.
    pub fn above(self, other: Doc) -> Doc {
        match (self.is_empty(), other.is_empty()) {
            (true, _) => other,
            (_, true) => self,
            _ => Doc(Node::Above(Box::new(self.0), Box::new(other.0))),
        }
    }

    /// `nest n d`: indent every line of `d` after the first by `n` spaces.
    pub fn nest(self, n: usize) -> Doc {
        if self.is_empty() || n == 0 { self } else { Doc(Node::Nest(n, Box::new(self.0))) }
    }

    /// Tag this document with a highlight style.
    pub fn highlight(self, style: HighlightStyle) -> Doc {
        Doc(Node::Highlight(style, Box::new(self.0)))
    }
}

/// `hcat`: horizontal concatenation without separator.
pub fn hcat(ds: impl IntoIterator<Item = Doc>) -> Doc {
    ds.into_iter().fold(Doc::empty(), Doc::cat_with)
}

/// `hsep`: horizontal concatenation separated by single spaces.
pub fn hsep(ds: impl IntoIterator<Item = Doc>) -> Doc {
    let mut iter = ds.into_iter().filter(|d| !d.is_empty());
    let first = match iter.next() { Some(d) => d, None => return Doc::empty() };
    iter.fold(first, |acc, d| acc.beside(d))
}

/// `vcat`: vertical concatenation, one document per line.
pub fn vcat(ds: impl IntoIterator<Item = Doc>) -> Doc {
    let mut iter = ds.into_iter().filter(|d| !d.is_empty());
    let first = match iter.next() { Some(d) => d, None => return Doc::empty() };
    iter.fold(first, |acc, d| acc.above(d))
}

/// `sep`: tries to put on one line; we always go vertical for simplicity.
pub fn sep(ds: impl IntoIterator<Item = Doc>) -> Doc { vcat(ds) }
pub fn cat(ds: impl IntoIterator<Item = Doc>) -> Doc { vcat(ds) }
pub fn fsep(ds: impl IntoIterator<Item = Doc>) -> Doc { hsep(ds) }
pub fn fcat(ds: impl IntoIterator<Item = Doc>) -> Doc { hcat(ds) }

// -- Atomic punctuation -------------------------------------------------------

pub fn semi() -> Doc { Doc::char(';') }
pub fn colon() -> Doc { Doc::char(':') }
pub fn comma() -> Doc { Doc::char(',') }
pub fn space() -> Doc { Doc::char(' ') }
pub fn equals() -> Doc { Doc::char('=') }
pub fn lparen() -> Doc { Doc::char('(') }
pub fn rparen() -> Doc { Doc::char(')') }
pub fn lbrack() -> Doc { Doc::char('[') }
pub fn rbrack() -> Doc { Doc::char(']') }
pub fn lbrace() -> Doc { Doc::char('{') }
pub fn rbrace() -> Doc { Doc::char('}') }

pub fn int(n: i64) -> Doc { Doc::text(n.to_string()) }
pub fn integer(n: i128) -> Doc { Doc::text(n.to_string()) }
pub fn double(n: f64) -> Doc { Doc::text(format!("{}", n)) }

pub fn quotes(d: Doc) -> Doc { Doc::char('\'').cat_with(d).cat_with(Doc::char('\'')) }
pub fn double_quotes(d: Doc) -> Doc { Doc::char('"').cat_with(d).cat_with(Doc::char('"')) }
pub fn parens(d: Doc) -> Doc { Doc::char('(').cat_with(d).cat_with(Doc::char(')')) }
pub fn brackets(d: Doc) -> Doc { Doc::char('[').cat_with(d).cat_with(Doc::char(']')) }
pub fn braces(d: Doc) -> Doc { Doc::char('{').cat_with(d).cat_with(Doc::char('}')) }

pub fn hang(d1: Doc, n: usize, d2: Doc) -> Doc { sep([d1, d2.nest(n)]) }

/// `punctuate sep ds`: insert `sep` between successive `ds`.
pub fn punctuate(sep: Doc, ds: Vec<Doc>) -> Vec<Doc> {
    let n = ds.len();
    if n == 0 { return Vec::new(); }
    let mut out = Vec::with_capacity(n);
    for (i, d) in ds.into_iter().enumerate() {
        if i == n - 1 {
            out.push(d);
        } else {
            out.push(d.cat_with(sep.clone()));
        }
    }
    out
}

/// Output text with a fixed advertised width.
pub fn fixed_width_text(n: usize, s: &str) -> Doc {
    if s.chars().count() <= n {
        Doc::text(s)
    } else {
        let head: String = s.chars().take(n).collect();
        let tail: String = s.chars().skip(n).collect();
        Doc::text(head).cat_with(Doc::zero_width_text(tail))
    }
}

/// Treat a string as a single-column "symbol" (zero-width past column 1).
pub fn symbol(s: &str) -> Doc { fixed_width_text(1, s) }

/// `numbered vsep ds`: prefix each `d` with a right-flushed index, joined by `vsep`.
pub fn numbered(vsep: Doc, ds: Vec<Doc>) -> Doc {
    if ds.is_empty() { return Doc::empty(); }
    let n = ds.len();
    let n_width = n.to_string().chars().count();
    let mut buf = String::new();
    let lined: Vec<Doc> = ds.into_iter().enumerate().map(|(i, d)| {
        buf.clear();
        write!(&mut buf, "{}", i + 1).unwrap();
        let prefix = flush_right(n_width, &buf);
        Doc::text(prefix).cat_with(d)
    }).collect();
    let with_seps = punctuate(vsep, lined);
    vcat(with_seps)
}

pub fn numbered_dot(ds: Vec<Doc>) -> Doc {
    let dotted: Vec<Doc> = ds.into_iter().map(|d| Doc::text(". ").cat_with(d)).collect();
    numbered(Doc::text(""), dotted)
}

// -- Highlight helpers --------------------------------------------------------

pub fn comment(d: Doc) -> Doc { d.highlight(HighlightStyle::Comment) }
pub fn keyword(d: Doc) -> Doc { d.highlight(HighlightStyle::Keyword) }
pub fn operator(d: Doc) -> Doc { d.highlight(HighlightStyle::Operator) }

pub fn comment_text(s: &str) -> Doc { comment(Doc::text(s)) }
pub fn keyword_text(s: &str) -> Doc { keyword(Doc::text(s)) }
pub fn operator_text(s: &str) -> Doc { operator(Doc::text(s)) }

pub fn op_parens(d: Doc) -> Doc {
    operator_text("(").cat_with(d).cat_with(operator_text(")"))
}

// =============================================================================
// Layout: convert a Node tree to a flat list of (indent, content) lines.
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
struct Line {
    indent: usize,
    content: String,
}

fn layout(n: &Node, base_indent: usize) -> Vec<Line> {
    layout_with(n, base_indent, &|_, s: &str| s.to_string())
}

fn layout_with<F: Fn(HighlightStyle, &str) -> String>(
    n: &Node,
    base_indent: usize,
    wrap: &F,
) -> Vec<Line> {
    match n {
        Node::Empty => vec![Line { indent: base_indent, content: String::new() }],
        Node::Text(s) | Node::ZeroWidth(s) => {
            vec![Line { indent: base_indent, content: s.clone() }]
        }
        Node::Cat(a, b) => {
            let mut la = layout_with(a, base_indent, wrap);
            let lb = layout_with(b, base_indent, wrap);
            // Glue first line of b onto last line of a.
            let last = la.pop().unwrap_or(Line { indent: base_indent, content: String::new() });
            let mut lb_iter = lb.into_iter();
            let first_b = lb_iter.next().unwrap_or(Line { indent: 0, content: String::new() });
            let merged = Line {
                indent: last.indent,
                content: last.content + &first_b.content,
            };
            la.push(merged);
            la.extend(lb_iter);
            la
        }
        Node::Above(a, b) => {
            let mut la = layout_with(a, base_indent, wrap);
            let lb = layout_with(b, base_indent, wrap);
            la.extend(lb);
            la
        }
        Node::Nest(k, inner) => layout_with(inner, base_indent + k, wrap),
        Node::Highlight(style, inner) => {
            // Wrap each rendered line's content with the wrapper. Multi-line
            // highlights are handled per-line; this matches the
            // `withTag`-style behaviour used by the HTML renderer.
            let mut ls = layout_with(inner, base_indent, wrap);
            for line in ls.iter_mut() {
                line.content = wrap(*style, &line.content);
            }
            ls
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn text_and_render() {
        assert_eq!(Doc::text("hello").render(), "hello");
        assert_eq!(Doc::empty().render(), "");
    }

    #[test]
    fn cat_horizontal() {
        let d = Doc::text("ab").cat_with(Doc::text("cd"));
        assert_eq!(d.render(), "abcd");
    }

    #[test]
    fn beside_inserts_space() {
        assert_eq!(Doc::text("a").beside(Doc::text("b")).render(), "a b");
    }

    #[test]
    fn above_inserts_newline() {
        let d = Doc::text("a").above(Doc::text("b"));
        assert_eq!(d.render(), "a\nb");
    }

    #[test]
    fn nest_indents_subsequent_lines() {
        let inner = Doc::text("a").above(Doc::text("b"));
        let d = Doc::text("hdr").cat_with(inner.nest(2));
        // Cat glues first line of nested onto "hdr" (no indent on first).
        // Subsequent line (b) gets nested by 2.
        assert_eq!(d.render(), "hdra\n  b");
    }

    #[test]
    fn vcat_lines_in_order() {
        let d = vcat(vec![Doc::text("a"), Doc::text("b"), Doc::text("c")]);
        assert_eq!(d.render(), "a\nb\nc");
    }

    #[test]
    fn hcat_concatenates() {
        assert_eq!(
            hcat(vec![Doc::text("a"), Doc::text("b"), Doc::text("c")]).render(),
            "abc"
        );
    }

    #[test]
    fn hsep_inserts_spaces() {
        assert_eq!(
            hsep(vec![Doc::text("a"), Doc::text("b"), Doc::text("c")]).render(),
            "a b c"
        );
    }

    #[test]
    fn brackets_wrap() {
        assert_eq!(parens(Doc::text("x")).render(), "(x)");
        assert_eq!(brackets(Doc::text("y")).render(), "[y]");
        assert_eq!(braces(Doc::text("z")).render(), "{z}");
    }

    #[test]
    fn punctuate_inserts_separators() {
        let ds = punctuate(
            Doc::char(','),
            vec![Doc::text("a"), Doc::text("b"), Doc::text("c")],
        );
        assert_eq!(hcat(ds).render(), "a,b,c");
    }

    #[test]
    fn numbered_dot_basic() {
        let d = numbered_dot(vec![Doc::text("alpha"), Doc::text("beta"), Doc::text("gamma")]);
        // 3 → 1 char index width; entries get ". " prefix; vsep is empty text.
        assert_eq!(d.render(), "1. alpha\n2. beta\n3. gamma");
    }

    #[test]
    fn fixed_width_text_pads_advertised_width() {
        // 3 chars rendered, width-3 advertised: text only.
        assert_eq!(fixed_width_text(3, "abc").render(), "abc");
        // 5 chars rendered but width-3 advertised: split into width-3 head plus zero-width tail.
        assert_eq!(fixed_width_text(3, "abcde").render(), "abcde");
    }

    #[test]
    fn highlight_passes_through_render() {
        let d = keyword(Doc::text("rule"));
        assert_eq!(d.render(), "rule");
        let html = d.render_with(&|s, body| match s {
            HighlightStyle::Keyword => format!("<kw>{}</kw>", body),
            _ => body.to_string(),
        });
        assert_eq!(html, "<kw>rule</kw>");
    }

    #[test]
    fn is_empty_recurses() {
        assert!(Doc::empty().is_empty());
        assert!(Doc::text("").is_empty());
        assert!(Doc::empty().nest(2).is_empty());
        assert!(!Doc::text("x").is_empty());
        assert!(!Doc::text("a").above(Doc::empty()).is_empty());
    }
}
