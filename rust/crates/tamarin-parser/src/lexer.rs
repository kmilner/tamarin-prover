//! Lexer for `.spthy` files.
//!
//! The lexer is a streaming character cursor that exposes higher-level
//! "skip whitespace, then peek/consume" operations rather than a separate
//! token stream. This matches Parsec's style and is convenient for
//! context-sensitive lexing (e.g. natural-number subscripts, formal
//! comments `name{* ... *}`, hex colour codes, multi-character symbol
//! choices like `++` vs `+`).

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pos {
    pub offset: usize,
    pub line: u32,
    pub col: u32,
}

impl Pos {
    pub const ZERO: Pos = Pos { offset: 0, line: 1, col: 1 };
}

#[derive(Debug, Clone)]
pub struct Lexer<'a> {
    src: &'a str,
    pos: Pos,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer { src, pos: Pos::ZERO }
    }

    pub fn pos(&self) -> Pos { self.pos }
    pub fn set_pos(&mut self, p: Pos) { self.pos = p; }
    pub fn src(&self) -> &'a str { self.src }
    pub fn rest(&self) -> &'a str { &self.src[self.pos.offset..] }
    pub fn is_eof(&self) -> bool { self.pos.offset >= self.src.len() }

    pub fn line_col(&self) -> (u32, u32) { (self.pos.line, self.pos.col) }

    /// Peek the next char without advancing.
    pub fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    /// Peek the char immediately after the next one (the second remaining char).
    pub fn peek2(&self) -> Option<char> {
        let mut it = self.rest().chars();
        it.next();
        it.next()
    }

    /// Advance one char, updating line/col.
    pub fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        let len = c.len_utf8();
        self.pos.offset += len;
        if c == '\n' {
            self.pos.line += 1;
            self.pos.col = 1;
        } else {
            self.pos.col += 1;
        }
        Some(c)
    }

    /// If the next char matches `c`, consume and return true.
    pub fn eat(&mut self, c: char) -> bool {
        if self.peek() == Some(c) { self.bump(); true } else { false }
    }

    /// Try to consume the literal string `s` at current position.
    pub fn eat_str(&mut self, s: &str) -> bool {
        if self.rest().starts_with(s) {
            for _ in s.chars() { self.bump(); }
            true
        } else { false }
    }

    // ---------- Whitespace and comments ----------

    /// Skip Whitespace, line comments `//...`, and nested block comments `/* ... */`.
    /// `#`-prefixed preprocessor directives are NOT skipped (they're tokens).
    pub fn skip_ws(&mut self) {
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() => { self.bump(); }
                Some('/') => {
                    if self.rest().starts_with("//") {
                        // line comment to EOL
                        while let Some(c) = self.peek() {
                            if c == '\n' { break; }
                            self.bump();
                        }
                    } else if self.rest().starts_with("/*") {
                        self.bump(); self.bump();
                        let mut depth = 1usize;
                        while depth > 0 {
                            match self.peek() {
                                None => return, // unterminated, stop
                                Some('/') if self.rest().starts_with("/*") => {
                                    self.bump(); self.bump(); depth += 1;
                                }
                                Some('*') if self.rest().starts_with("*/") => {
                                    self.bump(); self.bump(); depth -= 1;
                                }
                                _ => { self.bump(); }
                            }
                        }
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
    }

    // ---------- Symbol matchers ----------

    /// Try to consume a literal symbol after skipping whitespace.
    /// Symbol is matched verbatim, but if it ends with an alphanum we also
    /// require the next char to NOT be alphanum (word boundary).
    pub fn symbol(&mut self, s: &str) -> bool {
        self.skip_ws();
        if !self.rest().starts_with(s) { return false; }
        // Word-boundary check for keyword-like symbols.
        if s.chars().last().is_some_and(is_ident_char) {
            let after = &self.rest()[s.len()..];
            if after.chars().next().is_some_and(is_ident_char) {
                return false;
            }
        }
        for _ in s.chars() { self.bump(); }
        self.skip_ws();
        true
    }

    /// Like [`symbol`], but does not consume on failure.
    pub fn try_symbol(&mut self, s: &str) -> bool {
        let save = self.pos;
        if self.symbol(s) { true } else { self.pos = save; false }
    }

    /// Peek for a symbol (with word-boundary check) without consuming.
    pub fn peek_symbol(&mut self, s: &str) -> bool {
        let save = self.pos;
        let r = self.try_symbol(s);
        self.pos = save;
        r
    }

    // ---------- Identifiers ----------

    /// Parse an identifier: alphanum start, alphanum or `_` continuation.
    /// Returns None if the next char isn't alphanumeric.
    ///
    /// Note: unlike Haskell's `T.identifier spthy`, which rejects the reserved
    /// names `["in","let","rule","diff"]` (Token.hs:225), this deliberately does
    /// NOT exclude reserved names. Callers rely on this (e.g. the `diff` term op
    /// in parser.rs); facts named these words are still rejected upstream by the
    /// uppercase-first-letter rule, so the only divergence is the unusual case of
    /// a user naming a function/variable after a reserved keyword.
    pub fn identifier(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        let mut s = String::new();
        match self.peek() {
            Some(c) if c.is_alphanumeric() => { s.push(c); self.bump(); }
            _ => { self.pos = save; return None; }
        }
        while let Some(c) = self.peek() {
            if is_ident_char(c) { s.push(c); self.bump(); } else { break; }
        }
        self.skip_ws();
        Some(s)
    }

    /// Peek an identifier without consuming.
    pub fn peek_identifier(&mut self) -> Option<String> {
        let save = self.pos;
        let id = self.identifier();
        self.pos = save;
        id
    }

    /// Parse a natural number literal (decimal only).
    ///
    /// Haskell `T.natural spthy` (Token.hs:341) additionally accepts Parsec's
    /// `0x`/`0o` hex/octal prefixes. This restriction to decimal is intentional:
    /// every `natural` call site is a small decimal index (premise/conclusion
    /// numbers, function arity, reuse limit, `x.1` subscripts) that no real
    /// `.spthy` file writes in an alternate radix.
    pub fn natural(&mut self) -> Option<u64> {
        self.skip_ws();
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() { s.push(c); self.bump(); } else { break; }
        }
        if s.is_empty() { None } else { let n = s.parse().ok(); self.skip_ws(); n }
    }

    /// Subscript-digit natural (Unicode subscripts ₀–₉).
    pub fn natural_subscript(&mut self) -> Option<u64> {
        self.skip_ws();
        let mut n: u64 = 0;
        let mut got = false;
        while let Some(c) = self.peek() {
            let d = match c {
                '\u{2080}' => 0, '\u{2081}' => 1, '\u{2082}' => 2, '\u{2083}' => 3,
                '\u{2084}' => 4, '\u{2085}' => 5, '\u{2086}' => 6, '\u{2087}' => 7,
                '\u{2088}' => 8, '\u{2089}' => 9, _ => break,
            };
            n = n * 10 + d;
            got = true;
            self.bump();
        }
        if got { self.skip_ws(); Some(n) } else { None }
    }

    /// String literal in double quotes.
    ///
    /// Escapes are handled by dropping the backslash and keeping the next char
    /// verbatim (`\"` -> `"`, `\\` -> `\`, `\n` -> `n`). This is intentionally a
    /// restricted approximation and matches neither Haskell semantics exactly:
    /// config/fileArgs use `T.stringLiteral` (full Haskell escape decoding incl.
    /// `\n`->newline, numeric `\65`, gap escapes), while export bodies use a
    /// stricter `bodyChar` (Signature.hs:277-287) that only accepts `\\`/`\"` and
    /// fails on any other `\x`. The common `\\`/`\"` cases coincide across all
    /// call sites, and the diverging numeric/gap escapes do not occur in real
    /// config strings, include paths, or export bodies.
    pub fn string_literal(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        if !self.eat('"') { self.pos = save; return None; }
        let mut s = String::new();
        loop {
            match self.peek() {
                None => { self.pos = save; return None; }
                Some('"') => { self.bump(); self.skip_ws(); return Some(s); }
                Some('\\') => {
                    self.bump();
                    match self.peek() {
                        Some(c) => { s.push(c); self.bump(); }
                        None => { self.pos = save; return None; }
                    }
                }
                Some(c) => { s.push(c); self.bump(); }
            }
        }
    }

    /// Single-quoted string literal — not allowing single-quote or newline inside.
    pub fn single_quoted(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        if !self.eat('\'') { self.pos = save; return None; }
        let mut s = String::new();
        loop {
            match self.peek() {
                None | Some('\n') | Some('\'') => break,
                Some(c) => { s.push(c); self.bump(); }
            }
        }
        // Haskell `singleQuotedString = singleQuoted $ many1 (noneOf "'\n")`
        // (Token.hs:452-453): `many1` requires at least one body char, so `''`
        // must fail.
        if s.is_empty() { self.pos = save; return None; }
        if !self.eat('\'') { self.pos = save; return None; }
        self.skip_ws();
        Some(s)
    }

    /// Formal comment: `<header>{* body *}` (header is one or more letters).
    pub fn formal_comment(&mut self) -> Option<(String, String)> {
        self.skip_ws();
        let save = self.pos;
        let mut header = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_alphabetic() { header.push(c); self.bump(); } else { break; }
        }
        if header.is_empty() { self.pos = save; return None; }
        if !self.eat_str("{*") { self.pos = save; return None; }
        let mut body = String::new();
        loop {
            match self.peek() {
                None => { self.pos = save; return None; }
                Some('*') if self.rest().starts_with("*}") => {
                    self.bump(); self.bump(); self.skip_ws();
                    return Some((header, body));
                }
                Some('\\') => {
                    self.bump();
                    match self.peek() {
                        Some(c @ '\\') | Some(c @ '*') => { body.push(c); self.bump(); }
                        // Haskell `bodyChar` (Token.hs:382-387): on `\` the inner
                        // `char '\\' <|> char '*'` only accepts `\` or `*`; any
                        // other `\x` makes `bodyChar` (wrapped in `try`) backtrack
                        // un-consuming the `\`, so `many bodyChar` stops and the
                        // required `string "*}"` then fails at the `\` — i.e. the
                        // whole formalComment fails.
                        _ => { self.pos = save; return None; }
                    }
                }
                Some(c) => { body.push(c); self.bump(); }
            }
        }
    }

    /// Hex colour code (optionally prefixed with `#`, optionally single-quoted).
    ///
    /// Unlike the Haskell `symbol`-based parser (Token.hs:404-406), this does not
    /// skip whitespace after the opening quote or after `#`, so `' #FF'` / `'# FF'`
    /// are rejected here though Haskell accepts them. Real colour attributes are
    /// always tight (e.g. `'#111111'`), so this whitespace divergence has no
    /// practical effect.
    pub fn hex_color(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        let quoted = self.eat('\'');
        let _ = self.eat('#');
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_hexdigit() { s.push(c); self.bump(); } else { break; }
        }
        if quoted && !self.eat('\'') { self.pos = save; return None; }
        if s.is_empty() { self.pos = save; return None; }
        self.skip_ws();
        Some(s)
    }

    /// External identifier: `x-<ident>`.
    pub fn ext_identifier(&mut self) -> Option<String> {
        self.skip_ws();
        let save = self.pos;
        if !self.eat_str("x-") { self.pos = save; return None; }
        let id = self.identifier()?;
        Some(format!("x-{}", id))
    }
}

#[inline]
pub fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skip_whitespace_and_comments() {
        let mut l = Lexer::new("  // a line\n /* block */ x");
        l.skip_ws();
        assert_eq!(l.peek(), Some('x'));
    }

    #[test]
    fn nested_block_comment() {
        let mut l = Lexer::new("/* outer /* inner */ still */ x");
        l.skip_ws();
        assert_eq!(l.peek(), Some('x'));
    }

    #[test]
    fn identifier_then_symbol() {
        let mut l = Lexer::new("foo  bar123");
        assert_eq!(l.identifier().as_deref(), Some("foo"));
        assert_eq!(l.identifier().as_deref(), Some("bar123"));
    }

    #[test]
    fn symbol_word_boundary() {
        // `theory` should not match `theoryX`
        let mut l = Lexer::new("theoryX");
        assert!(!l.symbol("theory"));
        assert_eq!(l.identifier().as_deref(), Some("theoryX"));
    }

    #[test]
    fn natural_subscript_digits() {
        let mut l = Lexer::new("\u{2081}\u{2082}\u{2083}");
        assert_eq!(l.natural_subscript(), Some(123));
    }

    #[test]
    fn double_quoted_with_escape() {
        let mut l = Lexer::new(r#" "abc \"x\" def" "#);
        assert_eq!(l.string_literal().as_deref(), Some(r#"abc "x" def"#));
    }

    #[test]
    fn single_quoted_basic() {
        let mut l = Lexer::new(" 'foo'  ");
        assert_eq!(l.single_quoted().as_deref(), Some("foo"));
    }

    #[test]
    fn formal_comment_basic() {
        let mut l = Lexer::new(" text{* hello *} ");
        let (h, b) = l.formal_comment().unwrap();
        assert_eq!(h, "text");
        assert_eq!(b, " hello ");
    }
}
