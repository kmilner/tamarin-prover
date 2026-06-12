//! Recursive-descent parser for `.spthy` files.

use std::collections::HashSet;

use crate::ast::*;
use crate::lexer::{is_ident_char, Lexer, Pos};
use crate::proof_tree::parse_proof_tree;

// =============================================================================
// Errors
// =============================================================================

#[derive(Debug, Clone)]
pub struct ParseError {
    pub line: u32,
    pub col: u32,
    pub offset: usize,
    pub msg: String,
    pub snippet: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "parse error at line {} col {}: {} (near: {:?})",
            self.line, self.col, self.msg, self.snippet
        )
    }
}

impl std::error::Error for ParseError {}

// =============================================================================
// Parser entry points
// =============================================================================

/// Parse an `OpenTheory` (the default `theory ... begin ... end` form).
///
/// Anything after the closing `end` is ignored: Tamarin theories are commonly
/// followed by analysis banners and other free text that the official parser
/// also tolerates.
pub fn parse_theory(input: &str, flags: &[&str]) -> Result<Theory, ParseError> {
    let mut p = Parser::new(input, flags, false);
    let thy = p.theory()?;
    Ok(thy)
}

/// Parse either an `OpenTheory` or `OpenDiffTheory`. Decided by first
/// inspecting the file for a `diff` flag or by trying diff first.
/// In practice we just try a regular theory; the diff flag is set in the
/// preamble via `#define diff` or by the caller passing `flags`.
pub fn parse_theory_or_diff(input: &str, flags: &[&str]) -> Result<Theory, ParseError> {
    parse_theory(input, flags)
}

/// Parse a stream of intruder-rule declarations of the form
///     `rule (modulo AC) <name>[<limit>]: [..] --[..]-> [..]`
/// (with no surrounding `theory ... begin ... end` wrapper).
///
/// Direct port of HS `parseIntruderRules` (Theory/Text/Parser/Rule.hs:200-204):
/// ```haskell
/// parseIntruderRules
///     :: MaudeSig -> String -> B.ByteString -> Either ParseError [IntrRuleAC]
/// parseIntruderRules msig ctxtDesc =
///     parseString [] ctxtDesc (setState (mkStateSig msig) >> many intrRule)
///   . T.unpack . TE.decodeUtf8
/// ```
/// HS threads a `MaudeSig` through parser state so the term parser knows
/// which function symbols are builtin.  In this port the parser always
/// recognises every builtin operator at the syntax level — semantic
/// gating happens at elaboration — so the `MaudeSig` argument is
/// captured only for diagnostic context.
///
/// The bodies are parsed using the existing `parse_rule_ac` path.
/// The caller is responsible for translating the parser-AST rules into
/// `IntrRuleAC` (incl. the `c_`/`d_` name dispatch HS `intrInfo` does
/// at Rule.hs:161-169).
pub fn parse_intruder_rules(input: &str) -> Result<Vec<Rule>, ParseError> {
    let mut p = Parser::new(input, &[], false);
    let mut rules = Vec::new();
    loop {
        p.skip_ws();
        if p.lx.is_eof() { break; }
        // HS `intrRule` uses `try (symbol "rule" *> moduloAC *> intrInfo <* colon)`
        // (Rule.hs:157) — i.e. requires the `rule (modulo AC) name:` head.
        // `parse_rule_ac` enforces the same shape.
        let r = p.parse_rule_ac()?;
        rules.push(r);
    }
    Ok(rules)
}

// =============================================================================
// Parser state
// =============================================================================

pub struct Parser<'a> {
    lx: Lexer<'a>,
    /// Defined preprocessor flags. Mutated by `#define` directives.
    flags: HashSet<String>,
    /// Whether we're parsing a diff theory (set when `theory ...` is followed
    /// by `--diff` mode or when input includes `#define diff`).
    is_diff: bool,
    /// Currently-known function symbols (added by builtins / functions:).
    /// Used to disambiguate `f(...)` (function app) from a process call by
    /// identifier in the term parser. Only an upper bound; we accept unknown
    /// symbols too at parse level.
    known_funcs: HashSet<String>,
    /// Whether to enable parsing of operators that depend on builtins.
    /// We default-enable everything since this is a structural parser.
    enable_dh: bool,
    enable_xor: bool,
    enable_mset: bool,
    enable_nat: bool,
    enable_bp: bool,
    /// Builtin names that are reserved (e.g. the function `inv`, `pmult`, ...).
    reserved_funcs: HashSet<String>,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str, flags: &[&str], is_diff: bool) -> Self {
        let mut flags_set = HashSet::new();
        for f in flags { flags_set.insert((*f).to_string()); }
        let mut p = Parser {
            lx: Lexer::new(src),
            flags: flags_set,
            is_diff,
            known_funcs: HashSet::new(),
            enable_dh: false,
            enable_xor: false,
            enable_mset: false,
            enable_nat: false,
            enable_bp: false,
            reserved_funcs: HashSet::new(),
        };
        // Always enable parse-time recognition of the operators. The parser is
        // syntactic — semantic gating against builtin enablement happens at
        // elaboration. This follows the practice of accepting more than the
        // strict Haskell grammar at the syntax level.
        p.enable_dh = true;
        p.enable_xor = true;
        p.enable_mset = true;
        p.enable_nat = true;
        p.enable_bp = true;
        p
    }

    // -------- Error helpers --------

    fn err(&self, msg: impl Into<String>) -> ParseError {
        let pos = self.lx.pos();
        let snippet: String = self.lx.rest().chars().take(40).collect();
        ParseError {
            line: pos.line,
            col: pos.col,
            offset: pos.offset,
            msg: msg.into(),
            snippet,
        }
    }

    fn save(&self) -> Pos { self.lx.pos() }
    fn restore(&mut self, p: Pos) { self.lx.set_pos(p); }

    fn skip_ws(&mut self) { self.lx.skip_ws(); }

    #[allow(dead_code)]
    fn expect_eof(&mut self) -> Result<(), ParseError> {
        self.skip_ws();
        if self.lx.is_eof() { Ok(()) } else {
            Err(self.err(format!("expected EOF, got {:?}",
                self.lx.rest().chars().take(30).collect::<String>())))
        }
    }

    fn at_keyword(&mut self, kw: &str) -> bool {
        if !self.lx.peek_symbol(kw) { return false; }
        // Reject if followed by `-` (e.g. `rule-equivalence` is NOT `rule`).
        let save = self.save();
        let _ = self.lx.try_symbol(kw);
        let next = self.lx.peek();
        self.restore(save);
        next != Some('-')
    }
    fn try_kw(&mut self, kw: &str) -> bool {
        if !self.lx.peek_symbol(kw) { return false; }
        let save = self.save();
        let _ = self.lx.try_symbol(kw);
        if self.lx.peek() == Some('-') { self.restore(save); return false; }
        true
    }
    fn require_kw(&mut self, kw: &str) -> Result<(), ParseError> {
        if self.try_kw(kw) { Ok(()) } else { Err(self.err(format!("expected `{}`", kw))) }
    }

    fn require_punct(&mut self, p: &str) -> Result<(), ParseError> {
        self.skip_ws();
        if self.lx.eat_str(p) { self.skip_ws(); Ok(()) }
        else { Err(self.err(format!("expected `{}`", p))) }
    }

    fn try_punct(&mut self, p: &str) -> bool {
        self.skip_ws();
        let save = self.save();
        if self.lx.eat_str(p) { self.skip_ws(); true }
        else { self.restore(save); false }
    }

    /// Non-consuming lookahead for a punctuation token.
    fn peek_punct(&mut self, p: &str) -> bool {
        let save = self.save();
        let m = self.try_punct(p);
        self.restore(save);
        m
    }

    fn ident(&mut self) -> Result<String, ParseError> {
        self.lx.identifier().ok_or_else(|| self.err("expected identifier"))
    }

    fn natural(&mut self) -> Result<u64, ParseError> {
        self.lx.natural().ok_or_else(|| self.err("expected number"))
    }

    fn string_literal(&mut self) -> Result<String, ParseError> {
        self.lx.string_literal().ok_or_else(|| self.err("expected string literal"))
    }

    // =========================================================================
    // Top-level theory
    // =========================================================================

    pub fn theory(&mut self) -> Result<Theory, ParseError> {
        self.skip_ws();
        // Optional leading `#` directives. Handle them as items inside the body
        // — `theory` keyword must come first.
        self.require_kw("theory")?;
        let name = self.ident()?;
        let mut configuration = None;
        if self.try_kw("configuration") {
            self.require_punct(":")?;
            configuration = Some(self.string_literal()?);
            self.require_kw("begin")?;
        } else {
            self.require_kw("begin")?;
        }
        let items = self.theory_items_until_end()?;
        self.require_kw("end")?;
        // Allow trailing whitespace / comments / arbitrary text? Haskell stops here.
        Ok(Theory {
            is_diff: self.is_diff,
            name,
            configuration,
            items,
        })
    }

    /// Parse items until we encounter `end` (top-level) or `#endif` / `#else`.
    fn theory_items_until_end(&mut self) -> Result<Vec<TheoryItem>, ParseError> {
        let mut items = Vec::new();
        loop {
            self.skip_ws();
            if self.lx.is_eof() { break; }
            if self.at_keyword("end") { break; }
            // Pre-processor: #ifdef, #endif, #else terminate or extend.
            let save = self.save();
            if self.lx.eat_str("#") {
                // peek directive name
                let mut buf = String::new();
                let mut probe = self.lx.clone();
                while let Some(c) = probe.peek() {
                    if c.is_ascii_alphabetic() { buf.push(c); probe.bump(); } else { break; }
                }
                let directive = buf.as_str();
                if directive == "endif" || directive == "else" {
                    self.restore(save);
                    break;
                }
                self.restore(save);
            }
            let item = self.theory_item()?;
            items.push(item);
        }
        Ok(items)
    }

    fn theory_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.skip_ws();

        // Try preprocessor directives (start with `#`).
        if let Some(item) = self.try_preproc()? { return Ok(item); }

        // Try formal comment first (header `{* body *}`)
        let save = self.save();
        if let Some((h, b)) = self.lx.formal_comment() {
            return Ok(TheoryItem::FormalComment { header: h, body: b });
        }
        self.restore(save);

        // Try keyword-led items in priority order.
        if self.at_keyword("builtins") { return self.builtins(); }
        if self.at_keyword("options") { return self.options(); }
        if self.at_keyword("functions") || self.at_keyword("function") { return self.functions(); }
        if self.at_keyword("equations") { return self.equations(); }
        if self.at_keyword("macros") || self.at_keyword("macro") { return self.macros(); }
        if self.at_keyword("predicates") || self.at_keyword("predicate") { return self.predicates(); }
        if self.at_keyword("heuristic") { return self.heuristic(); }
        if self.at_keyword("tactic") { return self.tactic(); }
        if self.at_keyword("restriction") { return self.restriction_item(); }
        if self.at_keyword("axiom") { return self.legacy_axiom(); }
        if self.at_keyword("rule") { return self.rule_item(); }
        if self.at_keyword("lemma") { return self.lemma_item(); }
        if self.at_keyword("diffLemma") { return self.diff_lemma_item(); }
        if self.at_keyword("test") { return self.case_test_item(); }
        if self.at_keyword("equivLemma") { return self.equiv_lemma(false); }
        if self.at_keyword("diffEquivLemma") { return self.equiv_lemma(true); }
        if self.at_keyword("export") { return self.export_item(); }
        if self.at_keyword("process") { return self.toplevel_process(); }
        if self.at_keyword("let") { return self.process_def(); }

        // Accountability: `lemma X [accountability_attrs] ...` is matched by lemma_item.
        // Also: anonymous lemmaAcc `lemma name : accounts for [..]`.

        Err(self.err(format!(
            "unknown top-level construct, near {:?}",
            self.lx.rest().chars().take(30).collect::<String>()
        )))
    }

    // -------------------- Preprocessor --------------------

    fn try_preproc(&mut self) -> Result<Option<TheoryItem>, ParseError> {
        let save = self.save();
        self.skip_ws();
        if !self.lx.eat_str("#") { self.restore(save); return Ok(None); }
        // Read directive name.
        let mut name = String::new();
        while let Some(c) = self.lx.peek() {
            if c.is_ascii_alphabetic() { name.push(c); self.lx.bump(); } else { break; }
        }
        match name.as_str() {
            "ifdef" => {
                self.skip_ws();
                let cond = self.flag_disjuncts()?;
                let cond_holds = self.eval_flagformula(&cond);
                let then_items;
                let else_items;
                if cond_holds {
                    then_items = self.theory_items_until_end()?;
                    if self.try_punct("#else") {
                        // Else branch text is skipped.
                        self.skip_until("#endif");
                        else_items = None;
                    } else if self.try_punct("#endif") {
                        else_items = None;
                    } else {
                        return Err(self.err("expected #endif or #else"));
                    }
                } else {
                    // Skip then-branch.
                    let found = self.skip_until_branch_terminator();
                    match found {
                        BranchEnd::Else => {
                            then_items = vec![];
                            let items = self.theory_items_until_end()?;
                            self.require_punct("#endif")?;
                            else_items = Some(items);
                        }
                        BranchEnd::Endif => {
                            then_items = vec![];
                            else_items = None;
                        }
                        BranchEnd::Eof => {
                            return Err(self.err("unterminated #ifdef"));
                        }
                    }
                }
                Ok(Some(TheoryItem::IfDef { cond, then_items, else_items }))
            }
            "define" => {
                self.skip_ws();
                let id = self.ident()?;
                self.flags.insert(id.clone());
                Ok(Some(TheoryItem::Define(id)))
            }
            "include" => {
                self.skip_ws();
                let path = self.string_literal()?;
                Ok(Some(TheoryItem::Include(path)))
            }
            "endif" | "else" => {
                // Should have been handled by the matching #ifdef. We restore.
                self.restore(save);
                Ok(None)
            }
            other => Err(self.err(format!("unknown preprocessor directive `#{}`", other))),
        }
    }

    fn skip_until(&mut self, terminator: &str) {
        loop {
            self.skip_ws();
            if self.lx.is_eof() { return; }
            if self.try_punct(terminator) { return; }
            self.lx.bump();
        }
    }

    fn skip_until_branch_terminator(&mut self) -> BranchEnd {
        let mut depth = 0u32;
        loop {
            self.skip_ws();
            if self.lx.is_eof() { return BranchEnd::Eof; }
            if self.lx.peek() == Some('#') {
                let save = self.save();
                self.lx.bump();
                let mut name = String::new();
                while let Some(c) = self.lx.peek() {
                    if c.is_ascii_alphabetic() { name.push(c); self.lx.bump(); } else { break; }
                }
                match name.as_str() {
                    "ifdef" => { depth += 1; }
                    "endif" => {
                        if depth == 0 { return BranchEnd::Endif; }
                        depth -= 1;
                    }
                    "else" => {
                        if depth == 0 { return BranchEnd::Else; }
                    }
                    _ => {}
                }
                let _ = save;
            } else {
                self.lx.bump();
            }
        }
    }

    // -------------------- Builtins / options / heuristic / tactic --------------------

    fn builtins(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("builtins")?;
        self.require_punct(":")?;
        let mut names = Vec::new();
        loop {
            let n = self.hyphen_identifier()?;
            names.push(n.clone());
            self.note_builtin(&n);
            if !self.try_punct(",") { break; }
        }
        Ok(TheoryItem::Builtins(names))
    }

    /// Identifier that may contain hyphens (e.g. `asymmetric-encryption`,
    /// `diffie-hellman`, `dest-pairing`). Hyphens are concatenated into the
    /// returned name with no whitespace allowed across the boundary.
    fn hyphen_identifier(&mut self) -> Result<String, ParseError> {
        let mut s = self.ident()?;
        loop {
            // Look for `-<ident>` immediately after with no whitespace.
            if self.lx.peek() != Some('-') { break; }
            // We need to peek the char *after* the dash without consuming.
            let mut probe = self.lx.clone();
            probe.bump();
            match probe.peek() {
                Some(c) if c.is_alphabetic() => {
                    self.lx.bump(); // consume `-`
                    s.push('-');
                    let id = self.ident()?;
                    s.push_str(&id);
                }
                _ => break,
            }
        }
        Ok(s)
    }

    fn note_builtin(&mut self, name: &str) {
        let funcs: &[&str] = match name {
            "diffie-hellman" => &["inv", "1"],
            "bilinear-pairing" => &["inv", "1", "pmult", "em"],
            "multiset" => &[],
            "xor" => &["zero"],
            "symmetric-encryption" => &["senc", "sdec"],
            "asymmetric-encryption" => &["aenc", "adec", "pk"],
            "signing" => &["sign", "verify", "true", "pk"],
            "dest-pairing" => &["fst", "snd", "pair"],
            "dest-symmetric-encryption" => &["senc", "sdec"],
            "dest-asymmetric-encryption" => &["aenc", "adec", "pk"],
            "dest-signing" => &["sign", "verify", "revealVerify", "getMessage", "true", "pk"],
            "revealing-signing" => &["revealSign", "revealVerify", "getMessage", "verify", "true", "pk"],
            "hashing" => &["h"],
            "natural-numbers" => &[],
            "locations-report" => &["rep", "check_rep"],
            _ => &[],
        };
        for f in funcs {
            self.known_funcs.insert((*f).to_string());
            self.reserved_funcs.insert((*f).to_string());
        }
    }

    fn options(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("options")?;
        self.require_punct(":")?;
        let mut opts = Vec::new();
        loop {
            let n = self.hyphen_identifier()?;
            opts.push(n);
            if !self.try_punct(",") { break; }
        }
        Ok(TheoryItem::Options(opts))
    }

    fn heuristic(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("heuristic")?;
        self.require_punct(":")?;
        // Read until newline as raw text. Heuristic rankings are flexible; we
        // take everything up to next newline / `\n` boundary.
        let raw = self.read_to_eol();
        Ok(TheoryItem::Heuristic(raw.trim().to_string()))
    }

    fn read_to_eol(&mut self) -> String {
        let mut s = String::new();
        while let Some(c) = self.lx.peek() {
            if c == '\n' { break; }
            s.push(c);
            self.lx.bump();
        }
        // Trim any trailing inline comment? Skip; consumer can deal.
        s
    }

    fn tactic(&mut self) -> Result<TheoryItem, ParseError> {
        // tactic: <name>\n  presort: ...\n  prio: ...\n  ...
        // We recognise the structure by reading until we hit an end-of-tactic
        // marker — tactics terminate when a keyword that starts a new theory
        // item appears at the top of a line. Pragmatic: read until next
        // top-level keyword.
        self.require_kw("tactic")?;
        self.require_punct(":")?;
        let name = self.ident()?;
        let raw = self.read_until_next_top_level();
        Ok(TheoryItem::Tactic(Tactic { name, raw }))
    }

    /// Read raw text until we see an identifier at a word boundary that is
    /// one of the recognised top-level keywords, or a `#`-prefixed
    /// preprocessor directive. Used for tactics, proof skeletons, etc.
    fn read_until_next_top_level(&mut self) -> String {
        const KW: &[&str] = &[
            "end", "rule", "lemma", "diffLemma", "restriction", "axiom",
            "tactic", "heuristic", "predicates", "predicate", "macros", "macro",
            "functions", "function", "equations", "builtins", "options",
            "process", "test", "equivLemma", "diffEquivLemma", "export",
        ];
        let mut s = String::new();
        // Track whether the previous character was an identifier char. If so,
        // we are in the middle of a word and should not match keywords here.
        let mut prev_was_ident = false;
        loop {
            if self.lx.is_eof() { break; }
            // Skip whitespace and comments without resetting prev_was_ident,
            // since whitespace is itself a word boundary — actually whitespace
            // resets the prev-ident state. Block/line comments are entirely
            // skipped by skip_ws.
            let pre_ws = self.lx.pos();
            self.lx.skip_ws();
            if self.lx.pos() != pre_ws {
                // Capture skipped whitespace verbatim.
                let skipped = &self.lx.src()[pre_ws.offset..self.lx.pos().offset];
                s.push_str(skipped);
                prev_was_ident = false;
            }
            if self.lx.is_eof() { break; }
            // At a word boundary, check for top-level keywords.
            if !prev_was_ident {
                if let Some(id) = self.peek_hyphen_identifier() {
                    if KW.contains(&id.as_str()) { break; }
                }
                if self.lx.peek() == Some('#') {
                    let mut probe = self.lx.clone();
                    probe.bump();
                    let mut name = String::new();
                    while let Some(c) = probe.peek() {
                        if c.is_ascii_alphabetic() { name.push(c); probe.bump(); }
                        else { break; }
                    }
                    if matches!(name.as_str(),
                        "ifdef" | "endif" | "else" | "define" | "include")
                    { break; }
                }
            }
            // Append next char.
            match self.lx.peek() {
                Some(c) => {
                    prev_was_ident = is_ident_char(c) || c == '-';
                    s.push(c);
                    self.lx.bump();
                }
                None => break,
            }
        }
        s
    }

    // -------------------- functions / equations / macros / predicates --------------------

    fn functions(&mut self) -> Result<TheoryItem, ParseError> {
        // `functions:` or `function:`
        if !self.try_kw("functions") { self.require_kw("function")?; }
        self.require_punct(":")?;
        let mut decls = Vec::new();
        loop {
            let f = self.function_decl()?;
            self.known_funcs.insert(f.name.clone());
            decls.push(f);
            if !self.try_punct(",") { break; }
        }
        Ok(TheoryItem::Functions(decls))
    }

    fn function_decl(&mut self) -> Result<FunctionDecl, ParseError> {
        let name = self.ident()?;
        let (arg_types, out_type);
        if self.try_punct("/") {
            let k = self.natural()?;
            arg_types = vec![None; k as usize];
            out_type = None;
        } else {
            self.require_punct("(")?;
            let mut args = Vec::new();
            if !self.try_punct(")") {
                loop {
                    let t = self.type_p()?;
                    args.push(t);
                    if !self.try_punct(",") { break; }
                }
                self.require_punct(")")?;
            }
            self.require_punct(":")?;
            out_type = self.type_p()?;
            arg_types = args.into_iter().collect();
        }
        // Optional attributes [private, constructor, destructor, ...]
        let mut private = false;
        let mut destructor = false;
        if self.try_punct("[") {
            loop {
                self.skip_ws();
                if self.try_kw("private") { private = true; }
                else if self.try_kw("constructor") {}
                else if self.try_kw("destructor") { destructor = true; }
                else { break; }
                if !self.try_punct(",") { break; }
            }
            self.require_punct("]")?;
        }
        Ok(FunctionDecl { name, arg_types, out_type, private, destructor })
    }

    /// SAPIC type: `<defaultSapicTypeS>` = `Any` placeholder, or an identifier.
    /// We accept any identifier as a type.
    fn type_p(&mut self) -> Result<Option<String>, ParseError> {
        // Haskell uses `defaultSapicTypeS` — a literal token. We'll accept
        // any identifier and additionally `Any` as the default placeholder.
        self.skip_ws();
        // Peek for sentinel — Haskell uses `*` for default.
        if self.try_punct("*") { return Ok(None); }
        let id = self.ident()?;
        if id == "Any" || id == "any" { Ok(None) } else { Ok(Some(id)) }
    }

    fn equations(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("equations")?;
        let convergent = if self.try_punct("[") {
            let _ = self.try_kw("convergent");
            self.require_punct("]")?;
            true
        } else { false };
        self.require_punct(":")?;
        let mut eqs = Vec::new();
        loop {
            let lhs = self.term(true)?;
            self.require_punct("=")?;
            let rhs = self.term(true)?;
            eqs.push(Equation { lhs, rhs });
            if !self.try_punct(",") { break; }
        }
        Ok(TheoryItem::Equations { convergent, eqs })
    }

    fn macros(&mut self) -> Result<TheoryItem, ParseError> {
        if !self.try_kw("macros") { self.require_kw("macro")?; }
        self.require_punct(":")?;
        let mut ms = Vec::new();
        loop {
            let name = self.ident()?;
            self.require_punct("(")?;
            let mut args = Vec::new();
            if !self.try_punct(")") {
                loop {
                    let v = self.var_spec()?;
                    args.push(v);
                    if !self.try_punct(",") { break; }
                }
                self.require_punct(")")?;
            }
            self.require_punct("=")?;
            let body = self.term(false)?;
            // Macros are recognised as functions in subsequent terms.
            self.known_funcs.insert(name.clone());
            ms.push(Macro { name, args, body });
            if !self.try_punct(",") { break; }
        }
        Ok(TheoryItem::Macros(ms))
    }

    fn predicates(&mut self) -> Result<TheoryItem, ParseError> {
        if !self.try_kw("predicates") { self.require_kw("predicate")?; }
        self.require_punct(":")?;
        let mut ps = Vec::new();
        loop {
            let f = self.fact()?;
            self.require_punct("<=>")?;
            let phi = self.formula()?;
            ps.push(Predicate { fact: f, formula: phi });
            if !self.try_punct(",") { break; }
        }
        Ok(TheoryItem::Predicates(ps))
    }

    // -------------------- Restriction / axiom --------------------

    fn restriction_item(&mut self) -> Result<TheoryItem, ParseError> {
        let r = self.restriction("restriction")?;
        Ok(TheoryItem::Restriction(r))
    }

    fn legacy_axiom(&mut self) -> Result<TheoryItem, ParseError> {
        let r = self.restriction("axiom")?;
        Ok(TheoryItem::LegacyAxiom(r))
    }

    fn restriction(&mut self, kw: &str) -> Result<Restriction, ParseError> {
        self.require_kw(kw)?;
        let name = self.ident()?;
        let mut attributes = Vec::new();
        if self.try_punct("[") {
            loop {
                self.skip_ws();
                if self.try_kw("left") { attributes.push(RestrictionAttr::LeftRestriction); }
                else if self.try_kw("right") { attributes.push(RestrictionAttr::RightRestriction); }
                else { break; }
                if !self.try_punct(",") { break; }
            }
            self.require_punct("]")?;
        }
        self.require_punct(":")?;
        let phi = self.double_quoted_formula()?;
        Ok(Restriction { name, formula: phi, attributes })
    }

    /// Parse a formula between literal `"` and `"`. Whitespace and comments
    /// inside (including `/* ... */` blocks containing `"`) are handled by
    /// the normal lexer's `skip_ws`. This matches Haskell's
    /// `doubleQuoted parseFormula` rather than reading a string literal and
    /// re-parsing it.
    fn double_quoted_formula(&mut self) -> Result<Formula, ParseError> {
        self.require_punct("\"")?;
        let f = self.formula()?;
        self.require_punct("\"")?;
        Ok(f)
    }

    // -------------------- Rule --------------------

    fn rule_item(&mut self) -> Result<TheoryItem, ParseError> {
        // We must distinguish protocol rules from intruder rules. Intruder
        // rules use `rule (modulo AC) name: ...` — they live in the top-level
        // theory only when explicitly parsed (e.g. for a precomputed intruder
        // file). We treat both uniformly; the `modulo` field captures it.
        let r = self.parse_rule()?;
        // Tag intruder rules: their names start with `c<...>` or `d<...>`,
        // typically only when modulo == Some("AC"). We don't enforce this.
        if r.modulo.as_deref() == Some("AC") {
            Ok(TheoryItem::IntrRule(r))
        } else {
            Ok(TheoryItem::Rule(r))
        }
    }

    fn parse_rule(&mut self) -> Result<Rule, ParseError> {
        self.require_kw("rule")?;
        let modulo = self.try_modulo();
        let name = self.ident()?;
        let attributes = self.rule_attributes()?;
        self.require_punct(":")?;
        // Optional let block.
        let let_block = if self.at_keyword("let") {
            self.parse_let_block()?
        } else { vec![] };
        // Premises [..]
        let premises = self.fact_list()?;
        // Actions / restrictions either `--[..]->` or `-->`
        let (actions, embedded_restrictions);
        if self.try_punct("-->") {
            actions = vec![];
            embedded_restrictions = vec![];
        } else {
            self.require_punct("--[")?;
            let mut acts = Vec::new();
            let mut rstrs = Vec::new();
            self.skip_ws();
            if !self.try_punct("]->") {
                loop {
                    let item = self.fact_or_restr()?;
                    match item {
                        FactOrRestr::Fact(f) => acts.push(f),
                        FactOrRestr::Restr(phi) => rstrs.push(phi),
                    }
                    // HS `commaSep` (Rule.hs:186) = `sepEndBy comma`: a trailing
                    // comma before `]->` is permitted.
                    if !self.try_punct(",") { break; }
                    if self.peek_punct("]->") { break; }
                }
                self.require_punct("]->")?;
            }
            actions = acts;
            embedded_restrictions = rstrs;
        }
        let conclusions = self.fact_list()?;
        // Optional variants
        let variants = if self.try_kw("variants") {
            let mut vs = Vec::new();
            loop {
                let v = self.parse_rule_ac()?;
                vs.push(v);
                if !self.try_punct(",") { break; }
            }
            vs
        } else { vec![] };
        // Optional `left ... right ...` for diff rules
        let left_right = if self.try_kw("left") {
            let l = self.parse_rule()?;
            self.require_kw("right")?;
            let r = self.parse_rule()?;
            Some((Box::new(l), Box::new(r)))
        } else { None };
        Ok(Rule {
            name, modulo, attributes, let_block,
            premises, actions, conclusions, embedded_restrictions,
            variants, left_right,
        })
    }

    fn parse_rule_ac(&mut self) -> Result<Rule, ParseError> {
        self.require_kw("rule")?;
        // moduloAC required
        let modulo = self.try_modulo();
        let name = self.ident()?;
        let attributes = self.rule_attributes()?;
        self.require_punct(":")?;
        let let_block = if self.at_keyword("let") { self.parse_let_block()? } else { vec![] };
        let premises = self.fact_list()?;
        let (actions, embedded_restrictions);
        if self.try_punct("-->") {
            actions = vec![];
            embedded_restrictions = vec![];
        } else {
            self.require_punct("--[")?;
            let mut acts = Vec::new();
            let mut rstrs = Vec::new();
            if !self.try_punct("]->") {
                loop {
                    let item = self.fact_or_restr()?;
                    match item {
                        FactOrRestr::Fact(f) => acts.push(f),
                        FactOrRestr::Restr(phi) => rstrs.push(phi),
                    }
                    // HS `commaSep` (Rule.hs:186) = `sepEndBy comma`: a trailing
                    // comma before `]->` is permitted.
                    if !self.try_punct(",") { break; }
                    if self.peek_punct("]->") { break; }
                }
                self.require_punct("]->")?;
            }
            actions = acts;
            embedded_restrictions = rstrs;
        }
        let conclusions = self.fact_list()?;
        Ok(Rule {
            name, modulo, attributes, let_block,
            premises, actions, conclusions, embedded_restrictions,
            variants: vec![], left_right: None,
        })
    }

    fn try_modulo(&mut self) -> Option<String> {
        let save = self.save();
        if !self.try_punct("(") { return None; }
        if !self.try_kw("modulo") { self.restore(save); return None; }
        let id = match self.ident() { Ok(s) => s, Err(_) => { self.restore(save); return None; } };
        if !self.try_punct(")") { self.restore(save); return None; }
        Some(id)
    }

    fn rule_attributes(&mut self) -> Result<Vec<RuleAttr>, ParseError> {
        let mut attrs = Vec::new();
        if !self.try_punct("[") { return Ok(attrs); }
        loop {
            self.skip_ws();
            // colour=, color=
            if self.try_kw("colour") {
                self.require_punct("=")?;
                let c = self.lx.hex_color().ok_or_else(|| self.err("expected hex color"))?;
                attrs.push(RuleAttr::Color(c));
            } else if self.try_kw("color") {
                self.require_punct("=")?;
                let c = self.lx.hex_color().ok_or_else(|| self.err("expected hex color"))?;
                attrs.push(RuleAttr::Color(c));
            } else if self.try_kw("process") {
                self.require_punct("=")?;
                let s = self.read_balanced_token()?;
                attrs.push(RuleAttr::Process(s));
            } else if self.try_kw("no_derivcheck") {
                attrs.push(RuleAttr::NoDerivCheck);
            } else if self.try_kw("role") {
                self.require_punct("=")?;
                let s = self.string_literal_or_squoted()?;
                attrs.push(RuleAttr::Role(s));
            } else if self.try_kw("issapicrule") {
                attrs.push(RuleAttr::IsSapicRule);
            } else {
                // External attribute: x-<id> [= raw]
                let save = self.save();
                if let Some(ext) = self.lx.ext_identifier() {
                    let val = if self.try_punct("=") {
                        Some(self.read_balanced_token()?)
                    } else { None };
                    attrs.push(RuleAttr::External(ext, val));
                } else {
                    self.restore(save);
                    break;
                }
            }
            if !self.try_punct(",") { break; }
        }
        self.require_punct("]")?;
        Ok(attrs)
    }

    fn string_literal_or_squoted(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        if let Some(s) = self.lx.string_literal() { return Ok(s); }
        if let Some(s) = self.lx.single_quoted() { return Ok(s); }
        Err(self.err("expected quoted string"))
    }

    /// Read an identifier or a balanced parenthesised token (for `process=...`).
    fn read_balanced_token(&mut self) -> Result<String, ParseError> {
        self.skip_ws();
        let start = self.save();
        let pairs = [('(', ')'), ('[', ']'), ('{', '}'), ('"', '"'), ('\'', '\''), ('<', '>')];
        if let Some(c) = self.lx.peek() {
            for (l, r) in pairs.iter() {
                if c == *l {
                    self.lx.bump();
                    let mut s = String::new();
                    let mut depth = 1u32;
                    while depth > 0 {
                        match self.lx.peek() {
                            None => return Err(self.err("unterminated bracketed value")),
                            Some(ch) if ch == *l && *l != *r => { depth += 1; s.push(ch); self.lx.bump(); }
                            Some(ch) if ch == *r => {
                                depth -= 1;
                                if depth > 0 { s.push(ch); }
                                self.lx.bump();
                            }
                            Some(ch) => { s.push(ch); self.lx.bump(); }
                        }
                    }
                    self.skip_ws();
                    return Ok(s);
                }
            }
        }
        // Otherwise, read a single identifier-or-number token.
        let id = self.ident()?;
        let _ = start;
        Ok(id)
    }

    fn parse_let_block(&mut self) -> Result<Vec<LetBinding>, ParseError> {
        self.require_kw("let")?;
        let mut bs = Vec::new();
        loop {
            self.skip_ws();
            if self.at_keyword("in") { break; }
            // End-of-block sentinels (defensive — the canonical terminator is
            // `in`, but malformed inputs shouldn't loop forever).
            if self.lx.peek() == Some('[')
                || self.lx.rest().starts_with("-->")
                || self.lx.rest().starts_with("--[")
            { break; }
            let lhs_save = self.save();
            let lhs = match self.term(false) {
                Ok(t) => t,
                Err(_) => { self.restore(lhs_save); break; }
            };
            if !self.try_punct("=") {
                self.restore(lhs_save);
                break;
            }
            let rhs = self.term(false)?;
            bs.push(LetBinding { var: lhs, value: rhs });
        }
        // Consume the `in` terminator if present.
        let _ = self.try_kw("in");
        Ok(bs)
    }

    fn fact_list(&mut self) -> Result<Vec<Fact>, ParseError> {
        self.require_punct("[")?;
        let mut fs = Vec::new();
        if self.try_punct("]") { return Ok(fs); }
        loop {
            let f = self.fact()?;
            fs.push(f);
            // HS `commaSep1 fact` (Rule.hs:196) = `sepEndBy1 comma`: a trailing
            // comma before `]` is permitted.
            if !self.try_punct(",") { break; }
            if self.peek_punct("]") { break; }
        }
        self.require_punct("]")?;
        Ok(fs)
    }

    fn fact_or_restr(&mut self) -> Result<FactOrRestr, ParseError> {
        // `_restrict(formula)` or fact.
        if self.try_kw("_restrict") {
            self.require_punct("(")?;
            let phi = self.formula()?;
            self.require_punct(")")?;
            Ok(FactOrRestr::Restr(phi))
        } else {
            Ok(FactOrRestr::Fact(self.fact()?))
        }
    }

    // -------------------- Lemma --------------------

    fn lemma_item(&mut self) -> Result<TheoryItem, ParseError> {
        // Look ahead to decide between a normal lemma and an accountability lemma.
        // Accountability lemmas have the body `accounts for [..]` after the name.
        let save = self.save();
        self.require_kw("lemma")?;
        let _ = self.try_modulo();
        let name = self.ident()?;
        let attrs = self.lemma_attributes()?;
        self.require_punct(":")?;

        // Detect accountability: `<test_idents> accounts for "phi"`
        let snap = self.save();
        if let Some(acc) = self.try_acc_lemma_body(&name, &attrs)? {
            return Ok(TheoryItem::AccLemma(acc));
        }
        self.restore(snap);

        // Trace quantifier
        let trace_quantifier = if self.try_kw("all-traces") {
            TraceQuantifier::AllTraces
        } else if self.try_kw("exists-trace") {
            TraceQuantifier::ExistsTrace
        } else {
            TraceQuantifier::AllTraces
        };
        let formula = self.double_quoted_formula()?;
        let proof = self.try_proof_skeleton()?;
        let _ = save;
        Ok(TheoryItem::Lemma(Lemma {
            name, modulo: None, attributes: attrs, trace_quantifier, formula, proof,
        }))
    }

    fn try_acc_lemma_body(&mut self, name: &str, _attrs: &[LemmaAttr])
        -> Result<Option<AccLemma>, ParseError>
    {
        // Pattern: `<id1, id2, ...> (accounts|account) for "phi"`
        let save = self.save();
        let mut idents = Vec::new();
        loop {
            self.skip_ws();
            let probe = self.save();
            if let Some(id) = self.lx.peek_identifier() {
                if id == "accounts" || id == "account" { break; }
                let _ = self.ident();
                idents.push(id);
                if !self.try_punct(",") { break; }
            } else {
                self.restore(probe);
                break;
            }
        }
        if !(self.try_kw("accounts") || self.try_kw("account")) {
            self.restore(save); return Ok(None);
        }
        self.require_kw("for")?;
        let formula = self.double_quoted_formula()?;
        Ok(Some(AccLemma {
            name: name.to_string(),
            attributes: Vec::new(),
            formula,
            case_test_idents: idents,
        }))
    }

    fn diff_lemma_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("diffLemma")?;
        let name = self.ident()?;
        let attributes = self.lemma_attributes()?;
        self.require_punct(":")?;
        let proof = self.try_proof_skeleton()?;
        Ok(TheoryItem::DiffLemma(DiffLemma { name, attributes, proof }))
    }

    fn case_test_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("test")?;
        let name = self.ident()?;
        self.require_punct(":")?;
        let formula = self.double_quoted_formula()?;
        Ok(TheoryItem::CaseTest(CaseTest { name, formula }))
    }

    fn lemma_attributes(&mut self) -> Result<Vec<LemmaAttr>, ParseError> {
        let mut attrs = Vec::new();
        if !self.try_punct("[") { return Ok(attrs); }
        loop {
            self.skip_ws();
            if self.try_kw("typing") || self.try_kw("sources") { attrs.push(LemmaAttr::Sources); }
            else if self.try_kw("reuse") { attrs.push(LemmaAttr::Reuse); }
            else if self.try_kw("diff_reuse") { attrs.push(LemmaAttr::DiffReuse); }
            else if self.try_kw("use_induction") { attrs.push(LemmaAttr::UseInduction); }
            else if self.try_kw("hide_lemma") {
                self.require_punct("=")?;
                let id = self.ident()?;
                attrs.push(LemmaAttr::HideLemma(id));
            }
            else if self.try_kw("heuristic") {
                self.require_punct("=")?;
                let raw = self.read_until_attribute_end();
                attrs.push(LemmaAttr::Heuristic(raw));
            }
            else if self.try_kw("output") {
                self.require_punct("=")?;
                self.require_punct("[")?;
                let mut outs = Vec::new();
                if !self.try_punct("]") {
                    loop {
                        let id = self.ident()?;
                        outs.push(id);
                        if !self.try_punct(",") { break; }
                    }
                    self.require_punct("]")?;
                }
                attrs.push(LemmaAttr::Output(outs));
            }
            else if self.try_kw("left") { attrs.push(LemmaAttr::Left); }
            else if self.try_kw("right") { attrs.push(LemmaAttr::Right); }
            else {
                // Generic hint attribute: read until `,` or `]`.
                let raw = self.read_until_attribute_end();
                if raw.is_empty() { break; }
                attrs.push(LemmaAttr::Hint(raw));
            }
            if !self.try_punct(",") { break; }
        }
        self.require_punct("]")?;
        Ok(attrs)
    }

    fn read_until_attribute_end(&mut self) -> String {
        let mut s = String::new();
        let mut depth = 0i32;
        loop {
            match self.lx.peek() {
                None => break,
                Some(']') if depth == 0 => break,
                Some(',') if depth == 0 => break,
                Some('[') | Some('(') | Some('{') => {
                    depth += 1;
                    s.push(self.lx.peek().unwrap());
                    self.lx.bump();
                }
                Some(']') | Some(')') | Some('}') => {
                    depth -= 1;
                    s.push(self.lx.peek().unwrap());
                    self.lx.bump();
                }
                Some(c) => { s.push(c); self.lx.bump(); }
            }
        }
        s.trim().to_string()
    }

    fn try_proof_skeleton(&mut self) -> Result<Option<ProofSkeleton>, ParseError> {
        // Proofs in `.spthy` files start with one of a known set of proof
        // method tokens. We treat the proof as raw text up to the next
        // top-level keyword. If no proof tokens appear, return None.
        self.skip_ws();
        let save = self.save();
        let proof_starters = [
            "simplify", "solve", "case", "qed", "by", "next", "induction",
            "rule-equivalence", "backward-search", "sorry", "rule",
            "step", "rev",
        ];
        // Check for hyphenated proof identifiers.
        let probe = self.peek_hyphen_identifier();
        let starts = match probe {
            Some(id) => proof_starters.contains(&id.as_str()),
            None => false,
        };
        // For ambiguity: `rule` on its own followed by `:` is a rule, not a
        // proof. We only treat `rule` as proof start if followed by hyphen.
        let starts = starts && {
            if let Some(id) = self.peek_hyphen_identifier() {
                if id == "rule" {
                    // not valid as proof start
                    false
                } else { true }
            } else { false }
        };
        if !starts { self.restore(save); return Ok(None); }
        let raw = self.read_until_next_top_level();
        // Structured parse of `raw`.  Mirrors HS's `startProofSkeleton`
        // (Theory/Text/Parser/Proof.hs:90-95) which calls `proofSkeleton`
        // (Proof.hs:98-115) — a recursive descent over
        // `simplify | solve(...) | induction | by <method> | SOLVED`
        // with `case <name> ... next ... qed` blocks.  We parse over
        // the captured raw text rather than the original lexer so the
        // top-level boundary detection (`read_until_next_top_level`)
        // controls termination.
        //
        // If the structured parse fails we still keep the raw text,
        // and `replace_sorry_prove` will fall back to the auto-prover.
        let tree = parse_proof_tree(&raw).ok();
        Ok(Some(ProofSkeleton { raw, tree }))
    }

    /// Peek a possibly-hyphenated identifier without consuming.
    fn peek_hyphen_identifier(&mut self) -> Option<String> {
        let save = self.save();
        self.lx.skip_ws();
        let mut s = String::new();
        match self.lx.peek() {
            Some(c) if c.is_alphabetic() => { s.push(c); self.lx.bump(); }
            _ => { self.restore(save); return None; }
        }
        loop {
            match self.lx.peek() {
                Some(c) if is_ident_char(c) => { s.push(c); self.lx.bump(); }
                Some('-') => {
                    let mut probe = self.lx.clone();
                    probe.bump();
                    match probe.peek() {
                        Some(c) if c.is_alphabetic() => {
                            self.lx.bump(); s.push('-');
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        self.restore(save);
        Some(s)
    }

    // -------------------- Top-level process / processDef --------------------

    fn toplevel_process(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("process")?;
        self.require_punct(":")?;
        let p = self.process()?;
        Ok(TheoryItem::TopLevelProcess(p))
    }

    fn process_def(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("let")?;
        let name = self.ident()?;
        let vars = if self.try_punct("(") {
            let mut vs = Vec::new();
            if !self.try_punct(")") {
                loop {
                    let v = self.var_spec()?;
                    vs.push(v);
                    if !self.try_punct(",") { break; }
                }
                self.require_punct(")")?;
            }
            Some(vs)
        } else { None };
        self.require_punct("=")?;
        let body = self.process()?;
        Ok(TheoryItem::ProcessDef(ProcessDef { name, vars, body }))
    }

    fn equiv_lemma(&mut self, diff: bool) -> Result<TheoryItem, ParseError> {
        if diff { self.require_kw("diffEquivLemma")?; }
        else { self.require_kw("equivLemma")?; }
        self.require_punct(":")?;
        let p1 = self.process()?;
        if diff {
            Ok(TheoryItem::DiffEquivLemma(p1))
        } else {
            let p2 = self.process()?;
            Ok(TheoryItem::EquivLemma(p1, p2))
        }
    }

    fn export_item(&mut self) -> Result<TheoryItem, ParseError> {
        self.require_kw("export")?;
        let tag = self.ident()?;
        self.require_punct(":")?;
        let body = self.string_literal()?;
        Ok(TheoryItem::Export { tag, body })
    }

    // =========================================================================
    // Process parser (SAPIC)
    // =========================================================================

    fn process(&mut self) -> Result<Process, ParseError> {
        // Left-associative parallel / NDC composition.
        let mut left = self.action_process()?;
        loop {
            self.skip_ws();
            if self.try_punct("||") {
                let right = self.action_process()?;
                left = Process::Comb { comb: ProcessComb::Parallel, left: Box::new(left), right: Box::new(right) };
            } else if self.lx.peek() == Some('|') && self.lx.peek2() != Some('|') {
                // Single `|` parallel
                self.lx.bump();
                self.skip_ws();
                let right = self.action_process()?;
                left = Process::Comb { comb: ProcessComb::Parallel, left: Box::new(left), right: Box::new(right) };
            } else if self.try_punct("+") {
                let right = self.action_process()?;
                left = Process::Comb { comb: ProcessComb::Ndc, left: Box::new(left), right: Box::new(right) };
            } else { break; }
        }
        Ok(left)
    }

    fn action_process(&mut self) -> Result<Process, ParseError> {
        self.skip_ws();
        // Replication
        if self.try_punct("!") {
            let p = self.process()?;
            return Ok(Process::Replication(Box::new(p)));
        }
        if self.try_kw("lookup") {
            let t = self.term(false)?;
            self.require_kw("as")?;
            let v = self.var_spec()?;
            self.require_kw("in")?;
            let p = self.process()?;
            let q = self.else_process()?;
            return Ok(Process::Comb {
                comb: ProcessComb::Lookup(t, v),
                left: Box::new(p),
                right: Box::new(q),
            });
        }
        if self.try_kw("if") {
            // Try equality: t = t else formula
            let cond_save = self.save();
            let cond = match (|| -> Result<Condition, ParseError> {
                let t1 = self.term(false)?;
                self.require_punct("=")?;
                let t2 = self.term(false)?;
                Ok(Condition::Eq(t1, t2))
            })() {
                Ok(c) => c,
                Err(_) => {
                    self.restore(cond_save);
                    let phi = self.formula()?;
                    Condition::Formula(phi)
                }
            };
            self.require_kw("then")?;
            let p = self.process()?;
            let q = self.else_process()?;
            return Ok(Process::Comb {
                comb: ProcessComb::Cond(cond),
                left: Box::new(p),
                right: Box::new(q),
            });
        }
        if self.try_kw("let") {
            // `let pat = t [, pat = t]* in p` or with newline-separated
            // bindings (Tamarin's `genericletBlock = many1 definition` has no
            // separator between bindings).
            let mut bindings: Vec<(Term, Term)> = Vec::new();
            loop {
                let pat = self.term(false)?;
                self.require_punct("=")?;
                let val = self.term(false)?;
                bindings.push((pat, val));
                let _ = self.try_punct(",");
                self.skip_ws();
                if self.at_keyword("in") { break; }
                // Heuristic: if the next token doesn't look like the start of
                // another binding (an identifier or sigil-led variable), we
                // also stop.
                let probe = self.save();
                let cont = matches!(self.lx.peek(),
                    Some(c) if c.is_alphabetic() || c == '~' || c == '$' || c == '#' || c == '%' || c == '<');
                self.restore(probe);
                if !cont { break; }
            }
            self.require_kw("in")?;
            let p = self.process()?;
            let q = self.else_process()?;
            // Right-fold the bindings into nested Let combinators.
            let mut acc = p;
            for (pat, val) in bindings.into_iter().rev() {
                acc = Process::Comb {
                    comb: ProcessComb::Let { pat, value: val },
                    left: Box::new(acc),
                    right: Box::new(q.clone()),
                };
            }
            return Ok(acc);
        }
        // null process
        if self.try_punct("0") {
            return Ok(Process::Null);
        }
        // Parenthesised process — possibly with `@ term` annotation.
        if self.try_punct("(") {
            let p = self.process()?;
            self.require_punct(")")?;
            if self.try_punct("@") {
                let m = self.term(false)?;
                return Ok(Process::AtAnnotation(Box::new(p), m));
            }
            return Ok(p);
        }
        // Sapic action: new / insert / delete / in / out / lock / unlock / event / msr
        let save = self.save();
        if let Some((act, _)) = self.try_sapic_action()? {
            // Optional `; rest` (sequencing)
            let body = if self.try_punct(";") {
                self.action_process()?
            } else {
                Process::Null
            };
            return Ok(Process::Action { action: act, body: Box::new(body) });
        }
        self.restore(save);
        // Process call by name: ident or ident(args)
        let save2 = self.save();
        if let Some(id) = self.lx.identifier() {
            // Heuristic: if followed by `(`, parse as call args.
            let args = if self.try_punct("(") {
                let mut ts = Vec::new();
                if !self.try_punct(")") {
                    loop {
                        let t = self.term(false)?;
                        ts.push(t);
                        if !self.try_punct(",") { break; }
                    }
                    self.require_punct(")")?;
                }
                ts
            } else { vec![] };
            return Ok(Process::Call { name: id, args });
        }
        self.restore(save2);
        Err(self.err("expected process"))
    }

    fn else_process(&mut self) -> Result<Process, ParseError> {
        if self.try_kw("else") {
            self.process()
        } else { Ok(Process::Null) }
    }

    fn try_sapic_action(&mut self) -> Result<Option<(SapicAction, ())>, ParseError> {
        self.skip_ws();
        let save = self.save();
        if self.try_kw("new") {
            let v = self.var_spec()?;
            return Ok(Some((SapicAction::New(v), ())));
        }
        if self.try_kw("insert") {
            let t1 = self.term(false)?;
            self.require_punct(",")?;
            let t2 = self.term(false)?;
            return Ok(Some((SapicAction::Insert(t1, t2), ())));
        }
        if self.try_kw("delete") {
            let t = self.term(false)?;
            return Ok(Some((SapicAction::Delete(t), ())));
        }
        if self.try_kw("in") {
            self.require_punct("(")?;
            // Either `(msg)` or `(chan, msg)`
            let first = self.term(false)?;
            let res = if self.try_punct(",") {
                let snd = self.term(false)?;
                self.require_punct(")")?;
                SapicAction::ChIn { chan: Some(first), msg: snd }
            } else {
                self.require_punct(")")?;
                SapicAction::ChIn { chan: None, msg: first }
            };
            return Ok(Some((res, ())));
        }
        if self.try_kw("out") {
            self.require_punct("(")?;
            let first = self.term(false)?;
            let res = if self.try_punct(",") {
                let snd = self.term(false)?;
                self.require_punct(")")?;
                SapicAction::ChOut { chan: Some(first), msg: snd }
            } else {
                self.require_punct(")")?;
                SapicAction::ChOut { chan: None, msg: first }
            };
            return Ok(Some((res, ())));
        }
        if self.try_kw("lock") {
            let t = self.term(false)?;
            return Ok(Some((SapicAction::Lock(t), ())));
        }
        if self.try_kw("unlock") {
            let t = self.term(false)?;
            return Ok(Some((SapicAction::Unlock(t), ())));
        }
        if self.try_kw("event") {
            let f = self.fact()?;
            return Ok(Some((SapicAction::Event(f), ())));
        }
        // Embedded MSR: `[..] --[..]-> [..]`
        if self.lx.peek() == Some('[') {
            let prems = self.fact_list()?;
            let (acts, restrs) = if self.try_punct("-->") {
                (vec![], vec![])
            } else if self.try_punct("--[") {
                let mut acts = Vec::new();
                let mut rs = Vec::new();
                if !self.try_punct("]->") {
                    loop {
                        let item = self.fact_or_restr()?;
                        match item {
                            FactOrRestr::Fact(f) => acts.push(f),
                            FactOrRestr::Restr(p) => rs.push(p),
                        }
                        if !self.try_punct(",") { break; }
                    }
                    self.require_punct("]->")?;
                }
                (acts, rs)
            } else {
                self.restore(save);
                return Ok(None);
            };
            let concs = self.fact_list()?;
            return Ok(Some((SapicAction::Msr {
                prems, acts, concs, restrictions: restrs
            }, ())));
        }
        self.restore(save);
        Ok(None)
    }

    // =========================================================================
    // Facts
    // =========================================================================

    fn fact(&mut self) -> Result<Fact, ParseError> {
        self.skip_ws();
        let persistent = self.try_punct("!");
        let name = self.ident()?;
        if !name.chars().next().map_or(false, |c| c.is_ascii_uppercase()) {
            return Err(self.err(format!("fact name `{}` must start with uppercase", name)));
        }
        self.require_punct("(")?;
        let mut args = Vec::new();
        if !self.try_punct(")") {
            loop {
                let t = self.term(false)?;
                args.push(t);
                if !self.try_punct(",") { break; }
            }
            self.require_punct(")")?;
        }
        let mut annotations = Vec::new();
        if self.try_punct("[") {
            if !self.try_punct("]") {
                loop {
                    if self.try_punct("+") { annotations.push(FactAnnotation::SolveFirst); }
                    else if self.try_punct("-") { annotations.push(FactAnnotation::SolveLast); }
                    else if self.try_kw("no_precomp") { annotations.push(FactAnnotation::NoSources); }
                    else { break; }
                    if !self.try_punct(",") { break; }
                }
                self.require_punct("]")?;
            }
        }
        // HS-faithful parse-time canonicalisation, mirroring
        // `Theory.Text.Parser.Fact.mkProtoFact` (Fact.hs:56-63) combined with
        // `factTagMultiplicity` (Model/Fact.hs:354-360) and `factTagName`
        // (Model/Fact.hs:507-517).  Any fact whose name uppercases to one of
        // the reserved special names becomes that special fact, which:
        //   * fixes the CANONICAL name (KU/KD/Ded/Fr/In/Out),
        //   * fixes the multiplicity from the tag (KU and KD are Persistent;
        //     everything else here is Linear), discarding the user-written `!`,
        //   * enforces arity one (`singleTerm`) — a parse `fail` on mismatch,
        //   * drops annotations for all special facts except IN
        //     (`inFactAnn ann` keeps them; outFact/kuFact/kdFact/dedLogFact/
        //     freshFact take no annotations),
        //   * rejects `!Fr(...)` ("fresh facts cannot be persistent").
        // Because HS wraps the whole `fact'` body in `try`, a `fail` here
        // backtracks; in rule context this surfaces as a hard load error,
        // and in formula context the alternative (term atom) is tried.  We
        // mirror that by returning `Err` from `fact()`.
        let upper = name.to_ascii_uppercase();
        // (canonical name, persistent, keep-annotations)
        let canonical: Option<(&str, bool, bool)> = match upper.as_str() {
            "OUT" => Some(("Out", false, false)),
            "IN"  => Some(("In", false, true)),
            "KU"  => Some(("KU", true, false)),
            "KD"  => Some(("KD", true, false)),
            "DED" => Some(("Ded", false, false)),
            "FR"  => Some(("Fr", false, false)),
            _     => None,
        };
        if let Some((cname, cpersistent, keep_ann)) = canonical {
            // `!Fr(...)` is a parse error (Fact.hs:45).
            if upper == "FR" && persistent {
                return Err(self.err("fresh facts cannot be persistent"));
            }
            // `singleTerm`: special facts have arity one (Fact.hs:52-54).
            if args.len() != 1 {
                return Err(self.err(format!(
                    "fact '{}' used with arity {} instead of arity one",
                    name, args.len())));
            }
            return Ok(Fact {
                persistent: cpersistent,
                name: cname.to_string(),
                args,
                annotations: if keep_ann { annotations } else { Vec::new() },
            });
        }
        Ok(Fact { persistent, name, args, annotations })
    }

    // =========================================================================
    // Formulas
    // =========================================================================

    fn formula(&mut self) -> Result<Formula, ParseError> {
        self.iff()
    }

    fn iff(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.implies()?;
        if self.try_punct("<=>") || self.try_punct("⇔") {
            let rhs = self.implies()?;
            Ok(Formula::Iff(Box::new(lhs), Box::new(rhs)))
        } else { Ok(lhs) }
    }

    fn implies(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.disjuncts()?;
        if self.try_punct("==>") || self.try_punct("⇒") {
            let rhs = self.implies()?;
            Ok(Formula::Implies(Box::new(lhs), Box::new(rhs)))
        } else { Ok(lhs) }
    }

    fn disjuncts(&mut self) -> Result<Formula, ParseError> {
        let mut lhs = self.conjuncts()?;
        loop {
            // `|` is also process parallel — but inside formulas it's OR.
            if self.try_punct("|") || self.try_punct("∨") {
                let rhs = self.conjuncts()?;
                lhs = Formula::Or(Box::new(lhs), Box::new(rhs));
            } else { break; }
        }
        Ok(lhs)
    }

    fn conjuncts(&mut self) -> Result<Formula, ParseError> {
        let mut lhs = self.negation()?;
        loop {
            if self.try_punct("&") || self.try_punct("∧") {
                let rhs = self.negation()?;
                lhs = Formula::And(Box::new(lhs), Box::new(rhs));
            } else { break; }
        }
        Ok(lhs)
    }

    fn negation(&mut self) -> Result<Formula, ParseError> {
        if self.try_kw("not") || self.try_punct("¬") {
            let f = self.fatom()?;
            Ok(Formula::Not(Box::new(f)))
        } else {
            self.fatom()
        }
    }

    fn fatom(&mut self) -> Result<Formula, ParseError> {
        self.skip_ws();
        if self.try_kw("F") || self.try_punct("⊥") {
            return Ok(Formula::False);
        }
        if self.try_kw("T") || self.try_punct("⊤") {
            return Ok(Formula::True);
        }
        // Quantifiers: All / ∀ / Ex / ∃
        if self.try_kw("All") || self.try_punct("∀") {
            let mut vs = Vec::new();
            loop {
                self.skip_ws();
                if self.lx.peek() == Some('.') { break; }
                let v = self.var_spec()?;
                vs.push(v);
            }
            self.require_punct(".")?;
            let f = self.iff()?;
            return Ok(Formula::Forall(vs, Box::new(f)));
        }
        if self.try_kw("Ex") || self.try_punct("∃") {
            let mut vs = Vec::new();
            loop {
                self.skip_ws();
                if self.lx.peek() == Some('.') { break; }
                let v = self.var_spec()?;
                vs.push(v);
            }
            self.require_punct(".")?;
            let f = self.iff()?;
            return Ok(Formula::Exists(vs, Box::new(f)));
        }
        // Parenthesised formula — backtrack to term-relational on failure,
        // since e.g. `(a+z) = b` should parse as a relational equality atom
        // whose LHS happens to be a parenthesised term.
        if self.lx.peek() == Some('(') {
            let save_p = self.save();
            self.lx.bump();
            self.skip_ws();
            if let Ok(f) = self.iff() {
                if self.try_punct(")") {
                    return Ok(f);
                }
            }
            self.restore(save_p);
        }
        // Atom: try last(t), action f@t, equality, less, subterm, smaller, predicate
        let save = self.save();
        if self.try_kw("last") {
            self.require_punct("(")?;
            let t = self.term(false)?;
            self.require_punct(")")?;
            return Ok(Formula::Atom(Atom::Last(t)));
        }
        // Try fact@t (action atom)
        let save_f = self.save();
        if let Ok(f) = self.fact() {
            if self.try_punct("@") {
                let t = self.term(false)?;
                return Ok(Formula::Atom(Atom::Action(f, t)));
            }
            // Predicate atom (no @)
            return Ok(Formula::Atom(Atom::Pred(f)));
        }
        self.restore(save_f);
        // Try term-level atom: t = t / t < t / t << t / t (<) t
        let lhs = self.term(false)?;
        if self.try_punct("=") {
            let rhs = self.term(false)?;
            return Ok(Formula::Atom(Atom::Eq(lhs, rhs)));
        }
        if self.try_punct("<<") || self.try_punct("⊏") {
            let rhs = self.term(false)?;
            return Ok(Formula::Atom(Atom::Subterm(lhs, rhs)));
        }
        if self.try_punct("(<)") {
            let rhs = self.term(false)?;
            return Ok(Formula::Atom(Atom::LessMset(lhs, rhs)));
        }
        if self.try_punct("<") {
            let rhs = self.term(false)?;
            return Ok(Formula::Atom(Atom::Less(lhs, rhs)));
        }
        let _ = save;
        Err(self.err("expected formula atom"))
    }

    // =========================================================================
    // Terms
    // =========================================================================

    /// Top-level term parser. `eqn` indicates we're inside an equation
    /// (which forbids AC operators).
    fn term(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.tupleterm(eqn)
    }

    /// Right-associative tuple `<a, b, c, ...>` is parsed by `pairing` —
    /// at the `term` level we handle comma-grouped sequence only inside
    /// `<...>` brackets. So `tupleterm` here is just `msetterm` plus a
    /// chain on `,` when used inside angled brackets.
    fn tupleterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        // For top-level, no comma-grouping happens unless inside <...>.
        self.msetterm(eqn)
    }

    /// Parse a comma-separated term sequence and fold into a right-assoc
    /// pair (or single term). Used inside `<...>` and `f{...}`.
    fn tuple_contents(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut items = Vec::new();
        loop {
            let t = self.msetterm(eqn)?;
            items.push(t);
            if !self.try_punct(",") { break; }
        }
        if items.len() == 1 {
            Ok(items.into_iter().next().unwrap())
        } else {
            Ok(Term::Pair(items))
        }
    }

    fn msetterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut lhs = self.natterm(eqn)?;
        if !eqn && self.enable_mset {
            loop {
                self.skip_ws();
                // `++` or `+` (as multiset union); careful with `+` for NDC
                // and `%+` for nat plus, which are handled separately.
                if self.lx.rest().starts_with("++") {
                    self.lx.bump(); self.lx.bump(); self.skip_ws();
                    let rhs = self.natterm(eqn)?;
                    lhs = Term::BinOp(BinOp::Union, Box::new(lhs), Box::new(rhs));
                } else if self.lx.rest().starts_with('+')
                    && !self.lx.rest().starts_with("+>")
                {
                    // Avoid `+` that's part of process NDC. At term level
                    // we always treat `+` as union.
                    self.lx.bump(); self.skip_ws();
                    let rhs = self.natterm(eqn)?;
                    lhs = Term::BinOp(BinOp::Union, Box::new(lhs), Box::new(rhs));
                } else { break; }
            }
        }
        Ok(lhs)
    }

    fn natterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut lhs = self.xorterm(eqn)?;
        if !eqn && self.enable_nat {
            while self.try_punct("%+") {
                let rhs = self.xorterm(eqn)?;
                lhs = Term::BinOp(BinOp::NatPlus, Box::new(lhs), Box::new(rhs));
            }
        }
        Ok(lhs)
    }

    fn xorterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut lhs = self.multterm(eqn)?;
        if !eqn && self.enable_xor {
            while self.try_kw("XOR") || self.try_punct("⊕") {
                let rhs = self.multterm(eqn)?;
                lhs = Term::BinOp(BinOp::Xor, Box::new(lhs), Box::new(rhs));
            }
        }
        Ok(lhs)
    }

    fn multterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        if eqn || !self.enable_dh {
            return self.atom_term(eqn);
        }
        let mut lhs = self.expterm(eqn)?;
        loop {
            self.skip_ws();
            // Multiplication is `*` but not `**`. Avoid consuming `*}` (formal-comment end).
            if self.lx.peek() == Some('*') && self.lx.peek2() != Some('}') {
                self.lx.bump(); self.skip_ws();
                let rhs = self.expterm(eqn)?;
                lhs = Term::BinOp(BinOp::Mult, Box::new(lhs), Box::new(rhs));
            } else { break; }
        }
        Ok(lhs)
    }

    fn expterm(&mut self, eqn: bool) -> Result<Term, ParseError> {
        let mut lhs = self.atom_term(eqn)?;
        // `^` is right-associative in Tamarin (Haskell `chainl1` actually but
        // the operator is conventionally treated as such). Use left-assoc to
        // match `chainl1` semantics.
        while self.try_punct("^") {
            let rhs = self.atom_term(eqn)?;
            lhs = Term::BinOp(BinOp::Exp, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    /// One atomic term.
    fn atom_term(&mut self, eqn: bool) -> Result<Term, ParseError> {
        self.skip_ws();
        // SAPIC pattern-match prefix `=t` — treat as PatMatch wrapper.
        if self.lx.peek() == Some('=') {
            // Avoid consuming `=` if it's the start of an operator like `==>`,
            // `=>`, or `==`.
            let r = self.lx.rest();
            if !r.starts_with("==") && !r.starts_with("=>") {
                self.lx.bump();
                self.skip_ws();
                let inner = self.atom_term(eqn)?;
                return Ok(Term::PatMatch(Box::new(inner)));
            }
        }
        // Parens for grouping
        if self.try_punct("(") {
            let t = self.msetterm(eqn)?;
            // Allow a tuple inside () with ',' — actually Tamarin uses `<>` for
            // pairs and `()` for grouping only. So no comma inside `()`.
            self.require_punct(")")?;
            return Ok(t);
        }
        // Pair `<a, b, ...>` (right-associative). The `<<` subterm and
        // `<=>` iff operators only appear at formula level — at term level a
        // bare `<` always opens a tuple. We do refuse `<-` (process arrow).
        if self.lx.peek() == Some('<') {
            let r = self.lx.rest();
            if !r.starts_with("<-") {
                self.lx.bump(); // consume '<'
                self.skip_ws();
                let mut items = Vec::new();
                if !self.try_punct(">") {
                    loop {
                        let t = self.msetterm(eqn)?;
                        items.push(t);
                        if !self.try_punct(",") { break; }
                    }
                    self.require_punct(">")?;
                }
                if items.len() == 1 {
                    return Ok(items.into_iter().next().unwrap());
                }
                return Ok(Term::Pair(items));
            }
        }
        // Special tokens
        if self.try_kw("DH_neutral") { return Ok(Term::DhNeutral); }
        if self.try_punct("1:nat") { return Ok(Term::NatOne); }
        if self.try_punct("%1") { return Ok(Term::NatOne); }
        // `1` only valid when DH is enabled; we accept it always at parse level.
        // Word-boundary: don't match `1` if it's the start of a longer
        // identifier like `1G` or `1abc`.
        {
            let save = self.save();
            self.skip_ws();
            if self.lx.peek() == Some('1') {
                let mut probe = self.lx.clone();
                probe.bump();
                let next = probe.peek();
                if next.map_or(true, |c| !c.is_alphanumeric() && c != '_') {
                    self.lx.bump();
                    self.skip_ws();
                    return Ok(Term::NumberOne);
                }
            }
            self.restore(save);
        }
        // Sigil-prefixed variables: ~x, $x, #x, %x.
        if matches!(self.lx.peek(), Some('~') | Some('$') | Some('#')) {
            // Could be a fresh-name literal `~'n'` or `%'n'` — handled below.
            let c = self.lx.peek().unwrap();
            let mut probe = self.lx.clone();
            probe.bump();
            if c == '~' && probe.peek() == Some('\'') {
                self.lx.bump();
                let s = self.lx.single_quoted().ok_or_else(|| self.err("bad fresh literal"))?;
                return Ok(Term::FreshLit(s));
            }
            // Otherwise: variable.
            if let Some(v) = self.try_var_spec()? {
                let v = self.attach_sort_suffix(v)?;
                return Ok(Term::Var(v));
            }
        }
        if self.lx.peek() == Some('%') {
            // %1 / %'n' / %x — distinguish.
            let mut probe = self.lx.clone();
            probe.bump();
            match probe.peek() {
                Some('\'') => {
                    self.lx.bump();
                    let s = self.lx.single_quoted().ok_or_else(|| self.err("bad nat literal"))?;
                    return Ok(Term::NatLit(s));
                }
                Some('1') => {
                    self.lx.bump();
                    self.lx.bump();
                    return Ok(Term::NatOne);
                }
                Some(c) if c.is_ascii_alphabetic() => {
                    if let Some(v) = self.try_var_spec()? {
                        let v = self.attach_sort_suffix(v)?;
                        return Ok(Term::Var(v));
                    }
                }
                _ => {}
            }
        }
        // Literal `'foo'` is a public name term.
        if self.lx.peek() == Some('\'') {
            let s = self.lx.single_quoted().ok_or_else(|| self.err("bad public literal"))?;
            return Ok(Term::PubLit(s));
        }
        // Identifier — could be: diff(...), function application f(...),
        // algebraic application f{a}b, sort-suffixed var x:msg, or a bare
        // variable / nullary function.
        let save_id = self.save();
        if let Some(id) = self.lx.identifier() {
            // diff(a, b)
            if id == "diff" && self.lx.peek() == Some('(') {
                self.lx.bump();
                self.skip_ws();
                let a = self.msetterm(eqn)?;
                self.require_punct(",")?;
                let b = self.msetterm(eqn)?;
                self.require_punct(")")?;
                return Ok(Term::Diff(Box::new(a), Box::new(b)));
            }
            self.skip_ws();
            if self.lx.peek() == Some('(') {
                // Look one token ahead inside `(`: if it's `<)` (the multiset
                // less-than operator at process level), this isn't a
                // function call but the `(<)` token. Defer to the variable
                // path so the `(<)` check above the term parser can see it.
                let probe = self.save();
                self.lx.bump();
                let is_lessmset = self.lx.peek() == Some('<')
                    && {
                        let mut p2 = self.lx.clone();
                        p2.bump();
                        p2.peek() == Some(')')
                    };
                self.restore(probe);
                if is_lessmset {
                    let idx = self.try_dot_index();
                    let v = VarSpec { name: id, idx, sort: SortHint::Untagged, typ: None };
                    let v = self.attach_sort_suffix(v)?;
                    return Ok(Term::Var(v));
                }
                self.lx.bump();
                self.skip_ws();
                let mut ts = Vec::new();
                if !self.try_punct(")") {
                    loop {
                        let t = self.msetterm(eqn)?;
                        ts.push(t);
                        if !self.try_punct(",") { break; }
                    }
                    self.require_punct(")")?;
                }
                return Ok(Term::App(id, ts));
            }
            if self.lx.peek() == Some('{') {
                self.lx.bump();
                self.skip_ws();
                let arg1 = self.tuple_contents(eqn)?;
                self.require_punct("}")?;
                let arg2 = self.atom_term(eqn)?;
                return Ok(Term::AlgApp(id, Box::new(arg1), Box::new(arg2)));
            }
            // Bare identifier: untagged variable. Optionally with index `.<n>`
            // (only consumes `.` if followed by a digit) and optionally with
            // sort suffix `:msg|pub|fresh|node|nat` or a SAPIC type annotation.
            let idx = self.try_dot_index();
            let v = VarSpec { name: id, idx, sort: SortHint::Untagged, typ: None };
            let v = self.attach_sort_suffix(v)?;
            return Ok(Term::Var(v));
        }
        self.restore(save_id);
        Err(self.err("expected term"))
    }

    fn attach_sort_suffix(&mut self, mut v: VarSpec) -> Result<VarSpec, ParseError> {
        // Only sortless prefixes can have a suffix.
        // Suffix syntax: `<id>:msg`, `:pub`, `:fresh`, `:node`, `:nat`.
        let save = self.save();
        if self.try_punct(":") {
            // Distinguish suffix sort vs SAPIC type annotation.
            let snap = self.save();
            if self.try_kw("msg") { v.sort = SortHint::Suffix(SuffixSort::Msg); return Ok(v); }
            if self.try_kw("pub") { v.sort = SortHint::Suffix(SuffixSort::Pub); return Ok(v); }
            if self.try_kw("fresh") { v.sort = SortHint::Suffix(SuffixSort::Fresh); return Ok(v); }
            if self.try_kw("node") { v.sort = SortHint::Suffix(SuffixSort::Node); return Ok(v); }
            if self.try_kw("nat") { v.sort = SortHint::Suffix(SuffixSort::Nat); return Ok(v); }
            // Else SAPIC type annotation.
            self.restore(snap);
            if let Some(t) = self.lx.identifier() {
                v.typ = Some(t);
                return Ok(v);
            }
            self.restore(save);
        }
        Ok(v)
    }

    /// Parse a variable specification. Returns None if no var sigil/identifier
    /// is present.
    fn try_var_spec(&mut self) -> Result<Option<VarSpec>, ParseError> {
        self.skip_ws();
        let save = self.save();
        let sort = match self.lx.peek() {
            Some('~') => { self.lx.bump(); SortHint::Fresh }
            Some('$') => { self.lx.bump(); SortHint::Pub }
            Some('#') => { self.lx.bump(); SortHint::Node }
            Some('%') => {
                // Could be `%1` (nat one) or `%'n'` (nat name lit) or `%x` (nat var).
                let mut probe = self.lx.clone();
                probe.bump();
                match probe.peek() {
                    Some('\'') | Some('1') => return Ok(None), // handled by literal/atom path
                    Some(c) if c.is_ascii_alphabetic() => { self.lx.bump(); SortHint::Nat }
                    _ => { return Ok(None); }
                }
            }
            Some(c) if c.is_alphabetic() => SortHint::Untagged,
            _ => return Ok(None),
        };
        let name_save = self.save();
        let id = match self.lx.identifier() {
            Some(s) => s,
            None => { self.restore(save); return Ok(None); }
        };
        let _ = name_save;
        let idx = self.try_dot_index();
        Ok(Some(VarSpec { name: id, idx, sort, typ: None }))
    }

    fn var_spec(&mut self) -> Result<VarSpec, ParseError> {
        let v = self.try_var_spec()?.ok_or_else(|| self.err("expected variable"))?;
        // Allow `: msg | pub | fresh | node | nat` sort suffix or a SAPIC
        // type annotation after the variable.
        self.attach_sort_suffix(v)
    }

    /// Consume `.<digit>+` as a variable index, otherwise leave input
    /// alone. Used so that `x.` (in quantifier lists, function arity slashes,
    /// etc.) doesn't accidentally swallow the trailing dot.
    fn try_dot_index(&mut self) -> u64 {
        let save = self.save();
        // Don't skip whitespace — `.` must be immediately after the identifier
        // for it to be an index. (Tamarin's `indexedIdentifier` matches
        // `dot *> natural`, but the dot follows the lexeme without an
        // intervening token break.)
        if self.lx.peek() != Some('.') { return 0; }
        self.lx.bump();
        // After the dot we accept digits with no intervening whitespace.
        match self.lx.peek() {
            Some(c) if c.is_ascii_digit() => {
                self.lx.natural().unwrap_or_else(|| {
                    self.restore(save);
                    0
                })
            }
            _ => { self.restore(save); 0 }
        }
    }

    // =========================================================================
    // Flag formulas (for #ifdef)
    // =========================================================================

    fn flag_disjuncts(&mut self) -> Result<FlagFormula, ParseError> {
        let mut lhs = self.flag_conjuncts()?;
        while self.try_punct("|") || self.try_punct("∨") {
            let rhs = self.flag_conjuncts()?;
            lhs = FlagFormula::Or(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn flag_conjuncts(&mut self) -> Result<FlagFormula, ParseError> {
        let mut lhs = self.flag_negation()?;
        while self.try_punct("&") || self.try_punct("∧") {
            let rhs = self.flag_negation()?;
            lhs = FlagFormula::And(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn flag_negation(&mut self) -> Result<FlagFormula, ParseError> {
        if self.try_kw("not") || self.try_punct("¬") {
            let f = self.flag_atom()?;
            Ok(FlagFormula::Not(Box::new(f)))
        } else { self.flag_atom() }
    }

    fn flag_atom(&mut self) -> Result<FlagFormula, ParseError> {
        if self.try_punct("(") {
            let f = self.flag_disjuncts()?;
            self.require_punct(")")?;
            return Ok(f);
        }
        let id = self.ident()?;
        Ok(FlagFormula::Atom(id))
    }

    fn eval_flagformula(&self, f: &FlagFormula) -> bool {
        match f {
            FlagFormula::Atom(s) => self.flags.contains(s),
            FlagFormula::Not(g) => !self.eval_flagformula(g),
            FlagFormula::And(a, b) => self.eval_flagformula(a) && self.eval_flagformula(b),
            FlagFormula::Or(a, b) => self.eval_flagformula(a) || self.eval_flagformula(b),
        }
    }
}

#[derive(Debug)]
enum BranchEnd { Else, Endif, Eof }

#[derive(Debug)]
enum FactOrRestr {
    Fact(Fact),
    Restr(Formula),
}

// =============================================================================
// String-form formula parsing (lemmas and restrictions store the formula as
// a quoted string)
// =============================================================================

pub fn parse_formula_str(s: &str) -> Result<Formula, ParseError> {
    let mut p = Parser::new(s, &[], false);
    let f = p.formula()?;
    p.skip_ws();
    if !p.lx.is_eof() {
        return Err(p.err("trailing garbage in formula string"));
    }
    Ok(f)
}

// We need to silence one unused method warning if `is_ident_char` appears
// unused in some configurations.
#[allow(dead_code)]
fn _kw_anchor() { let _ = is_ident_char('a'); }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_theory() {
        let s = "theory Foo begin end";
        let t = parse_theory(s, &[]).unwrap();
        assert_eq!(t.name, "Foo");
        assert!(t.items.is_empty());
    }

    #[test]
    fn theory_with_builtins() {
        let s = "theory T begin builtins: hashing, signing end";
        let t = parse_theory(s, &[]).unwrap();
        match &t.items[0] {
            TheoryItem::Builtins(v) => assert_eq!(v, &vec!["hashing".to_string(), "signing".into()]),
            x => panic!("expected builtins, got {:?}", x),
        }
    }

    #[test]
    fn simple_rule() {
        let s = r#"
            theory T begin
              rule R: [Fr(~k)] --[ Foo(~k) ]-> [ Out(~k) ]
            end
        "#;
        let t = parse_theory(s, &[]).unwrap();
        match &t.items[0] {
            TheoryItem::Rule(r) => {
                assert_eq!(r.name, "R");
                assert_eq!(r.premises.len(), 1);
                assert_eq!(r.actions.len(), 1);
                assert_eq!(r.conclusions.len(), 1);
            }
            x => panic!("expected rule, got {:?}", x),
        }
    }

    #[test]
    fn lemma_with_quantifier() {
        let s = r#"
            theory T begin
              lemma secret: "All x #i. K(x) @ i ==> F"
            end
        "#;
        let t = parse_theory(s, &[]).unwrap();
        match &t.items[0] {
            TheoryItem::Lemma(_) => {}
            x => panic!("expected lemma, got {:?}", x),
        }
    }

    #[test]
    fn comment_handling() {
        let s = "/* outer */ theory T // line\n begin /* x /* y */ z */ end";
        let t = parse_theory(s, &[]).unwrap();
        assert_eq!(t.name, "T");
    }

    #[test]
    fn term_application() {
        let mut p = Parser::new("h(<a, b>, ~k)", &[], false);
        let t = p.term(false).unwrap();
        match t {
            Term::App(name, args) => {
                assert_eq!(name, "h");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn formula_string() {
        let f = parse_formula_str("All x. P(x) ==> Q(x)").unwrap();
        match f {
            Formula::Forall(_, _) => {}
            _ => panic!("expected Forall"),
        }
    }
}
