//! Structured tactics and their pretty-printing.
//!
//! Mirrors the Haskell reference:
//!   - data type:  `Theory.Constraint.System.Tactic / Prio / Deprio`
//!     (lib/theory/src/Theory/Constraint/System.hs:439-504)
//!   - parser:     `Theory.Text.Parser.Tactics`
//!     (lib/theory/src/Theory/Text/Parser/Tactics.hs:60-115)
//!   - pretty:     `prettyTactic` (lib/theory/src/TheoryObject.hs:881-909)
//!
//! The Rust parser captures the raw tactic body verbatim; this module
//! re-parses that body into the same structure HS keeps (presort char +
//! a list of prio/deprio blocks, each carrying a ranking name and the
//! per-disjuncts *string representations* exactly as HS builds them in
//! `function`/`functionNot`/`functionAnd`/`functionOr`), then renders it
//! through the ported `prettyTactic` so output is byte-identical.

/// A single selector function as written in a tactic, e.g.
/// `regex "In_S"` or `dhreNoise "curve"`.  Mirrors HS `function`
/// (Tactics.hs:66-70) producing `nameToFunction (name, params)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SelectorLeaf {
    /// The function name (`regex`, `dhreNoise`, `isFactName`, …).
    pub name: String,
    /// The double-quoted parameters in source order.
    pub params: Vec<String>,
}

/// The boolean expression tree HS builds per `disjuncts` line via
/// `functionNot`/`functionAnd`/`functionOr` (Tactics.hs:72-91).  One
/// `SelectorExpr` corresponds to one entry of HS `functionsPrio`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SelectorExpr {
    Leaf(SelectorLeaf),
    Not(Box<SelectorExpr>),
    And(Box<SelectorExpr>, Box<SelectorExpr>),
    Or(Box<SelectorExpr>, Box<SelectorExpr>),
}

/// A parsed `prio:`/`deprio:` block.
///
/// `ranking` is the `{...}` selector name (HS `stringRankingPrio`,
/// defaulting to `"id"`); `disjuncts` are the per-line string
/// representations HS stores in `stringsPrio` — one entry per parsed
/// `disjuncts` (a `f "p" | g "q"` chain) in source order.
///
/// `selectors` is the EVALUABLE form of those same disjuncts — one
/// `SelectorExpr` per `disjuncts` line, in the same order, mirroring HS
/// `functionsPrio :: [(AnnotatedGoal, ctx, System) -> Bool]`
/// (System.hs:442).  The prio recognises a goal iff ANY of these
/// expressions evaluates to True (HS `isPrio = or . sequenceA`,
/// ProofMethod.hs:884).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrioBlock {
    pub ranking: String,
    pub disjuncts: Vec<String>,
    pub selectors: Vec<SelectorExpr>,
}

/// A structured tactic: HS `Tactic { _name, _presort, _prios, _deprios }`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tactic {
    pub name: String,
    /// The single-character presort identifier as rendered by HS
    /// `goalRankingToChar` (System.hs:647-649). Defaults to `'s'`
    /// (HS `tactic` defaults presort to `SmartRanking False`,
    /// Tactics.hs:112).
    pub presort: char,
    pub prios: Vec<PrioBlock>,
    pub deprios: Vec<PrioBlock>,
}

impl Tactic {
    /// Parse a tactic from its name and raw body (the text following
    /// `tactic: <name>`, i.e. starting at `presort:`/`prio:`).
    pub fn parse(name: &str, raw: &str) -> Tactic {
        let mut p = TacticParser::new(raw);
        // presort: <letters>  (Tactics.hs:52-57, default SmartRanking False)
        let mut presort = 's';
        if p.try_kw("presort") {
            p.eat_colon();
            if let Some(word) = p.ident_letters() {
                presort = presort_char(&word);
            }
        }
        // many1 prio, then many1 deprio (Tactics.hs:113-114)
        let mut prios = Vec::new();
        while p.try_kw("prio") {
            prios.push(p.prio_block());
        }
        let mut deprios = Vec::new();
        while p.try_kw("deprio") {
            deprios.push(p.prio_block());
        }
        Tactic { name: name.to_string(), presort, prios, deprios }
    }

    /// Render via the ported HS `prettyTactic` (TheoryObject.hs:881-909).
    pub fn render(&self) -> String {
        let mut out = String::new();
        // `tactic: <name>` $-$ `presort: <char>`
        out.push_str("tactic: ");
        out.push_str(&self.name);
        out.push('\n');
        out.push_str("presort: ");
        out.push(self.presort);
        // sep [ ppTabTab "prio" ..., ppTabTab "deprio" ... ]
        // Each non-empty block contributes `prio: {r}` / `deprio: {r}`
        // followed by the nest-2 selector lines; blocks are joined by a
        // newline (vertical `sep`/`vcat`), with no blank lines.
        for b in &self.prios {
            out.push('\n');
            out.push_str(&render_block("prio", b));
        }
        for b in &self.deprios {
            out.push('\n');
            out.push_str(&render_block("deprio", b));
        }
        out
    }
}

/// `ppTab` for one block: `<kw>: {ranking}` $-$ nest-2 prettified lines.
fn render_block(kw: &str, b: &PrioBlock) -> String {
    let mut out = String::new();
    out.push_str(kw);
    out.push_str(": {");
    out.push_str(&b.ranking);
    out.push('}');
    for d in &b.disjuncts {
        out.push('\n');
        out.push_str("  ");
        out.push_str(&prettify(d));
    }
    out
}

/// HS `prettify` (TheoryObject.hs:904-909): split on whitespace (`words`),
/// then concatenate tokens with operator tokens (`|`, `&`, `not`)
/// rendered with their canonical spacing and all other tokens joined
/// with no separator.
fn prettify(s: &str) -> String {
    let mut out = String::new();
    for tok in s.split_whitespace() {
        match tok {
            "|" => out.push_str(" | "),
            "&" => out.push_str(" & "),
            "not" => out.push_str("not "),
            other => out.push_str(other),
        }
    }
    out
}

/// Map a presort token (HS `goalRankingPresort`, parsed with `noOracle`)
/// to the char `goalRankingToChar` would print
/// (System.hs:600-623, 647-649). Unknown tokens fall back to their first
/// character (HS would `error`, but we keep robust output for rendering).
fn presort_char(word: &str) -> char {
    match word {
        "s" => 's', // SmartRanking False
        "S" => 'S', // SmartRanking True
        "p" => 'p', // SapicRanking
        "P" => 'P', // SapicPKCS11Ranking
        "c" => 'c', // UsefulGoalNrRanking
        "C" => 'C', // GoalNrRanking
        "i" => 'i', // InjRanking False
        "I" => 'I', // InjRanking True
        _ => word.chars().next().unwrap_or('s'),
    }
}

// ---------------------------------------------------------------------------
// Body parser
// ---------------------------------------------------------------------------

struct TacticParser<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> TacticParser<'a> {
    fn new(raw: &'a str) -> Self {
        TacticParser { s: raw.as_bytes(), i: 0 }
    }

    fn skip_ws(&mut self) {
        while self.i < self.s.len() {
            let c = self.s[self.i];
            if c == b' ' || c == b'\t' || c == b'\n' || c == b'\r' {
                self.i += 1;
            } else if c == b'/' && self.i + 1 < self.s.len() && self.s[self.i + 1] == b'/' {
                // line comment
                while self.i < self.s.len() && self.s[self.i] != b'\n' {
                    self.i += 1;
                }
            } else if c == b'/' && self.i + 1 < self.s.len() && self.s[self.i + 1] == b'*' {
                // block comment
                self.i += 2;
                while self.i + 1 < self.s.len()
                    && !(self.s[self.i] == b'*' && self.s[self.i + 1] == b'/')
                {
                    self.i += 1;
                }
                self.i = (self.i + 2).min(self.s.len());
            } else {
                break;
            }
        }
    }

    fn eof(&self) -> bool {
        self.i >= self.s.len()
    }

    /// Peek the identifier word starting at the current (post-ws) position
    /// without consuming.
    fn peek_word(&mut self) -> Option<String> {
        self.skip_ws();
        let start = self.i;
        let mut j = start;
        while j < self.s.len() && is_ident_byte(self.s[j]) {
            j += 1;
        }
        if j == start {
            None
        } else {
            Some(String::from_utf8_lossy(&self.s[start..j]).into_owned())
        }
    }

    /// If the next word is exactly `kw`, consume it (and its `:` is left
    /// for the caller). Returns true on match.
    fn try_kw(&mut self, kw: &str) -> bool {
        let save = self.i;
        self.skip_ws();
        let start = self.i;
        let mut j = start;
        while j < self.s.len() && is_ident_byte(self.s[j]) {
            j += 1;
        }
        if &self.s[start..j] == kw.as_bytes() {
            self.i = j;
            true
        } else {
            self.i = save;
            false
        }
    }

    fn eat_colon(&mut self) {
        self.skip_ws();
        if self.i < self.s.len() && self.s[self.i] == b':' {
            self.i += 1;
        }
    }

    /// `many1 letter` — a run of ascii letters (HS goalRankingPresort).
    fn ident_letters(&mut self) -> Option<String> {
        self.skip_ws();
        let start = self.i;
        while self.i < self.s.len() && self.s[self.i].is_ascii_alphabetic() {
            self.i += 1;
        }
        if self.i == start {
            None
        } else {
            Some(String::from_utf8_lossy(&self.s[start..self.i]).into_owned())
        }
    }

    /// Parse one prio/deprio block body: the optional `{ranking}` then
    /// `many1 disjuncts` (Tactics.hs:94-106). The `prio`/`deprio` keyword
    /// itself has already been consumed by the caller.
    fn prio_block(&mut self) -> PrioBlock {
        self.eat_colon();
        // option "id" (braced identifier)
        let ranking = self.braced_ident().unwrap_or_else(|| "id".to_string());
        let mut disjuncts = Vec::new();
        let mut selectors = Vec::new();
        // many1 disjuncts — keep parsing until a block keyword or EOF.
        loop {
            self.skip_ws();
            if self.eof() {
                break;
            }
            // Stop at the next block keyword.
            if let Some(w) = self.peek_word() {
                if matches!(w.as_str(), "prio" | "deprio" | "presort") {
                    break;
                }
            }
            match self.disjuncts() {
                Some((d, e)) => { disjuncts.push(d); selectors.push(e); }
                None => break,
            }
        }
        PrioBlock { ranking, disjuncts, selectors }
    }

    /// Optional `{ident}` (HS `braced identifier`).
    fn braced_ident(&mut self) -> Option<String> {
        self.skip_ws();
        if self.i < self.s.len() && self.s[self.i] == b'{' {
            self.i += 1;
            self.skip_ws();
            let start = self.i;
            while self.i < self.s.len() && self.s[self.i] != b'}' {
                self.i += 1;
            }
            let inner = String::from_utf8_lossy(&self.s[start..self.i])
                .trim()
                .to_string();
            if self.i < self.s.len() {
                self.i += 1; // consume '}'
            }
            Some(inner)
        } else {
            None
        }
    }

    /// `disjuncts = chainl1 conjuncts opLOr`; `conjuncts = chainl1
    /// negation opLAnd`; `negation = opLNot? function`. We build the HS
    /// *string representation* (Tactics.hs:70-91) for the whole chain.
    fn disjuncts(&mut self) -> Option<(String, SelectorExpr)> {
        let (mut s, mut e) = self.conjuncts()?;
        loop {
            self.skip_ws();
            if self.i < self.s.len() && self.s[self.i] == b'|' {
                self.i += 1;
                let (rs, re) = self.conjuncts()?;
                s = format!("{} | {}", s, rs);
                e = SelectorExpr::Or(Box::new(e), Box::new(re));
            } else {
                break;
            }
        }
        Some((s, e))
    }

    fn conjuncts(&mut self) -> Option<(String, SelectorExpr)> {
        let (mut s, mut e) = self.negation()?;
        loop {
            self.skip_ws();
            if self.i < self.s.len() && self.s[self.i] == b'&' {
                self.i += 1;
                let (rs, re) = self.negation()?;
                s = format!("{} & {}", s, rs);
                e = SelectorExpr::And(Box::new(e), Box::new(re));
            } else {
                break;
            }
        }
        Some((s, e))
    }

    fn negation(&mut self) -> Option<(String, SelectorExpr)> {
        // opLNot is the word `not`.
        if self.try_kw("not") {
            let (s, e) = self.function()?;
            Some((format!("not {}", s), SelectorExpr::Not(Box::new(e))))
        } else {
            self.function()
        }
    }

    /// `function = identifier (doubleQuoted functionValue)+`
    /// rendered as `f "p1" "p2"` (Tactics.hs:66-70).
    fn function(&mut self) -> Option<(String, SelectorExpr)> {
        self.skip_ws();
        let start = self.i;
        while self.i < self.s.len() && is_ident_byte(self.s[self.i]) {
            self.i += 1;
        }
        if self.i == start {
            return None;
        }
        let name = String::from_utf8_lossy(&self.s[start..self.i]).into_owned();
        let mut params = Vec::new();
        // many1 doubleQuoted functionValue (functionValue forbids `"`)
        loop {
            self.skip_ws();
            if self.i < self.s.len() && self.s[self.i] == b'"' {
                self.i += 1;
                let p0 = self.i;
                while self.i < self.s.len() && self.s[self.i] != b'"' {
                    self.i += 1;
                }
                let param = String::from_utf8_lossy(&self.s[p0..self.i]).into_owned();
                if self.i < self.s.len() {
                    self.i += 1; // closing quote
                }
                params.push(param);
            } else {
                break;
            }
        }
        if params.is_empty() {
            // Not a valid function (no params): bail so the caller stops.
            return None;
        }
        // HS: f++" \""++intercalate "\" \"" param++"\""
        let mut s = String::with_capacity(name.len() + 8);
        s.push_str(&name);
        s.push_str(" \"");
        s.push_str(&params.join("\" \""));
        s.push('"');
        let leaf = SelectorExpr::Leaf(SelectorLeaf { name, params });
        Some((s, leaf))
    }
}

fn is_ident_byte(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_' || c == b'.'
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_renders_noise_unless() {
        let raw = "presort: s\n\
prio: {id}\n\
  regex\"^My\"\n\
  regex\"^I_\"\n\
prio: {id}\n\
  regex\"!KU\\(*~.*\\)\" & reasonableNoncesNoise\"resN\"\n\
prio: {smallest}\n\
  dhreNoise\"dh\"\n";
        let t = Tactic::parse("unless", raw);
        assert_eq!(t.presort, 's');
        assert_eq!(t.prios.len(), 3);
        let r = t.render();
        let expected = concat!(
            "tactic: unless\n",
            "presort: s\n",
            "prio: {id}\n",
            "  regex\"^My\"\n",
            "  regex\"^I_\"\n",
            "prio: {id}\n",
            "  regex\"!KU\\(*~.*\\)\" & reasonableNoncesNoise\"resN\"\n",
            "prio: {smallest}\n",
            "  dhreNoise\"dh\"",
        );
        assert_eq!(r, expected);
    }

    #[test]
    fn collapses_internal_regex_spaces_and_or_chain() {
        // LAK06-style: `|regex` with no trailing space, internal regex spaces.
        let raw = "presort: s\n\
prio:\n\
  regex \".*!K.\\( \\(.*~r0\\.1.*\" |regex \".*!K.\\( \\(.*~r0.*\" | regex \".*!K.\\( ~r.*\"\n";
        let t = Tactic::parse("helping", raw);
        assert_eq!(t.prios.len(), 1);
        assert_eq!(t.prios[0].ranking, "id");
        let r = t.render();
        assert!(
            r.contains("regex\".*!K.\\(\\(.*~r0\\.1.*\" | regex\".*!K.\\(\\(.*~r0.*\" | regex\".*!K.\\(~r.*\""),
            "got: {r}"
        );
    }

    #[test]
    fn prio_and_deprio() {
        let raw = "presort: s\n\
prio:\n\
  regex \".*!Tag\\(.*\"\n\
deprio:\n\
  regex \".*TagK\\(.*\"\n";
        let t = Tactic::parse("x", raw);
        assert_eq!(t.prios.len(), 1);
        assert_eq!(t.deprios.len(), 1);
        let r = t.render();
        assert_eq!(
            r,
            "tactic: x\npresort: s\nprio: {id}\n  regex\".*!Tag\\(.*\"\ndeprio: {id}\n  regex\".*TagK\\(.*\""
        );
    }
}
