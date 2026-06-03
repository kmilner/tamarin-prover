//! Structured parser for the proof skeleton attached to a lemma.
//!
//! Port of HS `Theory.Text.Parser.Proof.proofSkeleton`
//! (lib/theory/src/Theory/Text/Parser/Proof.hs:98-115).  The HS grammar
//! is:
//!
//! ```text
//! proofSkeleton =
//!     solvedProof <|> finalProof <|> interProof
//!   where
//!     solvedProof = "SOLVED"
//!     finalProof  = "by" proofMethod
//!     interProof  = proofMethod ( ("case" ident proofSkeleton)*
//!                                 "next" ... "qed"  | proofSkeleton )
//!
//! proofMethod = "sorry"        | "simplify"
//!             | "solve" "(" goal ")"
//!             | "contradiction"| "induction"
//!             | "INVALIDATED"  | "UNFINISHABLE"
//! ```
//!
//! See [`crate::ast::ParsedProofTree`] / [`crate::ast::ParsedMethod`]
//! for the shape of the structured output.  Anything we can't
//! recognise structurally (rare proof-method tokens, unusual goal
//! formulas) is captured in `Other(text)` / `GoalSpec::Raw(text)` so
//! the replay walker can fall back to the auto-prover.

use crate::ast::{DisjAlt, Fact, GoalSpec, ParsedMethod, ParsedProofTree};
use crate::lexer::{is_ident_char, Lexer};

#[derive(Debug, Clone)]
pub struct ProofTreeParseError {
    pub line: u32,
    pub col: u32,
    pub msg: String,
}

impl std::fmt::Display for ProofTreeParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "proof-tree parse error at line {} col {}: {}",
            self.line, self.col, self.msg)
    }
}
impl std::error::Error for ProofTreeParseError {}

/// Parse the raw skeleton text into a [`ParsedProofTree`].  Returns
/// `Err` if the token stream doesn't conform to the HS grammar — the
/// caller (parser.rs `try_proof_skeleton`) downgrades the failure to
/// `tree: None` so the lemma is at least readable, and replay falls
/// back to auto-prover at the top.
pub fn parse_proof_tree(raw: &str) -> Result<ParsedProofTree, ProofTreeParseError> {
    let mut p = TreeParser { lx: Lexer::new(raw) };
    p.lx.skip_ws();
    let tree = p.proof_skeleton()?;
    p.lx.skip_ws();
    if !p.lx.is_eof() {
        // Trailing junk — likely the outer `qed` from a higher-level
        // case block.  HS proofSkeleton consumes proper `qed` inside
        // interProof; anything left is fine for our purposes (caller's
        // `read_until_next_top_level` already framed the input).  We
        // could be stricter, but let's tolerate trailing whitespace
        // and stray characters here.
    }
    Ok(tree)
}

struct TreeParser<'a> {
    lx: Lexer<'a>,
}

impl<'a> TreeParser<'a> {
    fn err(&self, msg: impl Into<String>) -> ProofTreeParseError {
        let (line, col) = self.lx.line_col();
        ProofTreeParseError { line, col, msg: msg.into() }
    }

    /// HS `proofSkeleton` (Proof.hs:98-115).
    fn proof_skeleton(&mut self) -> Result<ParsedProofTree, ProofTreeParseError> {
        self.lx.skip_ws();
        // solvedProof: `SOLVED`
        if self.try_kw("SOLVED") {
            return Ok(ParsedProofTree {
                method: ParsedMethod::SolvedLeaf,
                cases: Vec::new(),
            });
        }
        // finalProof: `by <proofMethod>`
        if self.try_kw("by") {
            let m = self.proof_method()?;
            return Ok(ParsedProofTree { method: m, cases: Vec::new() });
        }
        // interProof: <method> ( case-block | proofSkeleton )
        let m = self.proof_method()?;
        // Decide: do we have a case-block or just an inline subproof?
        // HS: `(sepBy oneCase "next" <* "qed") <|>
        //      ((return . (,) "") <$> proofSkeleton)`
        // `oneCase` starts with `case <ident>`, so if the next token
        // is `case`, we're in the case-block branch.  Otherwise:
        //   - if next token is a proof-skeleton starter, that's an
        //     inline single-child sub-proof (single case with name "").
        //   - else: this method is a leaf (e.g. `simplify` followed by
        //     nothing if the proof ended).  Tolerated by HS via the
        //     "" subproof branch returning whatever proofSkeleton
        //     succeeded with — but if proofSkeleton fails the whole
        //     parse fails.  We surface this as an unrecognised
        //     terminator by returning the method with no children.
        self.lx.skip_ws();
        if self.peek_kw("case") {
            let mut cases: Vec<(String, ParsedProofTree)> = Vec::new();
            // HS: sepBy oneCase "next" <* "qed"
            // First case (mandatory at least one):
            cases.push(self.one_case()?);
            while self.try_kw("next") {
                cases.push(self.one_case()?);
            }
            self.require_kw("qed")?;
            return Ok(ParsedProofTree { method: m, cases });
        }
        // Inline (single-child) subproof.  HS: `(return . (,) "") <$>
        // proofSkeleton`.  If a proof-skeleton starter follows, recurse;
        // otherwise return a leaf.
        if self.at_proof_starter() {
            let sub = self.proof_skeleton()?;
            return Ok(ParsedProofTree {
                method: m,
                cases: vec![("".to_string(), sub)],
            });
        }
        // Method is itself a leaf (rare for interProof but fine — e.g.
        // a single `simplify` at end-of-proof).
        Ok(ParsedProofTree { method: m, cases: Vec::new() })
    }

    /// HS `oneCase` (Proof.hs:115):
    ///   `(,) <$> ("case" *> identifier) <*> proofSkeleton`
    fn one_case(&mut self) -> Result<(String, ParsedProofTree), ProofTreeParseError> {
        self.require_kw("case")?;
        let name = self.identifier_extended()?;
        let sub = self.proof_skeleton()?;
        Ok((name, sub))
    }

    /// HS `proofMethod` (Proof.hs:76-85).
    fn proof_method(&mut self) -> Result<ParsedMethod, ProofTreeParseError> {
        self.lx.skip_ws();
        if self.try_kw("sorry") { return Ok(ParsedMethod::Sorry); }
        if self.try_kw("simplify") { return Ok(ParsedMethod::Simplify); }
        if self.try_kw("contradiction") { return Ok(ParsedMethod::Contradiction); }
        if self.try_kw("induction") { return Ok(ParsedMethod::Induction); }
        if self.try_kw("INVALIDATED") { return Ok(ParsedMethod::Invalidated); }
        if self.try_kw("UNFINISHABLE") { return Ok(ParsedMethod::Unfinishable); }
        if self.try_kw("SOLVED") { return Ok(ParsedMethod::SolvedLeaf); }
        if self.try_kw("solve") {
            // `solve( <goal-text> )`.  HS parses an inner `goal`; we
            // capture the parenthesised text verbatim and best-effort
            // structural parse it.
            self.require_punct("(")?;
            let inner = self.read_balanced_paren()?;
            // `read_balanced_paren` consumed the matching `)`.
            let spec = parse_goal_spec(&inner);
            return Ok(ParsedMethod::SolveGoal(spec));
        }
        // Unrecognised token — capture the next identifier-like word
        // so we can carry it through to `Other(...)`.
        let save = self.lx.pos();
        let mut word = String::new();
        while let Some(c) = self.lx.peek() {
            if c.is_whitespace() || c == '(' || c == ')' { break; }
            word.push(c);
            self.lx.bump();
        }
        if word.is_empty() {
            self.lx.set_pos(save);
            return Err(self.err("expected proof method"));
        }
        Ok(ParsedMethod::Other(word))
    }

    // -------- helpers --------

    /// Match a keyword with a word boundary.
    fn try_kw(&mut self, kw: &str) -> bool {
        self.lx.skip_ws();
        self.lx.try_symbol(kw)
    }

    fn peek_kw(&mut self, kw: &str) -> bool {
        self.lx.skip_ws();
        self.lx.peek_symbol(kw)
    }

    fn require_kw(&mut self, kw: &str) -> Result<(), ProofTreeParseError> {
        if self.try_kw(kw) { Ok(()) } else {
            Err(self.err(format!("expected `{}`", kw)))
        }
    }

    fn require_punct(&mut self, p: &str) -> Result<(), ProofTreeParseError> {
        self.lx.skip_ws();
        if self.lx.eat_str(p) { Ok(()) }
        else { Err(self.err(format!("expected `{}`", p))) }
    }

    /// Identifier with extended chars: HS's `identifier` accepts
    /// alphanum + `_` and emits names like `Server_ReceiveOTP_NewSession_case_1`.
    /// Case names may also include `-` (rare; we tolerate it).
    fn identifier_extended(&mut self) -> Result<String, ProofTreeParseError> {
        self.lx.skip_ws();
        let mut s = String::new();
        match self.lx.peek() {
            Some(c) if c.is_alphanumeric() || c == '_' => {
                s.push(c); self.lx.bump();
            }
            _ => return Err(self.err("expected identifier")),
        }
        while let Some(c) = self.lx.peek() {
            if is_ident_char(c) { s.push(c); self.lx.bump(); }
            else { break; }
        }
        self.lx.skip_ws();
        Ok(s)
    }

    /// Read raw text between an already-consumed `(` and its matching
    /// `)`, accounting for nested parens.  Returns the inner text
    /// (excluding the final `)` which is consumed).
    fn read_balanced_paren(&mut self) -> Result<String, ProofTreeParseError> {
        let mut s = String::new();
        let mut depth: i32 = 1;
        while depth > 0 {
            match self.lx.peek() {
                None => return Err(self.err("unterminated `(` in solve(...)")),
                Some('(') => {
                    s.push('('); self.lx.bump(); depth += 1;
                }
                Some(')') => {
                    depth -= 1;
                    if depth == 0 { self.lx.bump(); break; }
                    s.push(')'); self.lx.bump();
                }
                Some(c) => { s.push(c); self.lx.bump(); }
            }
        }
        Ok(s)
    }

    /// True iff a token immediately follows that can start a
    /// proofSkeleton.  Used to decide whether `interProof`'s
    /// "inline subproof" branch fires.
    fn at_proof_starter(&mut self) -> bool {
        self.lx.skip_ws();
        for kw in &[
            "sorry", "simplify", "contradiction", "induction",
            "solve", "by", "SOLVED", "INVALIDATED", "UNFINISHABLE",
        ] {
            if self.lx.peek_symbol(kw) { return true; }
        }
        false
    }
}

// =============================================================================
// Goal-spec parser
// =============================================================================

/// Best-effort parse of the text inside `solve( ... )`.  Mirrors HS
/// `goal` (Theory/Text/Parser/Proof.hs:38-72):
///
/// ```haskell
/// goal = asum
///   [ stSplitGoal, premiseGoal, actionGoal,
///     chainGoal, disjSplitGoal, eqSplitGoal ]
/// ```
///
/// We structurally recognise Action (`Fact(...) @ #t`), Premise
/// (`Fact(...) ▶<n> #t`), and Disj (`gf1 ∥ gf2 ∥ ...` — HS
/// `disjSplitGoal`, Proof.hs:61).  Chain / Subterm / Split go to
/// `GoalSpec::Raw` and the walker falls back.
pub fn parse_goal_spec(raw: &str) -> GoalSpec {
    let trimmed = raw.trim();
    let mut p = GoalParser { lx: Lexer::new(trimmed) };
    if let Some(spec) = p.try_action_or_premise() {
        return spec;
    }
    if let Some(spec) = try_disj_split(trimmed) {
        return spec;
    }
    GoalSpec::Raw(trimmed.to_string())
}

/// Try to split the goal-spec text on top-level `∥` (HS U+2225, the
/// disjunction-split separator).  Returns `GoalSpec::Disj { alts }` if
/// at least one `∥` appears at top-level (depth-0 of `()/[]/<>/{}`),
/// classifying each disjunct by its shape (`∀ / ∃ / NonQuant`).
///
/// Mirrors HS `disjSplitGoal = (DisjG . Disj) <$> sepBy1 guardedFormula
/// (symbol "∥")` (Theory/Text/Parser/Proof.hs:61).  HS parses each
/// disjunct as a full `Guarded` value — we capture only the shape so
/// we can match against an existing `Goal::Disj` in `sys.goals` at
/// replay time without rebuilding LVar identities.
fn try_disj_split(text: &str) -> Option<GoalSpec> {
    let parts = split_top_level_disj(text);
    if parts.len() < 2 {
        return None;
    }
    let alts: Vec<DisjAlt> = parts.iter().map(|p| classify_disj_alt(p)).collect();
    Some(GoalSpec::Disj { alts })
}

/// Split `s` at top-level `∥` characters (U+2225).  Ignores any `∥`
/// that lives inside a `()/[]/<>/{}` bracket pair.
fn split_top_level_disj(s: &str) -> Vec<String> {
    const SEP: char = '\u{2225}';
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut depth: i32 = 0;
    for c in s.chars() {
        match c {
            '(' | '[' | '{' => { depth += 1; cur.push(c); }
            ')' | ']' | '}' => { depth -= 1; cur.push(c); }
            // `<` / `>` are used for tuple syntax inside facts; we don't
            // need to bracket-track them here because the `∥` separator
            // never appears inside `<…>`.  Tracking them would break on
            // `#t1 < #t2` which is a TIMEPOINT-LESS atom, not a tuple.
            _ if c == SEP && depth == 0 => {
                out.push(std::mem::take(&mut cur));
            }
            _ => cur.push(c),
        }
    }
    out.push(cur);
    out
}

/// Classify the shape of one disj-alt — its top-level quantifier, if
/// any, plus the number of bound variables.  Strips any surrounding
/// `(...)` so `(∀ x y. …)` and `∀ x y. …` classify identically.
fn classify_disj_alt(raw: &str) -> DisjAlt {
    let trimmed = strip_outer_parens(raw.trim());
    // Look for a leading `∀` (U+2200) or `∃` (U+2203) after stripping
    // any further whitespace.
    let t = trimmed.trim_start();
    if let Some(rest) = t.strip_prefix('\u{2200}') {
        return DisjAlt::All { n_vars: count_quant_vars(rest) };
    }
    if let Some(rest) = t.strip_prefix('\u{2203}') {
        return DisjAlt::Ex { n_vars: count_quant_vars(rest) };
    }
    DisjAlt::NonQuant
}

/// Strip ONE balanced layer of outer parens.  `"(x ∨ y)"` → `"x ∨ y"`;
/// `"x ∨ y"` returns unchanged.  Only strips if the opening `(` at
/// position 0 matches a closing `)` at the very end of the string with
/// no intermediate depth-0 break.
fn strip_outer_parens(s: &str) -> &str {
    let bytes = s.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'(' || bytes[bytes.len()-1] != b')' {
        return s;
    }
    // Verify the opening `(` matches the FINAL `)` (no depth-drop in between).
    let mut depth: i32 = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    if i + c.len_utf8() == s.len() {
                        // The first `(` closes at the last char — safe to strip.
                        return &s[1..s.len()-1];
                    }
                    return s; // Closes early — not a wrapping pair.
                }
            }
            _ => {}
        }
    }
    s
}

/// Count the number of identifier-like variable names appearing after
/// a `∀` / `∃` and before the next `.`.  HS's quantifier list is
/// `\\forall x1 x2 … xN.` — we count whitespace-separated tokens that
/// look like identifiers (possibly with a leading `#` for nodevars or
/// `~` for fresh-name vars).  Stops at the first `.` (the
/// quantifier-body separator).
fn count_quant_vars(after_qua: &str) -> usize {
    let mut n = 0usize;
    let mut in_token = false;
    for c in after_qua.chars() {
        if c == '.' { break; }
        if c == '#' || c == '~' || c == '$' || c == '%' || is_ident_char(c) {
            if !in_token { n += 1; in_token = true; }
        } else {
            in_token = false;
        }
    }
    n
}

struct GoalParser<'a> {
    lx: Lexer<'a>,
}

impl<'a> GoalParser<'a> {
    /// Try to match `[!]Name( <args> ) @ #t`  or
    /// `[!]Name( <args> ) ▶<idx> #t`.
    fn try_action_or_premise(&mut self) -> Option<GoalSpec> {
        let save = self.lx.pos();
        // Optional `!` prefix for persistent facts.
        self.lx.skip_ws();
        let persistent = self.lx.eat_str("!");
        self.lx.skip_ws();
        // Fact name: starts with uppercase.
        let name = self.lx.identifier()?;
        if !name.chars().next().map_or(false, |c| c.is_ascii_uppercase()) {
            self.lx.set_pos(save);
            return None;
        }
        self.lx.skip_ws();
        if !self.lx.eat_str("(") {
            self.lx.set_pos(save);
            return None;
        }
        // Read args text, balanced — we don't need to deeply parse the
        // terms here, but capture them as `crate::ast::Term::Var` from
        // raw text so the Fact struct is well-formed.
        let args_text = self.read_balanced_paren().ok()?;
        // After the `)`, expect `@` (action) or `▶<digit>` (premise).
        self.lx.skip_ws();
        if self.lx.eat_str("@") {
            self.lx.skip_ws();
            // Time variable: `#name[.idx]`.
            let _hash = self.lx.eat_str("#");
            let tvar = match self.lx.identifier() {
                Some(s) => s,
                None => { self.lx.set_pos(save); return None; }
            };
            // Skip `.idx` if present (we only care about the base name
            // for goal matching at replay time — the System's goal
            // term will have its own indices).
            if self.lx.eat_str(".") {
                let _ = self.lx.natural();
            }
            return Some(GoalSpec::Action {
                fact: build_fact(persistent, name, &args_text),
                time_var: tvar,
            });
        }
        // Premise marker: `▶<digit>` — UTF-8 ▶ is `\u{25B6}`, the
        // subscript digit follows.
        if self.lx.rest().starts_with('\u{25B6}') {
            // consume the ▶
            for _ in '\u{25B6}'.to_string().chars() { self.lx.bump(); }
            let idx_val = match self.lx.natural_subscript() {
                Some(n) => n,
                None => {
                    // Fallback: some tools render `▶0` with ASCII digits.
                    self.lx.skip_ws();
                    self.lx.natural()?
                }
            };
            self.lx.skip_ws();
            let _hash = self.lx.eat_str("#");
            let tvar = match self.lx.identifier() {
                Some(s) => s,
                None => { self.lx.set_pos(save); return None; }
            };
            if self.lx.eat_str(".") {
                let _ = self.lx.natural();
            }
            return Some(GoalSpec::Premise {
                fact: build_fact(persistent, name, &args_text),
                prem_idx: idx_val as usize,
                time_var: tvar,
            });
        }
        self.lx.set_pos(save);
        None
    }

    fn read_balanced_paren(&mut self) -> Result<String, ()> {
        let mut s = String::new();
        let mut depth: i32 = 1;
        while depth > 0 {
            match self.lx.peek() {
                None => return Err(()),
                Some('(') => { s.push('('); self.lx.bump(); depth += 1; }
                Some(')') => {
                    depth -= 1;
                    if depth == 0 { self.lx.bump(); break; }
                    s.push(')'); self.lx.bump();
                }
                Some(c) => { s.push(c); self.lx.bump(); }
            }
        }
        Ok(s)
    }
}

/// Build a `Fact` from name + raw args text.  We don't fully parse the
/// argument terms — that's used only for diagnostics today.  The
/// arity (number of commas at top level) is the load-bearing field for
/// goal matching (matches the count of terms in the runtime LNFact).
fn build_fact(persistent: bool, name: String, args_text: &str) -> Fact {
    use crate::ast::Term;
    let trimmed = args_text.trim();
    let args: Vec<Term> = if trimmed.is_empty() {
        Vec::new()
    } else {
        split_top_level_commas(trimmed)
            .into_iter()
            .map(|s| Term::Var(crate::ast::VarSpec {
                name: s.trim().to_string(),
                idx: 0,
                sort: crate::ast::SortHint::Untagged,
                typ: None,
            }))
            .collect()
    };
    Fact { persistent, name, args, annotations: Vec::new() }
}

/// Split a string at top-level commas — ignores commas inside any kind
/// of bracket (`()`, `<>`, `[]`, `{}`).
fn split_top_level_commas(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut depth: i32 = 0;
    for c in s.chars() {
        match c {
            '(' | '<' | '[' | '{' => { depth += 1; cur.push(c); }
            ')' | '>' | ']' | '}' => { depth -= 1; cur.push(c); }
            ',' if depth == 0 => { out.push(cur.clone()); cur.clear(); }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() { out.push(cur); }
    out
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leaf_by_sorry() {
        let t = parse_proof_tree("by sorry").expect("parse");
        assert_eq!(t.method, ParsedMethod::Sorry);
        assert!(t.cases.is_empty());
    }

    #[test]
    fn leaf_by_contradiction() {
        let t = parse_proof_tree("by contradiction").expect("parse");
        assert_eq!(t.method, ParsedMethod::Contradiction);
    }

    #[test]
    fn solved_leaf() {
        let t = parse_proof_tree("SOLVED").expect("parse");
        assert_eq!(t.method, ParsedMethod::SolvedLeaf);
    }

    #[test]
    fn induction_with_case_block() {
        let src = "
            induction
            case empty_trace
            by contradiction
            next
            case non_empty_trace
            by sorry
            qed
        ";
        let t = parse_proof_tree(src).expect("parse");
        assert_eq!(t.method, ParsedMethod::Induction);
        assert_eq!(t.cases.len(), 2);
        assert_eq!(t.cases[0].0, "empty_trace");
        assert_eq!(t.cases[0].1.method, ParsedMethod::Contradiction);
        assert_eq!(t.cases[1].0, "non_empty_trace");
        assert_eq!(t.cases[1].1.method, ParsedMethod::Sorry);
    }

    #[test]
    fn solve_action_goal() {
        let src = "solve( Foo( x ) @ #i )";
        let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Action { fact, time_var }) => {
                assert_eq!(fact.name, "Foo");
                assert_eq!(fact.args.len(), 1);
                assert_eq!(time_var, "i");
            }
            other => panic!("expected Action solve goal, got {:?}", other),
        }
        assert_eq!(t.cases.len(), 1);
        assert_eq!(t.cases[0].0, "");
        assert_eq!(t.cases[0].1.method, ParsedMethod::Sorry);
    }

    #[test]
    fn solve_premise_goal_subscript() {
        // ▶₀ (subscript 0)
        let src = "solve( Server( pid, sid, otc ) \u{25B6}\u{2080} #t1 )";
        let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Premise { fact, prem_idx, time_var }) => {
                assert_eq!(fact.name, "Server");
                assert_eq!(*prem_idx, 0);
                assert_eq!(time_var, "t1");
            }
            other => panic!("expected Premise solve goal, got {:?}", other),
        }
    }

    #[test]
    fn solve_persistent_premise() {
        // !F_Fact(...) ▶₂ #i
        let src = "solve( !F_OutSessKeys( a, b ) \u{25B6}\u{2082} #i )";
        let t = parse_proof_tree(&format!("{} by sorry", src)).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Premise { fact, prem_idx, .. }) => {
                assert!(fact.persistent);
                assert_eq!(fact.name, "F_OutSessKeys");
                assert_eq!(*prem_idx, 2);
            }
            other => panic!("expected persistent premise, got {:?}", other),
        }
    }

    #[test]
    fn nested_case_block() {
        let src = "
            solve( Foo( a ) @ #i )
              case case_1
              solve( Bar( b ) @ #j )
                case case_a
                by sorry
              next
                case case_b
                by contradiction
              qed
            next
              case case_2
              by sorry
            qed
        ";
        let t = parse_proof_tree(src).expect("parse");
        assert!(matches!(t.method, ParsedMethod::SolveGoal(_)));
        assert_eq!(t.cases.len(), 2);
        assert_eq!(t.cases[0].0, "case_1");
        assert_eq!(t.cases[0].1.cases.len(), 2);
        assert_eq!(t.cases[0].1.cases[0].0, "case_a");
        assert_eq!(t.cases[0].1.cases[1].0, "case_b");
        assert_eq!(t.cases[1].0, "case_2");
    }

    #[test]
    fn raw_goalspec_fallback() {
        // Subterm goals (`a ⊏ b`) — not handled yet, should fall back
        // to GoalSpec::Raw.  Use a single non-disjunctive token.
        let src = "solve( a \u{228F} b ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Raw(_)) => {}
            other => panic!("expected Raw goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_disj_two_alts() {
        // `solve( (last(#t1))  ∥ (#t1 < #t2) )` — two non-quant alts.
        let src = "solve( (last(#t1)) \u{2225} (#t1 < #t2) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Disj { alts }) => {
                assert_eq!(alts.len(), 2);
                assert!(matches!(alts[0], DisjAlt::NonQuant));
                assert!(matches!(alts[1], DisjAlt::NonQuant));
            }
            other => panic!("expected Disj goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_disj_quantified_alts() {
        // Yubikey slightly_weaker_invariant first solve(...) — 2 alts:
        // ∀-quantified with 7 vars, ∃-quantified with 5 vars.
        let src = "solve( (\u{2200} pid otc1 tc1 otc2 tc2 #t1 #t2. \
                          (last(#t1)) \u{2228} (last(#t2))) \u{2225} \
                          (\u{2203} #t1 #t2 a b c. (last(#t1))) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Disj { alts }) => {
                assert_eq!(alts.len(), 2);
                assert_eq!(alts[0], DisjAlt::All { n_vars: 7 });
                assert_eq!(alts[1], DisjAlt::Ex { n_vars: 5 });
            }
            other => panic!("expected Disj goal-spec, got {:?}", other),
        }
    }

    #[test]
    fn solve_disj_five_alts() {
        // Yubikey slightly_weaker_invariant inner solve — 5 non-quant alts.
        let src = "solve( (last(#t2)) \u{2225} (last(#t1)) \u{2225} \
                          ((#t1 < #t2) \u{2227} (last(#t3))) \u{2225} \
                          (#t2 < #t1) \u{2225} (#t1 = #t2) ) by sorry";
        let t = parse_proof_tree(src).expect("parse");
        match &t.method {
            ParsedMethod::SolveGoal(GoalSpec::Disj { alts }) => {
                assert_eq!(alts.len(), 5);
                for a in alts.iter() { assert!(matches!(a, DisjAlt::NonQuant)); }
            }
            other => panic!("expected Disj goal-spec, got {:?}", other),
        }
    }
}
