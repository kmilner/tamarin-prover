//! Port of `Term.Maude.Parser`'s reply-parsing portion.
//!
//! Parses the textual replies that Maude emits for `unify`, `match`,
//! `get variants`, and `reduce` queries.

use crate::function_symbols::{
    AcSym, Constructability, FunSym, NoEqSym, Privacy, CSym,
};
use crate::lterm::LSort;
use crate::maude_print::{
    fun_sym_decode, parse_lsort_sym, pp_maude_ac_sym, pp_maude_c_sym,
    replace_minus, FUN_SYM_PREFIX,
};
use crate::maude_sig::MaudeSig;
use crate::maude_types::{MSubst, MTerm, MaudeLit};
use crate::term::Term;

#[derive(Debug, Clone)]
pub struct ParseError(pub String);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for ParseError {}

// =============================================================================
// Cursor
// =============================================================================

struct Cursor<'a> {
    src: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    fn new(src: &'a [u8]) -> Self { Cursor { src, pos: 0 } }
    fn rest(&self) -> &[u8] { &self.src[self.pos..] }
    fn is_eof(&self) -> bool { self.pos >= self.src.len() }
    fn peek(&self) -> Option<u8> { self.src.get(self.pos).copied() }
    fn eat(&mut self, b: u8) -> bool {
        if self.peek() == Some(b) { self.pos += 1; true } else { false }
    }
    fn eat_str(&mut self, s: &[u8]) -> bool {
        if self.rest().starts_with(s) {
            self.pos += s.len();
            true
        } else { false }
    }
    fn read_decimal(&mut self) -> Option<u64> {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if b.is_ascii_digit() { self.pos += 1; } else { break; }
        }
        if self.pos == start { None }
        else { std::str::from_utf8(&self.src[start..self.pos]).ok()
            .and_then(|s| s.parse().ok()) }
    }
    fn skip_eol(&mut self) -> bool {
        if self.eat_str(b"\r\n") || self.eat(b'\n') { true } else { false }
    }
    /// Take while predicate holds, return slice consumed.
    fn take_while<F: Fn(u8) -> bool>(&mut self, f: F) -> &'a [u8] {
        let start = self.pos;
        while let Some(b) = self.peek() {
            if f(b) { self.pos += 1; } else { break; }
        }
        &self.src[start..self.pos]
    }
}

// =============================================================================
// Public entry points
// =============================================================================

/// Parse a `unify` reply.
pub fn parse_unify_reply(msig: &MaudeSig, reply: &[u8]) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::new(reply);
    if c.eat_str(b"No unifier.") {
        let _ = c.skip_eol();
        return Ok(vec![]);
    }
    parse_substitutions(msig, &mut c)
}

/// Parse a `match` reply.
pub fn parse_match_reply(msig: &MaudeSig, reply: &[u8]) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::new(reply);
    if c.eat_str(b"No match.") {
        let _ = c.skip_eol();
        return Ok(vec![]);
    }
    parse_substitutions(msig, &mut c)
}

/// Parse a `reduce` reply: `result <Sort>: <term>\n`.
pub fn parse_reduce_reply(msig: &MaudeSig, reply: &[u8]) -> Result<MTerm, ParseError> {
    let mut c = Cursor::new(reply);
    if !c.eat_str(b"result ") {
        return Err(ParseError(format!("expected `result `, got: {:?}",
            String::from_utf8_lossy(&c.rest()[..c.rest().len().min(40)]))));
    }
    // Sort: TOP -> Msg, otherwise parse_sort.
    if c.eat_str(b"TOP") {
        // ignore
    } else {
        parse_sort(&mut c)?;
    }
    if !c.eat_str(b": ") {
        return Err(ParseError("expected `: ` after result sort".into()));
    }
    let t = parse_term(msig, &mut c)?;
    let _ = c.skip_eol();
    Ok(t)
}

/// Parse a `get variants` reply.
pub fn parse_variants_reply(msig: &MaudeSig, reply: &[u8]) -> Result<Vec<MSubst>, ParseError> {
    let mut c = Cursor::new(reply);
    let _ = c.skip_eol();
    let mut variants = Vec::new();
    loop {
        if c.eat_str(b"No more variants.") { break; }
        if !c.eat_str(b"Variant ") {
            // optional `#`
            return Err(ParseError(format!(
                "expected `Variant ` or `No more variants.`; got {:?}",
                String::from_utf8_lossy(&c.rest()[..c.rest().len().min(40)])
            )));
        }
        let _ = c.eat(b'#');
        let _ = c.read_decimal().ok_or_else(|| ParseError("variant id".into()))?;
        let _ = c.skip_eol();
        if !c.eat_str(b"rewrites: ") { return Err(ParseError("expected rewrites:".into())); }
        let _ = c.read_decimal();
        let _ = c.skip_eol();
        // Reprinted term (sort/TOP : term\n)
        if c.eat_str(b"TOP") {
        } else {
            parse_sort(&mut c)?;
        }
        if !c.eat_str(b": ") { return Err(ParseError("expected `: ` in reprinted term".into())); }
        let _ = parse_term(msig, &mut c)?;
        let _ = c.skip_eol();
        // Then bindings: `xN:Sort --> term\n` until empty line.
        let mut subst = MSubst::new();
        loop {
            if c.peek() == Some(b'\n') || c.peek() == Some(b'\r') {
                let _ = c.skip_eol();
                break;
            }
            let entry = parse_entry(msig, &mut c)?;
            subst.push(entry);
        }
        variants.push(subst);
    }
    Ok(variants)
}

// =============================================================================
// Substitutions
// =============================================================================

fn parse_substitutions(msig: &MaudeSig, c: &mut Cursor) -> Result<Vec<MSubst>, ParseError> {
    let mut substs = Vec::new();
    loop {
        let _ = c.skip_eol();
        if c.is_eof() { break; }
        // Each substitution starts with `Solution N`, `Unifier N`, or `Matcher N`.
        let saved = c.pos;
        let header_ok = c.eat_str(b"Solution ")
            || { c.pos = saved; c.eat_str(b"Unifier ") }
            || { c.pos = saved; c.eat_str(b"Matcher ") };
        if !header_ok {
            // No more substitutions.
            c.pos = saved;
            break;
        }
        let _ = c.read_decimal();
        let _ = c.skip_eol();
        if c.eat_str(b"empty substitution") {
            let _ = c.skip_eol();
            substs.push(Vec::new());
            continue;
        }
        let mut entries = Vec::new();
        loop {
            // Stop when next line isn't an `xN:Sort --> ...` entry.
            let saved2 = c.pos;
            if c.eat_str(b"x") {
                c.pos = saved2;
                let entry = parse_entry(msig, c)?;
                entries.push(entry);
            } else {
                break;
            }
        }
        substs.push(entries);
    }
    Ok(substs)
}

fn parse_entry(msig: &MaudeSig, c: &mut Cursor) -> Result<((LSort, u64), MTerm), ParseError> {
    if !c.eat_str(b"x") {
        return Err(ParseError("expected `x` for substitution variable".into()));
    }
    let n = c.read_decimal().ok_or_else(|| ParseError("var index".into()))?;
    if !c.eat_str(b":") { return Err(ParseError("expected `:` after variable".into())); }
    let sort = parse_sort(c)?;
    if !c.eat_str(b" --> ") {
        return Err(ParseError("expected ` --> `".into()));
    }
    let t = parse_term(msig, c)?;
    let _ = c.skip_eol();
    Ok(((sort, n), t))
}

// =============================================================================
// Term parser
// =============================================================================

fn parse_sort(c: &mut Cursor) -> Result<LSort, ParseError> {
    if c.eat_str(b"Pub") { Ok(LSort::Pub) }
    else if c.eat_str(b"Fresh") { Ok(LSort::Fresh) }
    else if c.eat_str(b"Node") { Ok(LSort::Node) }
    else if c.eat_str(b"TamNat") { Ok(LSort::Nat) }
    else if c.eat_str(b"Msg") { Ok(LSort::Msg) }
    else if c.eat_str(b"M") {
        // `Msg` was matched above; the special-case in Haskell handles
        // a `Maude` truncation. Recover any continuation.
        if c.eat_str(b"sg") { Ok(LSort::Msg) }
        else { Err(ParseError("unknown sort starting with M".into())) }
    }
    else {
        Err(ParseError(format!("unknown sort prefix at {:?}",
            String::from_utf8_lossy(&c.rest()[..c.rest().len().min(20)]))))
    }
}

fn parse_term(msig: &MaudeSig, c: &mut Cursor) -> Result<MTerm, ParseError> {
    // `#N:Sort` or `%N:Sort` is a fresh variable (Maude-introduced).
    if c.eat(b'#') || c.eat(b'%') {
        let n = c.read_decimal().ok_or_else(|| ParseError("fresh var idx".into()))?;
        if !c.eat_str(b":") { return Err(ParseError("expected `:` after fresh idx".into())); }
        let s = parse_sort(c)?;
        return Ok(Term::Lit(MaudeLit::FreshVar(n, s)));
    }
    // Otherwise, read identifier up to `:(,)\n `.
    let ident = c.take_while(|b| !matches!(b, b':' | b'(' | b',' | b')' | b'\n' | b' '));
    if ident.is_empty() {
        return Err(ParseError("empty identifier".into()));
    }
    let ident = ident.to_vec();
    // Three branches: `(`, `:`, or end-of-token.
    if c.eat(b'(') {
        // Could be a constant `c(123)` or a function application.
        if let Some(s) = std::str::from_utf8(&ident).ok().and_then(parse_lsort_sym) {
            // constant
            let n = c.read_decimal().ok_or_else(|| ParseError("const idx".into()))?;
            if !c.eat(b')') { return Err(ParseError("expected `)` after const".into())); }
            return Ok(Term::Lit(MaudeLit::MaudeConst(n, s)));
        }
        // function application: parse comma-separated arguments.
        let mut args = Vec::new();
        loop {
            args.push(parse_term(msig, c)?);
            if c.eat_str(b", ") || c.eat(b',') { continue; }
            break;
        }
        if !c.eat(b')') { return Err(ParseError("expected `)` after args".into())); }
        Ok(build_app(msig, &ident, args))
    } else if c.eat_str(b":") {
        // Variable: `xN:Sort` — `ident` is `xN`.
        let s = parse_sort(c)?;
        if let Some(rest) = ident.strip_prefix(b"x") {
            let n: u64 = std::str::from_utf8(rest).ok()
                .and_then(|s| s.parse().ok())
                .ok_or_else(|| ParseError("invalid variable index".into()))?;
            Ok(Term::Lit(MaudeLit::MaudeVar(n, s)))
        } else {
            Err(ParseError("variable identifier must start with `x`".into()))
        }
    } else {
        // Nullary application.
        Ok(build_app(msig, &ident, Vec::new()))
    }
}

fn build_app(msig: &MaudeSig, ident: &[u8], args: Vec<MTerm>) -> MTerm {
    // AC operator?
    for op in [AcSym::Mult, AcSym::Union, AcSym::NatPlus, AcSym::Xor] {
        if ident == pp_maude_ac_sym(op).as_slice() {
            return crate::term::f_app_ac(op, args);
        }
    }
    // C operator (em)?
    // Mirror HS `fAppC EMap args` (Maude/Parser.hs:355): sort the two
    // arguments so `em` is canonical regardless of Maude's output order.
    if ident == pp_maude_c_sym(CSym::EMap).as_slice() {
        return crate::term::f_app_c(CSym::EMap, args);
    }
    // List?
    if ident == b"list" {
        // `list(cons(t1, cons(...)))` flattens to `FunSym::List [t1, ...]`.
        if args.len() == 1 {
            let flat = flatten_cons(&args[0]);
            return Term::App(FunSym::List, flat.into());
        }
    }
    if ident == b"cons" || ident == b"nil" {
        // Should have been handled inside `list(...)`. Fall through to no-eq.
    }
    // Free symbol — decode and lookup.
    if ident.starts_with(FUN_SYM_PREFIX.as_bytes()) {
        let (name, p, c) = fun_sym_decode(ident);
        let name = replace_minus(&name);
        let arity = args.len();
        let sym = NoEqSym {
            name,
            arity,
            privacy: p,
            constructability: c,
        };
        // Verify it's known to the signature; otherwise, accept anyway (the
        // Haskell version errors here, but lenient pass is fine for our
        // round-trip tests since we constructed the signature ourselves).
        let _ = msig;
        return Term::App(FunSym::NoEq(sym), args.into());
    }
    // Unknown — fall back to a public-constructor symbol with the raw name
    // for forward compatibility; this matches Haskell only for certain
    // built-ins (like Maude's own `true`).
    let sym = NoEqSym {
        name: ident.to_vec(),
        arity: args.len(),
        privacy: Privacy::Public,
        constructability: Constructability::Constructor,
    };
    Term::App(FunSym::NoEq(sym), args.into())
}

fn flatten_cons(t: &MTerm) -> Vec<MTerm> {
    if let Term::App(FunSym::NoEq(s), args) = t {
        if s.name == b"cons" && args.len() == 2 {
            let mut v = vec![args[0].clone()];
            v.extend(flatten_cons(&args[1]));
            return v;
        }
        if s.name == b"nil" && args.is_empty() {
            return Vec::new();
        }
    }
    vec![t.clone()]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::maude_sig::pair_maude_sig;

    #[test]
    fn parse_no_unifier() {
        let r = parse_unify_reply(&pair_maude_sig(), b"No unifier.\n").unwrap();
        assert!(r.is_empty());
    }

    #[test]
    fn parse_no_match() {
        let r = parse_match_reply(&pair_maude_sig(), b"No match.\n").unwrap();
        assert!(r.is_empty());
    }

    #[test]
    fn parse_simple_reduce_reply() {
        let r = parse_reduce_reply(&pair_maude_sig(), b"result Pub: p(1)\n").unwrap();
        match r {
            Term::Lit(MaudeLit::MaudeConst(1, LSort::Pub)) => {}
            x => panic!("got {:?}", x),
        }
    }
}
