//! Pretty-printer for `tamarin_parser::ast::Formula` /
//! `tamarin_theory::guarded::Guarded`.
//!
//! Ports of Haskell `prettyLNFormula`/`prettyGuarded` from
//! `lib/theory/src/Theory/Model/Formula.hs:511` and
//! `lib/theory/src/Theory/Constraint/System/Guarded.hs:822`.
//!
//! Output uses Tamarin's interactive UI math glyphs:
//!   `∀`, `∃`, `⇒`, `∧`, `∨`, `¬`, `⊤`, `⊥`, `@`, `<`, `=`, `⊏`,
//!   `last(...)`.
//!
//! Term arguments inside facts/atoms come from
//! `tamarin_parser::ast::Term`.  We render those locally rather than
//! pulling in `tamarin-term::pretty::pretty_lnterm` because the parser
//! AST and the post-elaboration `LNTerm` are different types.

use tamarin_parser::ast as p;

use crate::guarded::{Guarded, Quant};

/// Pretty-print a parser-AST formula.  Mirrors Haskell's
/// `prettyLNFormula` (Formula.hs:511).
pub fn pretty_formula(f: &p::Formula) -> String {
    let mut s = String::new();
    pp_formula(f, FormCtx::Top, &[], &mut s);
    s
}

/// Pretty-print a formula with HS-style `sep`/`nest`-driven line
/// wrapping.  `indent` is the column where the first character of the
/// formula will land in the final output; `width` is the (legacy)
/// target line width.
///
/// HS's `Text.PrettyPrint.HughesPJ` decides "does flat fit on this
/// line" via `fits ((w `min` r) - sl) p` (HughesPJ.hs:873), where
///   - `w = lineLength` (Main/Console.hs:236, `lineWidth = 110`),
///   - `r = ribbonLength = round(lineLength / ribbonsPerLine) = 73`
///     (HughesPJ.hs:1010, `defaultStyle.ribbonsPerLine = 1.5`,
///     HughesPJ.hs:940),
///   - `sl` = chars already laid down on the current output line.
/// I.e. a doc of flat length N fits at current column C on a line that
/// began at column L iff `C + N <= min(lineLength, L + ribbon)`.
///
/// This function threads `line_start` (= L) through recursive calls so
/// the fit budget matches HS's behavior on every line.  Top-level entry
/// assumes `line_start = 0` (formula begins on a fresh output line).
pub fn pretty_formula_wrapped(f: &p::Formula, indent: usize, width: usize) -> String {
    // Top-level callers do not yet pass line_start; assume the formula
    // begins on a fresh output line (line_start = 0).  This is correct
    // for the lemma-body call (formula at col 3 on a line that opens
    // with `  "`, i.e. starts at col 0).
    pp_formula_wrap(
        f,
        indent,
        /*line_start=*/0,
        /*eff_w=*/LINE_LENGTH,
        width,
        &[],
        false,
    )
}

/// Pretty-print a guarded formula.  Mirrors Haskell's
/// `prettyGuarded` (Guarded.hs:822).
pub fn pretty_guarded(g: &Guarded) -> String {
    let mut s = String::new();
    pp_guarded(g, &mut s);
    s
}

/// Pretty-print a guarded formula with HS-style `sep`/`nest`-driven
/// line wrapping.  `indent` is the column where the first character of
/// the formula will land in the final output; `width` is the target
/// line width.  Mirrors Haskell's `prettyGuarded` (Guarded.hs:822-864)
/// composed with the HughesPJ `sep`/`nest` layout semantics.
///
/// When the flat rendering fits within `width - indent`, returns that.
/// Otherwise decomposes at the top-level operator following HS's
/// `sep [quantifier, sep [dante, connective, dsucc]]` layout.
pub fn pretty_guarded_wrapped(g: &Guarded, indent: usize, width: usize) -> String {
    // Top-level call: assume the formula begins on a fresh output
    // line (line_start = 0).
    pp_guarded_inner_wrapped(g, false, indent, /*line_start=*/0, width, &[])
}

/// Pretty-print an atom standalone (e.g. inside a goal label).
pub fn pretty_atom(a: &p::Atom) -> String {
    let mut s = String::new();
    pp_atom(a, &[], &mut s);
    s
}

/// Pretty-print a parser-AST term standalone.
pub fn pretty_term(t: &p::Term) -> String {
    let mut s = String::new();
    pp_term(t, TermPrec::Top, &[], &mut s);
    s
}

/// Pretty-print a fact `F(a,b,...)`.
pub fn pretty_fact(fa: &p::Fact) -> String {
    let mut s = String::new();
    pp_fact(fa, &[], &mut s);
    s
}

// =============================================================================
// Formula (parser AST)
// =============================================================================

#[derive(Copy, Clone, PartialEq, Eq)]
#[allow(dead_code)]
enum FormCtx {
    Top,
    /// Inside a connective requiring parens for nested connectives.
    /// Kept for back-compat; current renderer uses HS-faithful
    /// `opParens` instead.
    Conn,
}

/// `scope` is a flat list of bound var names→sort (innermost binder
/// last).  When a body occurrence has no explicit sort hint, we look
/// it up here so `Ex #i. A(k) @ i` renders the inner `i` as `#i`.
fn pp_formula(f: &p::Formula, _ctx: FormCtx, scope: &[(String, p::SortHint)], out: &mut String) {
    use p::Formula::*;
    match f {
        True => out.push('\u{22A4}'),  // ⊤
        False => out.push('\u{22A5}'), // ⊥
        Atom(a) => pp_atom(a, scope, out),
        Not(p_) => {
            // HS `prettyLFormula` Not case: `¬<opParens p>` — wraps in
            // parens if the operand is non-atomic.
            out.push('\u{00AC}'); // ¬
            pp_formula_opparens(p_, scope, out);
        }
        And(l, r) => pp_binop(l, r, " \u{2227} ", scope, out),
        Or(l, r) => pp_binop(l, r, " \u{2228} ", scope, out),
        Implies(l, r) => pp_binop(l, r, " \u{21D2} ", scope, out),
        Iff(l, r) => pp_binop(l, r, " \u{21D4} ", scope, out),
        Forall(vs, body) => {
            out.push('\u{2200}'); // ∀
            out.push(' ');
            pp_var_list(vs, out);
            out.push_str(". ");
            let new_scope = extend_scope(scope, vs);
            pp_formula(body, FormCtx::Top, &new_scope, out);
        }
        Exists(vs, body) => {
            out.push('\u{2203}'); // ∃
            out.push(' ');
            pp_var_list(vs, out);
            out.push_str(". ");
            let new_scope = extend_scope(scope, vs);
            pp_formula(body, FormCtx::Top, &new_scope, out);
        }
    }
}

/// HS `Conn` case: `sep [opParens p <-> op, opParens q]` — both sides
/// wrapped in `opParens`, then sep.
fn pp_binop(
    l: &p::Formula,
    r: &p::Formula,
    op: &str,
    scope: &[(String, p::SortHint)],
    out: &mut String,
) {
    pp_formula_opparens(l, scope, out);
    out.push_str(op);
    pp_formula_opparens(r, scope, out);
}

/// HS `opParens`: wraps the inner doc in parens iff non-atomic.  Our
/// atomicity check is structural: True/False/Pred-only atoms are
/// atomic, everything else is non-atomic.
fn pp_formula_opparens(
    f: &p::Formula,
    scope: &[(String, p::SortHint)],
    out: &mut String,
) {
    if is_atomic_formula(f) {
        pp_formula(f, FormCtx::Top, scope, out);
    } else {
        out.push('(');
        pp_formula(f, FormCtx::Top, scope, out);
        out.push(')');
    }
}

fn is_atomic_formula(f: &p::Formula) -> bool {
    use p::Formula::*;
    match f {
        True | False => true,
        Atom(p::Atom::Pred(_)) => true,
        _ => false,
    }
}

// =============================================================================
// HS-style wrapped layout
// =============================================================================
//
// Port of `Text.PrettyPrint.HughesPJ`'s `sep` / `nest` semantics for
// the subset used by `prettyLFormula` (Formula.hs:471-507) and
// `prettyLemma` (Lemma.hs:117-127):
//   - `sep [a, b]` tries to fit `a b` on one line; if it overflows the
//     ribbon width, falls back to `a\n  b` (each at the current indent).
//   - `nest n d` adds `n` to the current indent for `d`'s layout.
//
// We use a flat-then-wrap strategy: for each composite formula node,
// first render flat; if it fits in `(width - indent)`, keep flat;
// otherwise recursively lay out across lines.

/// HS ribbon width.  HS sets `lineWidth = 110` (`Main/Console.hs:236`)
/// and `defaultStyle.ribbonsPerLine = 1.5` (`HughesPJ.hs:940`), giving
/// `ribbonLen = round(110/1.5) = 73` (`HughesPJ.hs:1010`).
pub const RIBBON: usize = 73;

/// HS hard page width.  Mirrors `lineWidth = 110`
/// (`Main/Console.hs:236`).
pub const LINE_LENGTH: usize = 110;

/// Legacy alias kept for callers that pass a `width` argument; equal
/// to `RIBBON` (HS ribbon).  The actual fit-decision now uses
/// `fits_flat` (`line_start + RIBBON`-capped at `LINE_LENGTH`), not
/// this constant.
pub const WRAP_WIDTH: usize = RIBBON;

/// HS-faithful fit check.  Returns `true` iff a flat doc of length
/// `flat_len` whose first char would land at column `start_col`, on a
/// line that began at column `line_start`, with effective remaining
/// lineLength budget `eff_w`, would fit per HS HughesPJ
/// `fits ((w `min` r) - sl) p` (HughesPJ.hs:873).
///
/// HS's check: `sl + flat_len <= min(w, r)`, where
///   - `sl = start_col - line_start` (chars before the doc on the
///     current line, in the `get1` TextBeside chain),
///   - `w = eff_w` (HS's `w` at this point in the doc walk),
///   - `r = RIBBON`.
///
/// Equivalently: `end_col <= line_start + min(eff_w, RIBBON)`.
fn fits_flat(line_start: usize, start_col: usize, flat_len: usize, eff_w: usize) -> bool {
    let end_col = start_col + flat_len;
    let cap = line_start + std::cmp::min(eff_w, RIBBON);
    end_col <= cap
}

fn pp_formula_wrap(
    f: &p::Formula,
    indent: usize,
    line_start: usize,
    eff_w: usize,
    width: usize,
    scope: &[(String, p::SortHint)],
    inner_op: bool,
) -> String {
    let flat = {
        let mut s = String::new();
        if inner_op { pp_formula_opparens(f, scope, &mut s); }
        else { pp_formula(f, FormCtx::Top, scope, &mut s); }
        s
    };
    if !flat.contains('\n') && fits_flat(line_start, indent, flat.chars().count(), eff_w) {
        return flat;
    }
    use p::Formula::*;
    match f {
        // Quantifier: `Q vs. body` flat, or `Q vs.\n<body_indent>body`.
        // HS `sep [quant_vs., nest 1 body]` puts body at quant-col + 1.
        // When `inner_op` is true the whole quantifier gets wrapped in
        // parens — the `(` is at `indent` and the `∃` shifts right by
        // one, so the body indent must account for that.
        Forall(vs, body) | Exists(vs, body) => {
            let sym = if matches!(f, Forall(_, _)) { "\u{2200}" } else { "\u{2203}" };
            let mut vars_str = String::new();
            pp_var_list(vs, &mut vars_str);
            let head = format!("{} {}.", sym, vars_str);
            let new_scope = extend_scope(scope, vs);
            let quant_col = if inner_op { indent + 1 } else { indent };
            let body_indent = quant_col + 1;
            // Body lands on a fresh line at body_indent; its line_start
            // is body_indent.  eff_w passes through — RIBBON dominates
            // the budget.
            let body_str = pp_formula_wrap(body, body_indent, body_indent, eff_w, width, &new_scope, false);
            let mut out = head;
            out.push('\n');
            out.push_str(&" ".repeat(body_indent));
            out.push_str(&body_str);
            if inner_op { format!("({})", out) } else { out }
        }
        // Conn op p q: try `(p) op (q)` one line, else
        // `<p_layout> op\n<indent> <q_layout>`.
        And(l, r) => pp_binop_wrap(l, r, "\u{2227}", indent, line_start, eff_w, width, scope, inner_op),
        Or(l, r) => pp_binop_wrap(l, r, "\u{2228}", indent, line_start, eff_w, width, scope, inner_op),
        Implies(l, r) => pp_binop_wrap(l, r, "\u{21D2}", indent, line_start, eff_w, width, scope, inner_op),
        Iff(l, r) => pp_binop_wrap(l, r, "\u{21D4}", indent, line_start, eff_w, width, scope, inner_op),
        // Not p: HS Formula.hs:481-483
        //   pp (Not p) = return $ operator_ "¬" <> opParens p'
        // The `¬` and `opParens p'` are joined via `<>` (horizontal,
        // no-break) — `¬<inner>` is one atomic doc.  When this `¬…` is
        // a child of a binary connective (the `Conn` case, Formula.hs
        // line 489), HS wraps the WHOLE thing in `opParens` again,
        // giving `(¬<inner>)`.  Mirror by adding outer parens when the
        // caller passed `inner_op=true`.  The inner `<inner>` may itself
        // span multiple lines if its own pp_formula_wrap decides to
        // break (e.g. an Exists with a long body).
        Not(p_) => {
            // `¬` sits at the line's first non-whitespace col.  With
            // outer parens, `(` is at `indent` and `¬` shifts to
            // `indent+1`.
            let neg_col = if inner_op { indent + 1 } else { indent };
            // Inner lands on the SAME line as the `¬` — line_start and
            // eff_w pass through unchanged.
            let inner = pp_formula_wrap(p_, neg_col + 1, line_start, eff_w, width, scope, true);
            let body = format!("\u{00AC}{}", inner);
            if inner_op { format!("({})", body) } else { body }
        }
        // Atoms / True / False: just the flat form (no useful break).
        _ => flat,
    }
}

fn pp_binop_wrap(
    l: &p::Formula,
    r: &p::Formula,
    op: &str,
    indent: usize,
    line_start: usize,
    eff_w: usize,
    width: usize,
    scope: &[(String, p::SortHint)],
    outer_op: bool,
) -> String {
    // HS: `sep [opParens p <-> op, opParens q]`.  Lay out the left
    // operand, then ` op` (when one-line) or `\n<indent>op<sp>` then
    // the right operand at the same indent.
    //
    // When the binop itself is wrapped in `(...)` (the caller's
    // `opParens` / `outer_op=true`), the operands sit INSIDE the
    // parens — their effective column is `indent + 1`.  This is the
    // `sep` col for the inner punctuated list (matches HS's
    // `parens (sep ...)` layout: `(` at col `indent`, items at col
    // `indent+1`).
    let sep_col = if outer_op { indent + 1 } else { indent };
    // l lands on the SAME line as the caller's content (the `(` of
    // opParens, when outer_op, lands at `indent` on the caller's line).
    // So l's `line_start` is the caller's `line_start`, and eff_w
    // passes through.
    let l_str = pp_formula_wrap(l, sep_col, line_start, eff_w, width, scope, true);
    // r lands on a fresh line at `sep_col` when the binop wraps; its
    // line_start is `sep_col`.  When the binop stays flat, r is on the
    // same line as l (line_start unchanged) — but in the flat case the
    // r_str isn't read until after we've already verified flat fits.
    let r_str = pp_formula_wrap(r, sep_col, sep_col, eff_w, width, scope, true);
    // If `l op r` (one line) fits, use it.  HS-faithful: total end
    // column from the line's start must satisfy `fits_flat`.
    let one_line = format!("{} {} {}", l_str, op, r_str);
    if !l_str.contains('\n')
        && !r_str.contains('\n')
        && fits_flat(line_start, indent, one_line.chars().count(), eff_w)
    {
        return if outer_op { format!("({})", one_line) } else { one_line };
    }
    // Multi-line: `<l_str> op\n<sep_col><r_str>` — l carries the op on
    // its last line, then a newline + sep_col padding + r.
    let pad = " ".repeat(sep_col);
    let body = format!("{} {}\n{}{}", l_str, op, pad, r_str);
    if outer_op {
        // HS wraps the parenthesised group as `(<body>)` — keep on
        // the same multi-line shape; the closing paren attaches to the
        // last line of body.
        format!("({})", body)
    } else {
        body
    }
}

fn extend_scope(scope: &[(String, p::SortHint)], vs: &[p::VarSpec]) -> Vec<(String, p::SortHint)> {
    let mut s: Vec<(String, p::SortHint)> = scope.to_vec();
    for v in vs {
        s.push((v.name.clone(), v.sort));
    }
    s
}

fn resolved_sort(v: &p::VarSpec, scope: &[(String, p::SortHint)]) -> p::SortHint {
    if !matches!(v.sort, p::SortHint::Untagged) {
        return v.sort;
    }
    // Walk scope inner-most first.
    for (name, sort) in scope.iter().rev() {
        if name == &v.name {
            return *sort;
        }
    }
    v.sort
}

fn pp_var_list(vs: &[p::VarSpec], out: &mut String) {
    for (i, v) in vs.iter().enumerate() {
        if i > 0 { out.push(' '); }
        pp_var(v, out);
    }
}

fn pp_var(v: &p::VarSpec, out: &mut String) {
    out.push_str(sort_prefix_from_hint(v.sort));
    out.push_str(&v.name);
    if v.idx > 0 {
        out.push('.');
        out.push_str(&v.idx.to_string());
    }
}

/// Variant that resolves an unsorted occurrence against a binding scope.
fn pp_var_scoped(v: &p::VarSpec, scope: &[(String, p::SortHint)], out: &mut String) {
    let sort = resolved_sort(v, scope);
    out.push_str(sort_prefix_from_hint(sort));
    out.push_str(&v.name);
    if v.idx > 0 {
        out.push('.');
        out.push_str(&v.idx.to_string());
    }
}

fn sort_prefix_from_hint(s: p::SortHint) -> &'static str {
    use p::SortHint::*;
    use p::SuffixSort;
    match s {
        Pub => "$",
        Fresh => "~",
        Node => "#",
        Nat => "%",
        Suffix(SuffixSort::Pub) => "$",
        Suffix(SuffixSort::Fresh) => "~",
        Suffix(SuffixSort::Node) => "#",
        Suffix(SuffixSort::Nat) => "%",
        Suffix(SuffixSort::Msg) | Msg | Untagged => "",
    }
}

// =============================================================================
// Atom
// =============================================================================

fn pp_atom(a: &p::Atom, scope: &[(String, p::SortHint)], out: &mut String) {
    use p::Atom::*;
    match a {
        Eq(l, r) => {
            pp_term(l, TermPrec::Top, scope, out);
            out.push_str(" = ");
            pp_term(r, TermPrec::Top, scope, out);
        }
        Less(l, r) => {
            pp_term(l, TermPrec::Top, scope, out);
            out.push_str(" < ");
            pp_term(r, TermPrec::Top, scope, out);
        }
        LessMset(l, r) => {
            pp_term(l, TermPrec::Top, scope, out);
            out.push_str(" (<) ");
            pp_term(r, TermPrec::Top, scope, out);
        }
        Subterm(l, r) => {
            pp_term(l, TermPrec::Top, scope, out);
            out.push_str(" \u{228F} "); // ⊏
            pp_term(r, TermPrec::Top, scope, out);
        }
        Action(fa, t) => {
            pp_fact(fa, scope, out);
            out.push_str(" @ ");
            pp_term(t, TermPrec::Top, scope, out);
        }
        Last(t) => {
            out.push_str("last(");
            pp_term(t, TermPrec::Top, scope, out);
            out.push(')');
        }
        Pred(fa) => pp_fact(fa, scope, out),
    }
}

// =============================================================================
// Fact
// =============================================================================

fn pp_fact(fa: &p::Fact, scope: &[(String, p::SortHint)], out: &mut String) {
    // HS `prettyFact` uses `nestShort'` which renders as `Name( args )`
    // with single-space padding inside the parens, comma-separated args.
    // Empty-arg facts still keep the spacing.
    if fa.persistent { out.push('!'); }
    out.push_str(&fa.name);
    out.push_str("( ");
    for (i, t) in fa.args.iter().enumerate() {
        if i > 0 { out.push_str(", "); }
        pp_term(t, TermPrec::Top, scope, out);
    }
    out.push_str(" )");
}

// =============================================================================
// Term
// =============================================================================

#[derive(Copy, Clone, PartialEq, Eq)]
enum TermPrec {
    Top,
    /// Inside an AC operator — parenthesise nested binops with lower
    /// precedence than the parent.
    InOp,
}

fn pp_term(t: &p::Term, prec: TermPrec, scope: &[(String, p::SortHint)], out: &mut String) {
    use p::Term::*;
    match t {
        Var(v) => pp_var_scoped(v, scope, out),
        PubLit(s) => {
            out.push('\'');
            out.push_str(s);
            out.push('\'');
        }
        FreshLit(s) => {
            out.push('~');
            out.push('\'');
            out.push_str(s);
            out.push('\'');
        }
        NatLit(s) => {
            out.push('%');
            out.push('\'');
            out.push_str(s);
            out.push('\'');
        }
        Number(n) => out.push_str(&n.to_string()),
        NumberOne => out.push('1'),
        NatOne => out.push_str("%1"),
        DhNeutral => out.push_str("1:msg"),
        Pair(items) => {
            out.push('<');
            for (i, it) in items.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                pp_term(it, TermPrec::Top, scope, out);
            }
            out.push('>');
        }
        App(name, args) => {
            out.push_str(name);
            if !args.is_empty() {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 { out.push_str(", "); }
                    pp_term(a, TermPrec::Top, scope, out);
                }
                out.push(')');
            }
        }
        AlgApp(name, l, r) => {
            // HS pretty-prints `aenc{m}pk` as `aenc(m, pk)` (canonical
            // function syntax) — the curly-brace form is parser sugar.
            out.push_str(name);
            out.push('(');
            pp_term(l, TermPrec::Top, scope, out);
            out.push_str(", ");
            pp_term(r, TermPrec::Top, scope, out);
            out.push(')');
        }
        Diff(l, r) => {
            out.push_str("diff(");
            pp_term(l, TermPrec::Top, scope, out);
            out.push_str(", ");
            pp_term(r, TermPrec::Top, scope, out);
            out.push(')');
        }
        BinOp(op, l, r) => {
            // HS `prettyTerm` (Term/Term.hs:273-274):
            //   `FApp (AC o)   ts -> ppTerms (ppACOp o) 1 "(" ")" ts`
            //   `FApp (NoEq s) [t1,t2] | s == expSym -> ppTerm t1 <> text "^" <> ppTerm t2`
            // — AC ops always print with surrounding `(` `)` (the
            // `"("`/`")"` lead/finish in `ppTerms`); exp prints with
            // no precedence/paren guard.
            let is_exp = matches!(op, p::BinOp::Exp);
            if !is_exp { out.push('('); }
            // Within an exp, children print at Top (no extra parens for
            // nested `^`).  Within an AC, children at Top — AC nesting
            // already gets its own mandatory parens via the recursive
            // call, and the parent's parens are unconditional.
            pp_term(l, TermPrec::Top, scope, out);
            out.push_str(binop_symbol(*op));
            pp_term(r, TermPrec::Top, scope, out);
            if !is_exp { out.push(')'); }
            let _ = prec; // precedence no longer needed
        }
        PatMatch(inner) => {
            out.push('=');
            pp_term(inner, TermPrec::Top, scope, out);
        }
    }
}

fn binop_symbol(op: p::BinOp) -> &'static str {
    use p::BinOp::*;
    match op {
        Exp => "^",
        Mult => "*",
        Union => "++",
        Xor => "\u{2295}", // ⊕
        NatPlus => "%+",
    }
}

// =============================================================================
// Guarded
// =============================================================================

fn pp_guarded(g: &Guarded, out: &mut String) {
    pp_guarded_inner(g, false, &[], out);
}

/// Look up the binder for `Bound(n)` given a scope stack (outer-to-inner
/// order).  HS convention: `Bound 0` = innermost binder's last entry.
/// We map by walking the stack inner→outer and indexing each binder's
/// var list from the end.
fn lookup_bound<'a>(n: u32, scope: &'a [Vec<crate::guarded::GBinding>]) -> Option<&'a crate::guarded::GBinding> {
    let mut m = n as usize;
    for vars in scope.iter().rev() {
        if m < vars.len() {
            return Some(&vars[vars.len() - 1 - m]);
        }
        m -= vars.len();
    }
    None
}

/// `paren_atomic` controls whether non-atomic shapes (Disj/Conj with
/// multiple children, GGuarded) get wrapped in parens.  Mirrors
/// Haskell's `opParens` use inside `pp` (Guarded.hs:840-841).
fn pp_guarded_inner(
    g: &Guarded,
    paren_atomic: bool,
    scope: &[Vec<crate::guarded::GBinding>],
    out: &mut String,
) {
    use crate::guarded::GBinding;
    match g {
        Guarded::Atom(a) => {
            // HS `pp (GAto a) = prettyNAtom (bvarToLVar a)` (Guarded.hs
            // 829) — bare atom.  The caller's `opParens` wrap (used in
            // GConj/GDisj children, lines 834+841) is encoded as
            // `paren_atomic=true` here; emit `(<atom>)`.
            if paren_atomic { out.push('('); }
            pp_gatom(a, scope, out);
            if paren_atomic { out.push(')'); }
        }
        Guarded::Disj(xs) if xs.is_empty() => {
            // HS `pp (GDisj (Disj [])) = operator_ "⊥"` (Guarded.hs:831).
            // Caller's opParens still wraps to `(⊥)`.
            if paren_atomic { out.push('('); }
            out.push('\u{22A5}'); // ⊥
            if paren_atomic { out.push(')'); }
        }
        Guarded::Conj(xs) if xs.is_empty() => {
            // HS `pp (GConj (Conj [])) = operator_ "⊤"` (Guarded.hs:838).
            if paren_atomic { out.push('('); }
            out.push('\u{22A4}'); // ⊤
            if paren_atomic { out.push(')'); }
        }
        Guarded::Disj(xs) => {
            // HS Guarded.hs:833-835 — `parens $ sep $ punctuate ∨ ps`.
            // The outer `parens` ALWAYS wraps (independent of the
            // caller's `opParens`; the GDisj self-parenthesises).  A
            // caller's `opParens` would double-wrap, but HS's
            // `opParens . pp` for a GDisj also double-wraps — that's
            // HS's behaviour.  Reproduce it by always emitting `(...)`
            // here and letting the caller add its own `(...)` when
            // `paren_atomic`.
            if paren_atomic { out.push('('); }
            out.push('(');
            for (i, x) in xs.iter().enumerate() {
                if i > 0 { out.push_str(" \u{2228} "); } // ∨
                pp_guarded_inner(x, true, scope, out);
            }
            out.push(')');
            if paren_atomic { out.push(')'); }
        }
        Guarded::Conj(xs) => {
            // HS Guarded.hs:840-842 — `sep $ punctuate ∧ ps` (no outer
            // `parens` inside Conj itself).  When the caller applies
            // `opParens` (the `paren_atomic=true` path), wrap in `(...)`.
            // Single-conjunct degenerate case: `sep [opParens c]` = `(c)`,
            // so an outer opParens would produce `((c))` — that's HS's
            // literal behaviour; we match it for faithfulness.
            let needs = paren_atomic;
            if needs { out.push('('); }
            for (i, x) in xs.iter().enumerate() {
                if i > 0 { out.push_str(" \u{2227} "); } // ∧
                pp_guarded_inner(x, true, scope, out);
            }
            if needs { out.push(')'); }
        }
        Guarded::GGuarded { qua, vars, guards, body } => {
            let mut new_scope: Vec<Vec<GBinding>> = scope.to_vec();
            new_scope.push(vars.clone());
            // Special case: `∀[] [Atom].⊥` renders as `¬<dante>` where
            // `dante = pp (GConj (Conj antecedent))` and Conj wraps each
            // conjunct in `opParens` (Guarded.hs:856-857).  So single
            // guard `¬(a)`, multiple `¬((a) ∧ (b))` (outer Conj from
            // `pp`).
            if matches!(qua, Quant::All)
                && vars.is_empty()
                && body_is_false(body)
            {
                // HS Guarded.hs:856-857: `operator_ "¬" <> dante` —
                // `<>` is no-break horizontal concat.  The caller's
                // `opParens` (GConj/GDisj child position) adds outer
                // parens around the whole `¬<dante>`.
                if paren_atomic { out.push('('); }
                out.push('\u{00AC}'); // ¬
                // `dante = pp (GConj antecedent)` (Guarded.hs:852)
                // emits each guard atom wrapped via `opParens` (lines
                // 840-841) and joined by ` ∧ `.
                for (i, gd) in guards.iter().enumerate() {
                    if i > 0 { out.push_str(" \u{2227} "); }
                    out.push('(');
                    pp_gatom(gd, &new_scope, out);
                    out.push(')');
                }
                if paren_atomic { out.push(')'); }
                return;
            }
            // Quantifier line.
            if paren_atomic { out.push('('); }
            out.push(match qua {
                Quant::All => '\u{2200}', // ∀
                Quant::Ex => '\u{2203}',  // ∃
            });
            out.push(' ');
            pp_binding_list(vars, out);
            out.push_str(". ");
            // Antecedent (guards).
            if guards.is_empty() {
                // Just the body.
                pp_guarded_inner(body, false, &new_scope, out);
            } else {
                let connective = match qua {
                    Quant::All => " \u{21D2} ", // ⇒
                    Quant::Ex => " \u{2227} ",  // ∧
                };
                // Mirror HS: `dante = pp (GConj (Conj antecedent))` —
                // each guard atom is wrapped via `opParens`, then
                // joined with `∧`.  Single atom → `(atom)`; multiple
                // → `(a) ∧ (b)`.
                for (i, gd) in guards.iter().enumerate() {
                    if i > 0 { out.push_str(" \u{2227} "); }
                    out.push('(');
                    pp_gatom(gd, &new_scope, out);
                    out.push(')');
                }
                // Special case: existential with trivially-true body
                // renders as `∃ vs. (guards)` (Guarded.hs:854-855).
                if !(matches!(qua, Quant::Ex) && body_is_true(body)) {
                    out.push_str(connective);
                    // HS Guarded.hs:858-860: `dsucc <- nest 1 <$> pp gf`
                    // — the body is rendered BARE (no `opParens`); only
                    // the body's own pp may emit parens (e.g. GDisj
                    // self-wraps).  paren_atomic=false here.
                    pp_guarded_inner(body, false, &new_scope, out);
                }
            }
            if paren_atomic { out.push(')'); }
        }
    }
}

// =============================================================================
// HS-style wrapped layout for Guarded
// =============================================================================
//
// Port of `prettyGuarded` (Guarded.hs:822-864) composed with HughesPJ's
// `sep` / `nest` semantics.  Same flat-then-wrap strategy as
// `pp_formula_wrap`: render flat first, and if it overflows the ribbon
// width, decompose at the top-level operator.

/// Wrap-aware variant of `pp_guarded_inner`.  `indent` is the column
/// where the first character of the result will land in the final
/// output; `width` is the target line width.
fn pp_guarded_inner_wrapped(
    g: &Guarded,
    paren_atomic: bool,
    indent: usize,
    line_start: usize,
    width: usize,
    scope: &[Vec<crate::guarded::GBinding>],
) -> String {
    // Flat first.
    let flat = {
        let mut s = String::new();
        pp_guarded_inner(g, paren_atomic, scope, &mut s);
        s
    };
    // HS-faithful fit check: see `fits_flat`.
    if !flat.contains('\n')
        && fits_flat(line_start, indent, flat.chars().count(), LINE_LENGTH)
    {
        return flat;
    }
    // Legacy width check retained for compatibility with callers that
    // pass a tighter `width`.
    let _ = width;
    use crate::guarded::GBinding;
    match g {
        Guarded::Atom(_) => flat,
        Guarded::Disj(xs) if xs.is_empty() => flat,
        Guarded::Conj(xs) if xs.is_empty() => flat,

        Guarded::Disj(xs) => {
            // HS Guarded.hs:833-835: `parens . sep . punctuate ∨ [opParens c]`.
            // The Disj ALWAYS wraps itself in `(...)`.  When the caller
            // additionally requested `opParens` (paren_atomic=true),
            // there is an OUTER `(...)`.  Layout:
            //   <outer_paren?>(<c0> ∨
            //                  <c1> ∨
            //                  ...
            //                  <cn>)<outer_paren?>
            // sep_col = indent + 1 (inside the inner `(`) when no
            //           outer wrap, or indent + 2 when paren_atomic.
            let outer = paren_atomic;
            let inner_paren_col = if outer { indent + 1 } else { indent };
            let sep_col = inner_paren_col + 1;
            let mut out = String::new();
            if outer { out.push('('); }
            out.push('(');
            for (i, x) in xs.iter().enumerate() {
                // First item is on the SAME line as the opening `(`
                // (line_start unchanged); subsequent items are on
                // fresh lines at `sep_col` (line_start = sep_col).
                let child_line_start = if i == 0 { line_start } else { sep_col };
                if i > 0 {
                    out.push('\n');
                    out.push_str(&" ".repeat(sep_col));
                }
                // Each child is opParens'd (paren_atomic=true).
                let child = pp_guarded_inner_wrapped(x, true, sep_col, child_line_start, width, scope);
                out.push_str(&child);
                if i + 1 < xs.len() {
                    out.push_str(" \u{2228}"); // ∨ at end of each but last
                }
            }
            out.push(')');
            if outer { out.push(')'); }
            out
        }

        Guarded::Conj(xs) => {
            // HS Guarded.hs:840-842: `sep . punctuate ∧ [opParens c]`.
            // No self-wrap; caller's `opParens` (paren_atomic=true) adds
            // the outer `(...)`.  Layout:
            //   <paren?><c0> ∧
            //           <c1> ∧
            //           ...
            //           <cn><paren?>
            // sep_col = indent (no outer) or indent + 1 (outer).
            let outer = paren_atomic;
            let sep_col = if outer { indent + 1 } else { indent };
            let mut out = String::new();
            if outer { out.push('('); }
            for (i, x) in xs.iter().enumerate() {
                // First item: same line as `(` (line_start preserved).
                // Subsequent: fresh line at sep_col.
                let child_line_start = if i == 0 { line_start } else { sep_col };
                if i > 0 {
                    out.push('\n');
                    out.push_str(&" ".repeat(sep_col));
                }
                let child = pp_guarded_inner_wrapped(x, true, sep_col, child_line_start, width, scope);
                out.push_str(&child);
                if i + 1 < xs.len() {
                    out.push_str(" \u{2227}"); // ∧
                }
            }
            if outer { out.push(')'); }
            out
        }

        Guarded::GGuarded { qua, vars, guards, body } => {
            let mut new_scope: Vec<Vec<GBinding>> = scope.to_vec();
            new_scope.push(vars.clone());

            // Negation shortcut (HS Guarded.hs:856-857).  Flat only.
            if matches!(qua, Quant::All)
                && vars.is_empty()
                && body_is_false(body)
            {
                return flat;
            }
            // `∃ vs. (guards)` shortcut (HS Guarded.hs:854-855).
            // Try flat (the only sensible layout); if the guards
            // themselves are long, fall through to the generic path.
            if matches!(qua, Quant::Ex) && body_is_true(body) {
                return flat;
            }
            // Generic GGuarded: `sep [quantifier, sep [dante, conn, dsucc]]`.
            // Outer sep col = indent (or indent+1 if paren_atomic).
            // Inner sep col = same as outer sep col (because the inner
            // sep lands at the outer sep's col when the outer wraps).
            // With nest 1 on dante and dsucc:
            //   dante at sep_col + 1
            //   connective at sep_col
            //   dsucc at sep_col + 1
            let outer = paren_atomic;
            let sep_col = if outer { indent + 1 } else { indent };
            let body_col = sep_col + 1;

            // Quantifier line.
            let mut quantifier = String::new();
            quantifier.push(match qua {
                Quant::All => '\u{2200}',
                Quant::Ex => '\u{2203}',
            });
            quantifier.push(' ');
            pp_binding_list(vars, &mut quantifier);
            quantifier.push_str(".");

            // dante (antecedent): renders as `pp (GConj antecedent)` =
            // `sep [opParens (pp g) | g <- antecedent]`.  Each guard
            // becomes `(<atom>)`.  Try flat, then wrap if too long.
            let dante_flat = if guards.is_empty() {
                // `pp (GConj []) = ⊤` — but HS line 853-855 special-cases
                // `(Ex, _, GConj [])` and (negation).  For other cases
                // with empty antecedent, dante = `⊤` rendered.  In
                // practice the generic path is only entered with at
                // least one guard.  Defensive: render `⊤`.
                "\u{22A4}".to_string()
            } else {
                let mut s = String::new();
                for (i, gd) in guards.iter().enumerate() {
                    if i > 0 { s.push_str(" \u{2227} "); }
                    s.push('(');
                    pp_gatom(gd, &new_scope, &mut s);
                    s.push(')');
                }
                s
            };
            let dante_fits_flat = body_col + dante_flat.chars().count() <= width;
            let dante_str = if dante_fits_flat || guards.len() <= 1 {
                dante_flat
            } else {
                // Wrap dante across multiple lines.  `sep $ punctuate ∧
                // [(g) for g in guards]` — placed at body_col.
                let mut s = String::new();
                for (i, gd) in guards.iter().enumerate() {
                    if i > 0 {
                        s.push('\n');
                        s.push_str(&" ".repeat(body_col));
                    }
                    s.push('(');
                    pp_gatom(gd, &new_scope, &mut s);
                    s.push(')');
                    if i + 1 < guards.len() {
                        s.push_str(" \u{2227}");
                    }
                }
                s
            };

            let connective = match qua {
                Quant::All => "\u{21D2}", // ⇒
                Quant::Ex => "\u{2227}",  // ∧
            };

            // dsucc (body): rendered BARE (no opParens), per
            // Guarded.hs:858-860.  At body_col with width-budget.
            // dsucc lands on a fresh line at body_col (line_start =
            // body_col).
            let dsucc_str = pp_guarded_inner_wrapped(body, false, body_col, body_col, width, &new_scope);

            // Try the inner sep flat at body_col: `<dante> conn <dsucc>`
            // on one line.  HS `nest 1` (Guarded.hs:852, 859) on dante
            // and dsucc wraps the inner sep in `nest_ 1` via sep1's
            // `sep1 g (Nest n p) k ys = nest_ n (sep1 g p (k-n) ys)`
            // propagation (HughesPJ.hs:749).  At display, lay walks
            // `Nest 1 inner_sep` at line start → shifts the WHOLE
            // inner_sep by +1, so dante (and conn and dsucc) all land
            // at `sep_col + 1 = body_col`, not at sep_col.
            //
            // Scheme 2 layout (used when inner_sep fits as one line):
            //   <quantifier>
            //   <body_col><dante> <conn> <dsucc>
            //
            // Fit check uses the GGuarded's outer `line_start` (where
            // the OUTER sep's line began, before any local NilAbove).
            // HS's `nicest1 w r sl` at the inner_sep Union has `sl`
            // counting the line's get1-chain ink — which started from
            // the outer sep's line_start.
            let inner_flat_one_line =
                !dante_str.contains('\n')
                && !dsucc_str.contains('\n')
                && fits_flat(
                    line_start,
                    body_col,
                    dante_str.chars().count()
                        + 1 + connective.chars().count() + 1
                        + dsucc_str.chars().count(),
                    LINE_LENGTH,
                );

            let mut out = String::new();
            if outer { out.push('('); }
            out.push_str(&quantifier);
            out.push('\n');
            if inner_flat_one_line {
                // Scheme 2: quantifier on its own line; inner sep flat
                // at body_col (HS's `nest_ 1` shift).
                out.push_str(&" ".repeat(body_col));
                out.push_str(&dante_str);
                out.push(' ');
                out.push_str(connective);
                out.push(' ');
                out.push_str(&dsucc_str);
            } else {
                // Scheme 3: full vertical inner sep.
                out.push_str(&" ".repeat(body_col));
                out.push_str(&dante_str);
                out.push('\n');
                out.push_str(&" ".repeat(sep_col));
                out.push_str(connective);
                out.push('\n');
                out.push_str(&" ".repeat(body_col));
                out.push_str(&dsucc_str);
            }
            if outer { out.push(')'); }
            out
        }
    }
}

/// Pretty-print a binder list `[(name, sort)]`.
fn pp_binding_list(bs: &[crate::guarded::GBinding], out: &mut String) {
    for (i, b) in bs.iter().enumerate() {
        if i > 0 { out.push(' '); }
        out.push_str(sort_prefix_from_hint(b.sort));
        out.push_str(&b.name);
    }
}

fn pp_gatom(a: &crate::guarded::GAtom, scope: &[Vec<crate::guarded::GBinding>], out: &mut String) {
    use crate::guarded::GAtom;
    match a {
        GAtom::Eq(l, r) => {
            pp_gterm(l, TermPrec::Top, scope, out);
            out.push_str(" = ");
            pp_gterm(r, TermPrec::Top, scope, out);
        }
        GAtom::Less(l, r) => {
            pp_gterm(l, TermPrec::Top, scope, out);
            out.push_str(" < ");
            pp_gterm(r, TermPrec::Top, scope, out);
        }
        GAtom::LessMset(l, r) => {
            pp_gterm(l, TermPrec::Top, scope, out);
            out.push_str(" (<) ");
            pp_gterm(r, TermPrec::Top, scope, out);
        }
        GAtom::Subterm(l, r) => {
            pp_gterm(l, TermPrec::Top, scope, out);
            out.push_str(" \u{228F} "); // ⊏
            pp_gterm(r, TermPrec::Top, scope, out);
        }
        GAtom::Action(fa, t) => {
            pp_gfact(fa, scope, out);
            out.push_str(" @ ");
            pp_gterm(t, TermPrec::Top, scope, out);
        }
        GAtom::Last(t) => {
            out.push_str("last(");
            pp_gterm(t, TermPrec::Top, scope, out);
            out.push(')');
        }
        GAtom::Pred(fa) => pp_gfact(fa, scope, out),
    }
}

fn pp_gfact(fa: &crate::guarded::GFact, scope: &[Vec<crate::guarded::GBinding>], out: &mut String) {
    // HS-faithful: `Name( args )` with internal spaces, matching `pp_fact`.
    if fa.persistent { out.push('!'); }
    out.push_str(&fa.name);
    out.push_str("( ");
    for (i, t) in fa.args.iter().enumerate() {
        if i > 0 { out.push_str(", "); }
        pp_gterm(t, TermPrec::Top, scope, out);
    }
    out.push_str(" )");
}

fn pp_gterm(t: &crate::guarded::GTerm, prec: TermPrec, scope: &[Vec<crate::guarded::GBinding>], out: &mut String) {
    use crate::guarded::{GTerm, BVar};
    match t {
        GTerm::Var(BVar::Free(v)) => pp_var(v, out),
        GTerm::Var(BVar::Bound(n)) => {
            if let Some(b) = lookup_bound(*n, scope) {
                out.push_str(sort_prefix_from_hint(b.sort));
                out.push_str(&b.name);
            } else {
                // Free DeBruijn (shouldn't appear in a well-formed Guarded);
                // emit as `?n` for debug visibility.
                out.push('?');
                out.push_str(&n.to_string());
            }
        }
        GTerm::PubLit(s) => { out.push('\''); out.push_str(s); out.push('\''); }
        GTerm::FreshLit(s) => { out.push_str("~'"); out.push_str(s); out.push('\''); }
        GTerm::NatLit(s) => { out.push_str("%'"); out.push_str(s); out.push('\''); }
        GTerm::Number(n) => { out.push_str(&n.to_string()); }
        GTerm::NumberOne => out.push('1'),
        GTerm::NatOne => out.push_str("%1"),
        GTerm::DhNeutral => out.push('1'),
        GTerm::App(name, args) => {
            out.push_str(name);
            out.push('(');
            for (i, a) in args.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                pp_gterm(a, TermPrec::Top, scope, out);
            }
            out.push(')');
        }
        GTerm::AlgApp(name, a, b) => {
            out.push_str(name);
            out.push('{');
            pp_gterm(a, TermPrec::Top, scope, out);
            out.push('}');
            pp_gterm(b, TermPrec::Top, scope, out);
        }
        GTerm::Pair(items) => {
            out.push('<');
            for (i, it) in items.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                pp_gterm(it, TermPrec::Top, scope, out);
            }
            out.push('>');
        }
        GTerm::Diff(l, r) => {
            out.push_str("diff(");
            pp_gterm(l, TermPrec::Top, scope, out);
            out.push_str(", ");
            pp_gterm(r, TermPrec::Top, scope, out);
            out.push(')');
        }
        GTerm::BinOp(op, l, r) => {
            let needs = prec == TermPrec::InOp;
            if needs { out.push('('); }
            pp_gterm(l, TermPrec::InOp, scope, out);
            out.push_str(binop_symbol(*op));
            pp_gterm(r, TermPrec::InOp, scope, out);
            if needs { out.push(')'); }
        }
        GTerm::PatMatch(inner) => {
            out.push('=');
            pp_gterm(inner, TermPrec::Top, scope, out);
        }
    }
}

fn body_is_false(g: &Guarded) -> bool {
    matches!(g, Guarded::Disj(v) if v.is_empty())
}

fn body_is_true(g: &Guarded) -> bool {
    matches!(g, Guarded::Conj(v) if v.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(name: &str, sort: p::SortHint) -> p::VarSpec {
        p::VarSpec { name: name.into(), idx: 0, sort, typ: None }
    }

    #[test]
    fn trivial_formulas() {
        assert_eq!(pretty_formula(&p::Formula::True), "\u{22A4}");
        assert_eq!(pretty_formula(&p::Formula::False), "\u{22A5}");
    }

    #[test]
    fn forall_with_action() {
        // ∀ ni #i. F(ni)@#i ⇒ ⊥
        let fa = p::Fact {
            persistent: false,
            name: "F".into(),
            args: vec![p::Term::Var(v("ni", p::SortHint::Untagged))],
            annotations: vec![],
        };
        let body = p::Formula::Implies(
            Box::new(p::Formula::Atom(p::Atom::Action(
                fa, p::Term::Var(v("i", p::SortHint::Node))))),
            Box::new(p::Formula::False),
        );
        let f = p::Formula::Forall(
            vec![v("ni", p::SortHint::Untagged), v("i", p::SortHint::Node)],
            Box::new(body),
        );
        let s = pretty_formula(&f);
        assert!(s.contains("\u{2200}"));
        // HS-faithful: `Name( args )` with internal spaces.
        assert!(s.contains("F( ni )"));
        assert!(s.contains("@ #i"));
        assert!(s.contains("\u{21D2}"));
    }

    #[test]
    fn pair_term() {
        let t = p::Term::Pair(vec![
            p::Term::Var(v("a", p::SortHint::Untagged)),
            p::Term::Var(v("b", p::SortHint::Untagged)),
        ]);
        assert_eq!(pretty_term(&t), "<a, b>");
    }

    #[test]
    fn binop_xor() {
        let t = p::Term::BinOp(
            p::BinOp::Xor,
            Box::new(p::Term::Var(v("a", p::SortHint::Untagged))),
            Box::new(p::Term::Var(v("b", p::SortHint::Untagged))),
        );
        let s = pretty_term(&t);
        assert!(s.contains("\u{2295}"));
    }

    #[test]
    fn guarded_negation_shortcut() {
        // ∀ [] [Less(i,j)] ⊥  ⇒  rendered as `¬(i < j)`.
        let g = Guarded::GGuarded {
            qua: Quant::All,
            vars: vec![],
            guards: vec![crate::guarded::atom_to_gatom_free(&p::Atom::Less(
                p::Term::Var(v("i", p::SortHint::Node)),
                p::Term::Var(v("j", p::SortHint::Node)),
            ))],
            body: Box::new(Guarded::Disj(vec![])),
        };
        let s = pretty_guarded(&g);
        assert!(s.starts_with("\u{00AC}"));
        assert!(s.contains("#i < #j"));
    }
}
