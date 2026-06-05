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

/// Pretty-print a guarded formula.  Mirrors Haskell's
/// `prettyGuarded` (Guarded.hs:822).
pub fn pretty_guarded(g: &Guarded) -> String {
    let mut s = String::new();
    pp_guarded(g, &mut s);
    s
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
            let needs = prec == TermPrec::InOp;
            if needs { out.push('('); }
            pp_term(l, TermPrec::InOp, scope, out);
            out.push_str(binop_symbol(*op));
            pp_term(r, TermPrec::InOp, scope, out);
            if needs { out.push(')'); }
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
        Guarded::Atom(a) => pp_gatom(a, scope, out),
        Guarded::Disj(xs) if xs.is_empty() => out.push('\u{22A5}'), // ⊥
        Guarded::Conj(xs) if xs.is_empty() => out.push('\u{22A4}'), // ⊤
        Guarded::Disj(xs) => {
            if paren_atomic { out.push('('); }
            for (i, x) in xs.iter().enumerate() {
                if i > 0 { out.push_str(" \u{2228} "); } // ∨
                pp_guarded_inner(x, true, scope, out);
            }
            if paren_atomic { out.push(')'); }
        }
        Guarded::Conj(xs) => {
            let needs = paren_atomic && xs.len() > 1;
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
                out.push('\u{00AC}'); // ¬
                // Wrap each guard atom and join with ∧.
                for (i, gd) in guards.iter().enumerate() {
                    if i > 0 { out.push_str(" \u{2227} "); }
                    out.push('(');
                    pp_gatom(gd, &new_scope, out);
                    out.push(')');
                }
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
                    pp_guarded_inner(body, true, &new_scope, out);
                }
            }
            if paren_atomic { out.push(')'); }
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
