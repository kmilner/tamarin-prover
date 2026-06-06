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
use tamarin_utils::fresh::PreciseFreshState;

use crate::guarded::{Guarded, Quant};

/// A scope entry: the binder's source name + sort, plus the *display* name
/// used to render bound occurrences in the body.  HS-faithful: the display
/// name is allocated by `Precise.freshIdent` at binder-entry; if the source
/// name was already in scope (or in the free-var seed), the display name
/// receives a `.<idx>` suffix per HS `show LVar` (LTerm.hs:525-532).
///
/// Mirrors HS `LVar`'s role inside the `Precise.Fresh` monad used by
/// `prettyLNFormula` (Formula.hs:511) and `prettyGuarded`
/// (Guarded.hs:822-864).
type Bind = (String, p::SortHint, String);

/// Pretty-print a parser-AST formula.  Mirrors Haskell's
/// `prettyLNFormula` (Formula.hs:511-513):
///
///     prettyLNFormula fm =
///         Precise.evalFresh (prettyLFormula prettyNAtom fm) (avoidPrecise fm)
///
/// We seed the Precise fresh state with the formula's free-var names
/// (`avoidPrecise = avoidPreciseVars . frees`, LTerm.hs:672-680) and
/// run pp under that state — each `Forall`/`Exists` then does
/// `scopeFreshness` and allocates display names that respect both the
/// free-var seed and any outer-binder allocations.
pub fn pretty_formula(f: &p::Formula) -> String {
    let mut s = String::new();
    let mut state = avoid_precise_formula(f);
    pp_formula(f, FormCtx::Top, &[], &mut state, &mut s);
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
/// This routes through the HS-faithful Doc engine
/// (`crate::pretty_hpj`) so per-NilAbove `w`-shrinkage is tracked
/// (HS get1 NilAbove: `nilAbove_ (get (w - sl) p)`).
pub fn pretty_formula_wrapped(f: &p::Formula, indent: usize, _width: usize) -> String {
    use crate::pretty_hpj as hpj;
    // Build the formula's Doc tree, then render via the HS-faithful
    // engine.  `indent` is the column where the first text of the
    // formula will land; we model it as an initial `sl` to render_at.
    let mut state = avoid_precise_formula(f);
    let doc = formula_to_doc(f, &[], &mut state);
    doc.render_at(hpj::LINE_LENGTH, hpj::RIBBON, indent)
}

/// Pretty-print a guarded formula.  Mirrors Haskell's
/// `prettyGuarded` (Guarded.hs:822-826):
///
///     prettyGuarded fm =
///         Precise.evalFresh (pp fm) (avoidPrecise fm)
///
/// We seed the Precise fresh state with the guarded formula's free-var
/// names and run pp under that state — each `GGuarded` then does
/// `scopeFreshness` and allocates display names via `openGuarded`'s
/// `freshLVar` (Guarded.hs:362-371, LTerm.hs:295-296) which calls
/// `freshIdent` per name — producing `.<idx>` suffixes when the source
/// name is already in scope.
pub fn pretty_guarded(g: &Guarded) -> String {
    let mut s = String::new();
    let mut state = avoid_precise_guarded(g);
    pp_guarded(g, &mut state, &mut s);
    s
}

/// Pretty-print a guarded formula with HS-style `sep`/`nest`-driven
/// line wrapping.  `indent` is the column where the first character of
/// the formula will land in the final output; `width` is the target
/// line width.  Mirrors Haskell's `prettyGuarded` (Guarded.hs:822-864)
/// composed with the HughesPJ `sep`/`nest` layout semantics.
///
/// We use the legacy string-based path here rather than the Doc engine
/// because the original layout matches HS byte-exact on Tutorial and
/// the engine path needs further calibration to handle the `nest 1`
/// w-budget bookkeeping that HS uses for the 3-item inner sep here.
/// The Doc engine IS used for the formula-side wrap (which fixes the
/// wireguard 5-deep And case) via `pretty_formula_wrapped`.
pub fn pretty_guarded_wrapped(g: &Guarded, indent: usize, width: usize) -> String {
    let mut state = avoid_precise_guarded(g);
    pp_guarded_inner_wrapped(g, false, indent, /*line_start=*/0, width, &[], &mut state)
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
// Precise-Fresh state seeding (HS `avoidPrecise = avoidPreciseVars . frees`,
// LTerm.hs:672-680).  We seed `name -> maxIdx+1` for every free-var name
// occurring in the formula.  At each binder, `freshIdent name` returns the
// current value (default 0) and bumps; so a name seeded at `1` produces
// display `name.1`, matching HS `show LVar` (LTerm.hs:525-532).
// =============================================================================

/// Insert `name -> max(existing, idx+1)` into a Precise state map — mirrors
/// HS `avoidPreciseVars` `M'.insertWith max name (lvarIdx v + 1) m`
/// (LTerm.hs:672-675).
fn avoid_precise_insert(state: &mut PreciseFreshState, name: &str, idx: u64) {
    let want = idx + 1;
    if let Some(cur) = state.as_map().get(name).copied() {
        if cur >= want { return; }
    }
    // PreciseFreshState has no direct "set" API; emulate via scope rollback
    // would re-allocate, so do it through repeated fresh_ident until we hit
    // `want`.  Using the public API keeps internals encapsulated.
    let cur = state.as_map().get(name).copied().unwrap_or(0);
    for _ in cur..want {
        let _ = state.fresh_ident(name);
    }
}

/// Walk a parser-AST formula collecting free-var (name, idx) pairs into a
/// Precise state.  "Free" = used in an atom but not bound by an enclosing
/// `Forall`/`Exists` with the same name.  Matches HS `frees fm` semantics
/// for `LNFormula` — bound LVars are `BVar::Bound` and don't appear.
fn avoid_precise_formula(f: &p::Formula) -> PreciseFreshState {
    let mut state = PreciseFreshState::nothing_used();
    let mut bound: Vec<String> = Vec::new();
    collect_free_vars_formula(f, &mut bound, &mut state);
    state
}

fn collect_free_vars_formula(
    f: &p::Formula,
    bound: &mut Vec<String>,
    state: &mut PreciseFreshState,
) {
    use p::Formula::*;
    match f {
        True | False => {}
        Atom(a) => collect_free_vars_atom(a, bound, state),
        Not(p_) => collect_free_vars_formula(p_, bound, state),
        And(l, r) | Or(l, r) | Implies(l, r) | Iff(l, r) => {
            collect_free_vars_formula(l, bound, state);
            collect_free_vars_formula(r, bound, state);
        }
        Forall(vs, body) | Exists(vs, body) => {
            let saved_len = bound.len();
            for v in vs { bound.push(v.name.clone()); }
            collect_free_vars_formula(body, bound, state);
            bound.truncate(saved_len);
        }
    }
}

fn collect_free_vars_atom(a: &p::Atom, bound: &[String], state: &mut PreciseFreshState) {
    use p::Atom::*;
    match a {
        Eq(l, r) | Less(l, r) | LessMset(l, r) | Subterm(l, r) => {
            collect_free_vars_term(l, bound, state);
            collect_free_vars_term(r, bound, state);
        }
        Action(fa, t) => {
            for arg in &fa.args { collect_free_vars_term(arg, bound, state); }
            collect_free_vars_term(t, bound, state);
        }
        Last(t) => collect_free_vars_term(t, bound, state),
        Pred(fa) => {
            for arg in &fa.args { collect_free_vars_term(arg, bound, state); }
        }
    }
}

fn collect_free_vars_term(t: &p::Term, bound: &[String], state: &mut PreciseFreshState) {
    use p::Term::*;
    match t {
        Var(v) => {
            if !bound.iter().any(|n| n == &v.name) {
                avoid_precise_insert(state, &v.name, v.idx);
            }
        }
        PubLit(_) | FreshLit(_) | NatLit(_)
        | Number(_) | NumberOne | NatOne | DhNeutral => {}
        Pair(items) => for it in items { collect_free_vars_term(it, bound, state); },
        App(_, args) => for a in args { collect_free_vars_term(a, bound, state); },
        AlgApp(_, l, r) | Diff(l, r) | BinOp(_, l, r) => {
            collect_free_vars_term(l, bound, state);
            collect_free_vars_term(r, bound, state);
        }
        PatMatch(inner) => collect_free_vars_term(inner, bound, state),
    }
}

/// HS `avoidPrecise` on a Guarded formula: walks `Free` BVar leaves only
/// (Bound vars are positional, not named) and inserts (name, idx+1) into
/// the Precise state.  Mirrors HS `avoidPreciseVars . frees`.
fn avoid_precise_guarded(g: &Guarded) -> PreciseFreshState {
    use crate::guarded_types::{collect_free_atom};
    let mut state = PreciseFreshState::nothing_used();
    fn walk(g: &Guarded, state: &mut PreciseFreshState) {
        match g {
            Guarded::Atom(a) => {
                let mut frees = Vec::new();
                collect_free_atom(a, &mut frees);
                for v in frees { avoid_precise_insert(state, &v.name, v.idx); }
            }
            Guarded::Disj(xs) | Guarded::Conj(xs) =>
                for x in xs { walk(x, state); },
            Guarded::GGuarded { guards, body, .. } => {
                for a in guards {
                    let mut frees = Vec::new();
                    collect_free_atom(a, &mut frees);
                    for v in frees { avoid_precise_insert(state, &v.name, v.idx); }
                }
                walk(body, state);
            }
        }
    }
    walk(g, &mut state);
    state
}

/// Allocate display names for a list of binder vars (parser AST), mirroring
/// HS `openFormulaPrefix`'s loop of `freshLVar n s` calls
/// (Formula.hs:293-307, LTerm.hs:295-296).  Returns the new scope entries.
fn allocate_formula_binders(
    vs: &[p::VarSpec],
    scope: &[Bind],
    state: &mut PreciseFreshState,
) -> Vec<Bind> {
    let mut out: Vec<Bind> = scope.to_vec();
    for v in vs {
        // HS `freshLVar n s = LVar n s <$> freshIdent n`.
        let idx = state.fresh_ident(&v.name);
        // HS `show LVar` body: idx==0 → just name; else `name.idx`
        // (LTerm.hs:526-532).
        let display = if idx == 0 {
            v.name.clone()
        } else {
            format!("{}.{}", v.name, idx)
        };
        out.push((v.name.clone(), v.sort, display));
    }
    out
}

/// Allocate display names for a guarded binder (GBinding list), mirroring
/// HS `openGuarded`'s `mapM (\(n,s) -> freshLVar n s) vs`
/// (Guarded.hs:362-371).
fn allocate_guarded_binders(
    vs: &[crate::guarded::GBinding],
    scope: &[Vec<Bind>],
    state: &mut PreciseFreshState,
) -> Vec<Bind> {
    let _ = scope; // unused: each GGuarded pushes a fresh inner list.
    let mut out: Vec<Bind> = Vec::with_capacity(vs.len());
    for v in vs {
        let idx = state.fresh_ident(&v.name);
        let display = if idx == 0 {
            v.name.clone()
        } else {
            format!("{}.{}", v.name, idx)
        };
        out.push((v.name.clone(), v.sort, display));
    }
    out
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

/// `scope` is a flat list of binder entries (innermost binder last).
/// Each entry carries the binder's source name+sort plus the display
/// name allocated via `Precise.freshIdent` — when an inner binder
/// shadows an outer name, the inner display name carries a `.<idx>`
/// suffix (HS `show LVar`, LTerm.hs:526-532).
///
/// `state` threads the HS `Precise.Fresh` state across `scopeFreshness`
/// boundaries (Formula.hs:496-502 — every `Qua` saves/restores state).
fn pp_formula(
    f: &p::Formula,
    _ctx: FormCtx,
    scope: &[Bind],
    state: &mut PreciseFreshState,
    out: &mut String,
) {
    use p::Formula::*;
    match f {
        True => out.push('\u{22A4}'),  // ⊤
        False => out.push('\u{22A5}'), // ⊥
        Atom(a) => pp_atom(a, scope, out),
        Not(p_) => {
            // HS `prettyLFormula` Not case: `¬<opParens p>` — wraps in
            // parens if the operand is non-atomic.
            out.push('\u{00AC}'); // ¬
            pp_formula_opparens(p_, scope, state, out);
        }
        And(l, r) => pp_binop(l, r, " \u{2227} ", scope, state, out),
        Or(l, r) => pp_binop(l, r, " \u{2228} ", scope, state, out),
        Implies(l, r) => pp_binop(l, r, " \u{21D2} ", scope, state, out),
        Iff(l, r) => pp_binop(l, r, " \u{21D4} ", scope, state, out),
        Forall(vs, body) => pp_qua(true, vs, body, scope, state, out),
        Exists(vs, body) => pp_qua(false, vs, body, scope, state, out),
    }
}

/// HS `pp fm@(Qua _ _ _) = scopeFreshness $ do ...` (Formula.hs:496-502):
/// save Precise state, allocate display names for `vs`, render body,
/// restore state.
fn pp_qua(
    is_forall: bool,
    vs: &[p::VarSpec],
    body: &p::Formula,
    scope: &[Bind],
    state: &mut PreciseFreshState,
    out: &mut String,
) {
    state.scope_freshness(|state| {
        let new_scope = allocate_formula_binders(vs, scope, state);
        out.push(if is_forall { '\u{2200}' } else { '\u{2203}' });
        out.push(' ');
        // Render binder display names (post-allocation).
        for (i, b) in new_scope[scope.len()..].iter().enumerate() {
            if i > 0 { out.push(' '); }
            out.push_str(sort_prefix_from_hint(b.1));
            out.push_str(&b.2);
        }
        out.push_str(". ");
        pp_formula(body, FormCtx::Top, &new_scope, state, out);
    })
}

/// HS `Conn` case: `sep [opParens p <-> op, opParens q]` — both sides
/// wrapped in `opParens`, then sep.
fn pp_binop(
    l: &p::Formula,
    r: &p::Formula,
    op: &str,
    scope: &[Bind],
    state: &mut PreciseFreshState,
    out: &mut String,
) {
    pp_formula_opparens(l, scope, state, out);
    out.push_str(op);
    pp_formula_opparens(r, scope, state, out);
}

/// HS `opParens`: wraps the inner doc in parens iff non-atomic.  Our
/// atomicity check is structural: True/False/Pred-only atoms are
/// atomic, everything else is non-atomic.
fn pp_formula_opparens(
    f: &p::Formula,
    scope: &[Bind],
    state: &mut PreciseFreshState,
    out: &mut String,
) {
    if is_atomic_formula(f) {
        pp_formula(f, FormCtx::Top, scope, state, out);
    } else {
        out.push('(');
        pp_formula(f, FormCtx::Top, scope, state, out);
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
// HS-style wrapped layout — Doc-engine path
// =============================================================================
//
// Build a `pretty_hpj::Doc` tree mirroring HS's `prettyLFormula`
// (Formula.hs:471-507): Conn → `sep [opParens p <-> op, opParens q]`,
// Qua → `sep [quantifier, nest 1 body]`.  The Doc engine handles
// per-NilAbove `w`-shrinkage (HS get1 NilAbove:
// `nilAbove_ (get (w - sl) p)`) which is required for HS-byte-exact
// wireguard output (the deeply-nested And case).

/// HS `opParens p = "(" <> p <> ")"` (Highlight.hs:58-59) —
/// unconditional paren wrap.
fn doc_op_parens(d: crate::pretty_hpj::Doc) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::Doc;
    Doc::text("(").beside(d).beside(Doc::text(")"))
}

/// `text` helper.
fn doc_text<S: Into<String>>(s: S) -> crate::pretty_hpj::Doc {
    crate::pretty_hpj::Doc::text(s.into())
}

/// Mirror of `pp_formula` returning a Doc.  Atoms/terms/facts render
/// inline (their flat strings); only the formula-structural nodes
/// (Conn / Qua / Not) produce sep-Unions where wrap decisions happen.
fn formula_to_doc(
    f: &p::Formula,
    scope: &[Bind],
    state: &mut PreciseFreshState,
) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj as hpj;
    use p::Formula::*;
    match f {
        True => doc_text("\u{22A4}"),
        False => doc_text("\u{22A5}"),
        Atom(a) => {
            let mut s = String::new();
            pp_atom(a, scope, &mut s);
            doc_text(s)
        }
        Not(p_) => {
            // HS: `operator_ "¬" <> opParens p'` — `<>` is no-break
            // beside.  The inner opParens is unconditional.
            let inner = formula_to_doc_opparens(p_, scope, state);
            doc_text("\u{00AC}").beside(inner)
        }
        And(l, r) => binop_to_doc(l, r, "\u{2227}", scope, state),
        Or(l, r) => binop_to_doc(l, r, "\u{2228}", scope, state),
        Implies(l, r) => binop_to_doc(l, r, "\u{21D2}", scope, state),
        Iff(l, r) => binop_to_doc(l, r, "\u{21D4}", scope, state),
        Forall(vs, body) | Exists(vs, body) => {
            // HS Qua: `sep [quantifier, nest 1 body]` —
            // `quantifier = ppQ <> ppVars vs <> "."`, body indented +1.
            // HS `pp (Qua _ _ _) = scopeFreshness $ do ...`
            // (Formula.hs:496-502) — every Qua saves/restores state.
            let sym = if matches!(f, Forall(_, _)) { "\u{2200}" } else { "\u{2203}" };
            state.scope_freshness(|state| {
                let new_scope = allocate_formula_binders(vs, scope, state);
                let mut vars_str = String::new();
                for (i, b) in new_scope[scope.len()..].iter().enumerate() {
                    if i > 0 { vars_str.push(' '); }
                    vars_str.push_str(sort_prefix_from_hint(b.1));
                    vars_str.push_str(&b.2);
                }
                let quant = doc_text(format!("{} {}.", sym, vars_str));
                let body_doc = formula_to_doc(body, &new_scope, state);
                hpj::sep(vec![quant, body_doc.nest(1)])
            })
        }
    }
}

/// HS opParens (unconditional `(` / `)` wrap).
fn formula_to_doc_opparens(
    f: &p::Formula,
    scope: &[Bind],
    state: &mut PreciseFreshState,
) -> crate::pretty_hpj::Doc {
    // HS `opParens` always wraps in parens.  Our `is_atomic_formula`
    // (`True/False/Pred`) short-circuits to no parens — but HS opParens
    // wraps everything: `opParens d = "(" <> d <> ")"`.
    // Keep RS's atomicity heuristic for True/False/Pred (it has no
    // visible effect on the wireguard case) — preserves byte-identical
    // output with the legacy path.
    if is_atomic_formula(f) {
        formula_to_doc(f, scope, state)
    } else {
        doc_op_parens(formula_to_doc(f, scope, state))
    }
}

fn binop_to_doc(
    l: &p::Formula,
    r: &p::Formula,
    op: &str,
    scope: &[Bind],
    state: &mut PreciseFreshState,
) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj as hpj;
    // HS Conn: `sep [opParens p <-> op, opParens q]`.  `<->` is `<+>`
    // (beside with single space).
    let l_doc = formula_to_doc_opparens(l, scope, state);
    let r_doc = formula_to_doc_opparens(r, scope, state);
    hpj::sep(vec![
        l_doc.beside_sp(doc_text(op)),
        r_doc,
    ])
}

// =============================================================================
// HS HughesPJ ribbon + fit constants (used by the guarded-formula
// wrap-aware renderer below).  The full-formula path now goes through
// the `pretty_hpj::Doc` engine; the guarded path retains a focused
// string-based fit check.
// =============================================================================

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

fn resolved_sort(v: &p::VarSpec, scope: &[Bind]) -> p::SortHint {
    if !matches!(v.sort, p::SortHint::Untagged) {
        return v.sort;
    }
    // Walk scope inner-most first.
    for b in scope.iter().rev() {
        if &b.0 == &v.name {
            return b.1;
        }
    }
    v.sort
}

/// Find the binding's display name, if any.  Match by (name, resolved sort)
/// against the scope (innermost first).  Mirrors HS's De Bruijn lookup —
/// a Bound var resolves to its binder's freshly-allocated LVar (whose
/// `show` is `sortPrefix ++ name[.idx]`).
fn lookup_display(name: &str, sort: p::SortHint, scope: &[Bind]) -> Option<(p::SortHint, String)> {
    for b in scope.iter().rev() {
        if b.0 == name && b.1 == sort {
            return Some((b.1, b.2.clone()));
        }
    }
    None
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
/// When the (name, sort) matches a binder, emit the binder's *display*
/// name (which may carry a `.<idx>` suffix per HS `show LVar`,
/// LTerm.hs:526-532).  Otherwise emit the source name+idx as Free.
fn pp_var_scoped(v: &p::VarSpec, scope: &[Bind], out: &mut String) {
    let sort = resolved_sort(v, scope);
    if v.idx == 0 {
        if let Some((bsort, display)) = lookup_display(&v.name, sort, scope) {
            out.push_str(sort_prefix_from_hint(bsort));
            out.push_str(&display);
            return;
        }
    }
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

fn pp_atom(a: &p::Atom, scope: &[Bind], out: &mut String) {
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

fn pp_fact(fa: &p::Fact, scope: &[Bind], out: &mut String) {
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

fn pp_term(t: &p::Term, prec: TermPrec, scope: &[Bind], out: &mut String) {
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
            //
            // For AC ops: HS's term is `FApp (AC op) [args]` — a flat
            // n-ary node — so `ppTerms` joins with the op and a SINGLE
            // outer paren-pair surrounds the whole chain.  Our parser
            // AST represents AC as binary `BinOp(op, l, r)`; to match
            // HS's flat rendering, flatten same-op children and join
            // with the op symbol.  Without this, nested binary
            // representations like `Xor(Xor(a, b), c)` print as
            // `((a⊕b)⊕c)` instead of HS's `(a⊕b⊕c)`.
            let is_exp = matches!(op, p::BinOp::Exp);
            let is_ac = matches!(op,
                p::BinOp::Mult | p::BinOp::Union | p::BinOp::Xor | p::BinOp::NatPlus);
            if is_ac {
                fn flatten<'a>(op: p::BinOp, t: &'a p::Term, out: &mut Vec<&'a p::Term>) {
                    match t {
                        p::Term::BinOp(inner, l, r) if *inner == op => {
                            flatten(op, l, out);
                            flatten(op, r, out);
                        }
                        _ => out.push(t),
                    }
                }
                let mut flat: Vec<&p::Term> = Vec::new();
                flatten(*op, l, &mut flat);
                flatten(*op, r, &mut flat);
                out.push('(');
                let sym = binop_symbol(*op);
                for (i, child) in flat.iter().enumerate() {
                    if i > 0 { out.push_str(sym); }
                    pp_term(child, TermPrec::Top, scope, out);
                }
                out.push(')');
                let _ = prec;
                return;
            }
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

fn pp_guarded(g: &Guarded, state: &mut PreciseFreshState, out: &mut String) {
    pp_guarded_inner(g, false, &[], state, out);
}

/// Look up the binder for `Bound(n)` given a scope stack (outer-to-inner
/// order).  HS convention: `Bound 0` = innermost binder's last entry.
/// We map by walking the stack inner→outer and indexing each binder's
/// var list from the end.  Returns the binder's display name + sort —
/// the display name carries the `.<idx>` suffix when shadowing
/// (HS `show LVar`, LTerm.hs:526-532; allocated by `openGuarded` via
/// `freshLVar`, Guarded.hs:362-371).
fn lookup_bound<'a>(n: u32, scope: &'a [Vec<Bind>]) -> Option<&'a Bind> {
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
    scope: &[Vec<Bind>],
    state: &mut PreciseFreshState,
    out: &mut String,
) {
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
                pp_guarded_inner(x, true, scope, state, out);
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
                pp_guarded_inner(x, true, scope, state, out);
            }
            if needs { out.push(')'); }
        }
        Guarded::GGuarded { qua, vars, guards, body } => {
            // HS `pp gf0@(GGuarded _ _ _ _) = scopeFreshness $ do ...`
            // (Guarded.hs:844-846): save Precise state, openGuarded
            // allocates fresh display names via `freshLVar n s`
            // (Guarded.hs:362-371, LTerm.hs:295-296), render under
            // the resulting scope, then restore state on exit.
            state.scope_freshness(|state| pp_gguarded(qua, vars, guards, body, paren_atomic, scope, state, out))
        }
    }
}

/// Render the body of a `GGuarded` after `scopeFreshness` has saved the
/// Precise state.  Mirrors HS Guarded.hs:844-864.
fn pp_gguarded(
    qua: &Quant,
    vars: &[crate::guarded::GBinding],
    guards: &[crate::guarded::GAtom],
    body: &Guarded,
    paren_atomic: bool,
    scope: &[Vec<Bind>],
    state: &mut PreciseFreshState,
    out: &mut String,
) {
    let alloc = allocate_guarded_binders(vars, scope, state);
    let mut new_scope: Vec<Vec<Bind>> = scope.to_vec();
    new_scope.push(alloc);
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
    pp_binding_list_with_display(&new_scope[scope.len()], out);
    out.push_str(". ");
    // Antecedent (guards).
    if guards.is_empty() {
        // Just the body.
        pp_guarded_inner(body, false, &new_scope, state, out);
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
            pp_guarded_inner(body, false, &new_scope, state, out);
        }
    }
    if paren_atomic { out.push(')'); }
}

/// Render the binder line for a GGuarded — uses the display names
/// allocated by `allocate_guarded_binders` (HS `freshLVar`, LTerm.hs
/// 295-296), so a shadowed inner binder emits `#j.1` instead of `#j`.
fn pp_binding_list_with_display(bs: &[Bind], out: &mut String) {
    for (i, b) in bs.iter().enumerate() {
        if i > 0 { out.push(' '); }
        out.push_str(sort_prefix_from_hint(b.1));
        out.push_str(&b.2);
    }
}


// =============================================================================
// HS-style wrapped layout for Guarded — legacy string-based path
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
    scope: &[Vec<Bind>],
    state: &mut PreciseFreshState,
) -> String {
    // Flat first.
    let flat = {
        let mut s = String::new();
        // Clone state for the flat probe — pp_guarded_inner mutates state
        // at GGuarded scope-freshness boundaries but restores on exit, so
        // a clone is safe and the outer state remains unchanged.
        let mut probe_state = state.clone();
        pp_guarded_inner(g, paren_atomic, scope, &mut probe_state, &mut s);
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
                let child = pp_guarded_inner_wrapped(x, true, sep_col, child_line_start, width, scope, state);
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
                let child = pp_guarded_inner_wrapped(x, true, sep_col, child_line_start, width, scope, state);
                out.push_str(&child);
                if i + 1 < xs.len() {
                    out.push_str(" \u{2227}"); // ∧
                }
            }
            if outer { out.push(')'); }
            out
        }

        Guarded::GGuarded { qua, vars, guards, body } => {
            // HS `scopeFreshness` boundary (Guarded.hs:844-846): save
            // Precise state, allocate display names, render, restore.
            state.scope_freshness(|state| {
            let alloc = allocate_guarded_binders(vars, scope, state);
            let mut new_scope: Vec<Vec<Bind>> = scope.to_vec();
            new_scope.push(alloc);

            // Negation shortcut (HS Guarded.hs:856-857).  Flat only.
            if matches!(qua, Quant::All)
                && vars.is_empty()
                && body_is_false(body)
            {
                return flat.clone();
            }
            // `∃ vs. (guards)` shortcut (HS Guarded.hs:854-855).
            // Try flat (the only sensible layout); if the guards
            // themselves are long, fall through to the generic path.
            if matches!(qua, Quant::Ex) && body_is_true(body) {
                return flat.clone();
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
            pp_binding_list_with_display(&new_scope[scope.len()], &mut quantifier);
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
            let dsucc_str = pp_guarded_inner_wrapped(body, false, body_col, body_col, width, &new_scope, state);

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
            })
        }
    }
}

/// Pretty-print a binder list — uses each entry's display name, which
/// is the source name (idx==0) or `name.<idx>` (HS `show LVar`,
/// LTerm.hs:526-532) after `freshLVar` allocation.
fn pp_gatom(a: &crate::guarded::GAtom, scope: &[Vec<Bind>], out: &mut String) {
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

fn pp_gfact(fa: &crate::guarded::GFact, scope: &[Vec<Bind>], out: &mut String) {
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

fn pp_gterm(t: &crate::guarded::GTerm, prec: TermPrec, scope: &[Vec<Bind>], out: &mut String) {
    use crate::guarded::{GTerm, BVar};
    match t {
        GTerm::Var(BVar::Free(v)) => pp_var(v, out),
        GTerm::Var(BVar::Bound(n)) => {
            if let Some(b) = lookup_bound(*n, scope) {
                out.push_str(sort_prefix_from_hint(b.1));
                out.push_str(&b.2);
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
