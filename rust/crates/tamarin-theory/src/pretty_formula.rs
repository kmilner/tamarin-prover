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

/// Render the lemma-header line, mirroring HS `prettyLemma`
/// (Lemma.hs:119-122):
///   `nest 2 $ sep [ prettyTraceQuantifier, doubleQuotes (prettyLNFormula f) ]`
/// Built as ONE `Doc` through the HS-faithful engine so the `sep`
/// (quant-keyword vs formula) flat-or-wrap decision, the formula's
/// internal `sep`/`nest` wrapping, and the continuation-line indents are
/// byte-identical to HS.  `quant` is the trace-quantifier keyword (e.g.
/// `"all-traces"` / `"exists-trace"`).  The returned string begins at
/// column 0 (the `nest 2` indent IS included in the output, like HS's
/// `nest 2` rendered at the theory's column 0).
pub fn lemma_header_line(quant: &str, f: &p::Formula) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    let mut state = avoid_precise_formula(f);
    let formula_doc = formula_to_doc(f, &[], &mut state);
    // `doubleQuotes d = "\"" <> d <> "\""` (Class.hs:148).
    let dq = Doc::text("\"").beside(formula_doc).beside(Doc::text("\""));
    // `sep [quant, dq]` then `nest 2`.
    let line = hpj::sep(vec![Doc::text(quant), dq]).nest(2);
    line.render()
}

/// Render `nest n $ doubleQuotes (prettyLNFormula f)` through the
/// HS-faithful engine (the restriction-body shape, TheoryObject.hs:850).
/// The `nest n` indent is included in the output; the `"` is a real Doc
/// `beside` so the formula's wrapped continuation lines indent to the
/// formula's start column.
pub fn formula_doublequoted_nested(f: &p::Formula, nest_n: usize) -> String {
    use crate::pretty_hpj::Doc;
    let mut state = avoid_precise_formula(f);
    let formula_doc = formula_to_doc(f, &[], &mut state);
    let dq = Doc::text("\"").beside(formula_doc).beside(Doc::text("\""));
    dq.nest(nest_n as isize).render()
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
/// Routes through the HS-faithful Doc engine (`crate::pretty_hpj`):
/// `guarded_to_doc` builds a `Doc` tree that mirrors HS `prettyGuarded`'s
/// `sep`/`nest`/`fsep` structure node-for-node, then `render_at` lays it
/// out with the same `get1` per-NilAbove `w`-shrinkage HughesPJ uses
/// (HughesPJ.hs:1011).  `indent` is the column where the formula's first
/// char will land (e.g. 1, right after the opening `"` of the lemma's
/// `doubleQuotes` wrap, Lemma.hs:138/141).
///
/// NOTE: `render_at`'s `sl_initial` only shrinks the budget; it does NOT
/// shift continuation lines by the leading prefix width.  In HS the
/// `prettyGuarded` doc is the RIGHT operand of `doubleQuotes`'s `<>`
/// (`"\"" <> prettyGuarded <> "\""`, Class.hs:148), and HughesPJ `beside`
/// DOES shift the right doc's vertical layout by the leading `"`'s width
/// (1 col).  Callers that place the formula after a 1-col prefix must use
/// `pretty_guarded_doublequoted` (which models the `"` as a real Doc
/// `beside`, getting the continuation indent right).  This bare entry
/// point is kept for callers that pass `indent=0`.
pub fn pretty_guarded_wrapped(g: &Guarded, indent: usize, _width: usize) -> String {
    use crate::pretty_hpj as hpj;
    let mut state = avoid_precise_guarded(g);
    let doc = guarded_to_doc(g, &[], &mut state);
    doc.render_at(hpj::LINE_LENGTH, hpj::RIBBON, indent)
}

/// HS `doubleQuotes (prettyGuarded gf)` (Lemma.hs:138/141, Class.hs:148).
/// Builds `"\"" <> guarded_doc <> "\""` as a single Doc and renders it,
/// so HughesPJ `beside`'s column-shift puts continuation lines at the
/// formula's start column (1, right after the opening quote) — matching
/// HS byte-exact.  The result is the full `"..."` string.
pub fn pretty_guarded_doublequoted(g: &Guarded) -> String {
    use crate::pretty_hpj::Doc;
    let mut state = avoid_precise_guarded(g);
    let doc = guarded_to_doc(g, &[], &mut state);
    Doc::text("\"").beside(doc).beside(Doc::text("\"")).render()
}

/// Build the `pretty_hpj::Doc` for a `prettyGoal (DisjG (Disj gfs))`
/// (Constraints.hs:281-283):
///   `fsep $ punctuate (operator_ "  ∥") (map (nest 1 . parens . prettyGuarded) gfs)`
/// Each disjunct is `nest 1 (parens (prettyGuarded gf))`, the separator is
/// `"  ∥"` (two spaces + ∥) placed AFTER each non-last item by `punctuate`,
/// and the items are joined by `fsep` (paragraph-fill, one space between).
pub fn disj_goal_to_doc(gfs: &[Guarded]) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let items: Vec<Doc> = gfs.iter()
        .map(|g| {
            let mut state = avoid_precise_guarded(g);
            let inner = guarded_to_doc(g, &[], &mut state);
            // `nest 1 (parens (prettyGuarded gf))` — `parens` (Class.hs:149)
            // is `"(" <> d <> ")"`.
            Doc::text("(").beside(inner).beside(Doc::text(")")).nest(1)
        })
        .collect();
    let punct = hpj::punctuate(Doc::text("  \u{2225}"), items); // "  ∥"
    hpj::fsep(punct)
}

/// Render a full `solve( <DisjG> )` proof-method line through the
/// HS-faithful engine, mirroring HS
///   `SolveGoal goal -> keyword_ "solve(" <-> prettyGoal goal <-> keyword_ ")"`
/// (ProofMethod.hs:1494) where `<->` is `<+>` (beside-with-space).  The
/// whole thing is built as ONE `Doc` so HughesPJ's beside column-shift
/// indents the goal's wrapped continuation lines to the column after
/// `solve( ` (= `indent + 7`), byte-identical to HS.
///
/// `indent` is the column where `solve(` starts (the proof-tree depth
/// indent).  The returned string's FIRST line has NO leading indent (the
/// proof-tree printer adds that itself); continuation lines carry their
/// full absolute indentation.
pub fn solve_disj_goal_line(gfs: &[Guarded], indent: usize) -> String {
    use crate::pretty_hpj::Doc;
    let goal_doc = disj_goal_to_doc(gfs);
    // `keyword_ "solve(" <+> goal <+> keyword_ ")"`.
    let line = Doc::text("solve(")
        .beside_sp(goal_doc)
        .beside_sp(Doc::text(")"));
    // Place at column `indent`: nest by `indent` so continuation lines are
    // indented to absolute columns, then strip the leading `indent` spaces
    // from the first line (the proof-tree printer prepends them itself).
    let indented = line.nest(indent as isize);
    let rendered = indented.render();
    // The first line begins with exactly `indent` spaces from the nest.
    let strip = rendered.chars().take(indent).take_while(|c| *c == ' ').count();
    rendered[strip..].to_string()
}

/// Build the `solve( <goal> )` line for a NON-DisjG goal, where the
/// caller has already constructed `goal_doc` for the goal body (HS
/// `prettyGoal`, Constraints.hs:273-287).  Mirrors HS
///   `SolveGoal goal -> keyword_ "solve(" <-> prettyGoal goal <-> keyword_ ")"`
/// (ProofMethod.hs:1494), `<->` = `<+>` (beside-with-space).  The whole
/// line is ONE `Doc` so HughesPJ's beside column-shift indents the goal's
/// wrapped continuation lines to the column after `solve( ` (= indent+7),
/// byte-identical to HS.  Same wrapping plumbing as `solve_disj_goal_line`.
pub fn solve_goal_line_from_doc(goal_doc: crate::pretty_hpj::Doc, indent: usize) -> String {
    use crate::pretty_hpj::Doc;
    let line = Doc::text("solve(")
        .beside_sp(goal_doc)
        .beside_sp(Doc::text(")"));
    let indented = line.nest(indent as isize);
    let rendered = indented.render();
    let strip = rendered.chars().take(indent).take_while(|c| *c == ' ').count();
    rendered[strip..].to_string()
}

/// Public accessor for the Doc-based fact renderer (HS `prettyLNFact` /
/// `prettyFact`), for use building goal Docs in pretty_theory.rs.
pub fn fact_doc(fa: &p::Fact) -> crate::pretty_hpj::Doc {
    fact_to_doc(fa, &[])
}

/// Public accessor for the Doc-based term renderer (HS `prettyLNTerm`).
pub fn term_doc(t: &p::Term) -> crate::pretty_hpj::Doc {
    term_to_doc(t, &[])
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

/// HS `ppFactsList list = fsep [operator_ "[", ppList (map ppFact list),
/// operator_ "]"]` where `ppList = fsep . punctuate comma`
/// (Theory/Model/Rule.hs:1266-1268).
fn facts_list_doc(facts: &[p::Fact]) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let inner: Vec<Doc> = facts.iter().map(|f| fact_to_doc(f, &[])).collect();
    let body = hpj::fsep(hpj::punctuate(comma_doc(), inner));
    hpj::fsep(vec![Doc::text("["), body, Doc::text("]")])
}

/// HS `prettyRuleRestrGen` (Theory/Model/Rule.hs:1254-1262):
///   `sep [ nest 1 (ppFactsList prems)
///        , if null acts then "-->"
///          else fsep ["--[", ppList (map ppFact acts), "]->"]
///        , nest 1 (ppFactsList concls) ]`
/// Built as a `pretty_hpj::Doc` so the `sep`/`fsep` wrapping is HS-exact.
pub fn rule_body_to_doc(
    prems: &[p::Fact],
    acts: &[p::Fact],
    concls: &[p::Fact],
) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let prem_doc = facts_list_doc(prems).nest(1);
    let arrow = if acts.is_empty() {
        Doc::text("-->")
    } else {
        let act_docs: Vec<Doc> = acts.iter().map(|f| fact_to_doc(f, &[])).collect();
        let act_body = hpj::fsep(hpj::punctuate(comma_doc(), act_docs));
        hpj::fsep(vec![Doc::text("--["), act_body, Doc::text("]->")])
    };
    let conc_doc = facts_list_doc(concls).nest(1);
    hpj::sep(vec![prem_doc, arrow, conc_doc])
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
    // HS `prettyFact` (Theory/Model/Fact.hs:539-544):
    //   `ppFact n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppTerm t`
    // `nestShort'` (Utils/PrettyPrint/Class.hs:221-223) wraps as
    // `sep [text "Name(", body, text ")"]`. When `body` is empty
    // (empty-arg fact), HS's HughesPJ `sep` collapses the empty middle
    // and emits `Name( )` with ONE inner space; non-empty `body` emits
    // `Name( a, b )` with one space pad on each side.
    if fa.persistent { out.push('!'); }
    out.push_str(&fa.name);
    if fa.args.is_empty() {
        out.push_str("( )");
    } else {
        out.push_str("( ");
        for (i, t) in fa.args.iter().enumerate() {
            if i > 0 { out.push_str(", "); }
            pp_term(t, TermPrec::Top, scope, out);
        }
        out.push_str(" )");
    }
}

// =============================================================================
// Term / Fact — HughesPJ Doc engine (HS-faithful wrapping)
//
// `term_to_doc` mirrors HS `prettyTerm` (Term/Term.hs:268-296): pairs use
// `ppTerms ", " 1 "<" ">" = fcat . (text "<":) . (++[text ">"]) . map (nest 1)
// . punctuate ", " . map ppTerm`; function applications use
// `ppFun f ts = text (f ++ "(") <> fsep (punctuate comma (map ppTerm ts))
// <> text ")"`.  `fact_to_doc` mirrors HS `prettyFact`/`ppFact`
// (Theory/Model/Fact.hs:539-544) = `nestShort' (n++"(") ")" . fsep .
// punctuate comma $ map ppTerm ts`, with `nestShort' lead finish =
// nestShort (length lead + 1) (text lead) (text finish)` and
// `nestShort n lead finish body = sep [lead $$ nest n body, finish]`
// (Class.hs:218-223).  Building these as real `pretty_hpj::Doc` trees and
// letting the ported HughesPJ engine lay them out makes the fcat/fsep/sep
// wrap decisions byte-identical to HS, replacing the hand-rolled string
// packers in pretty_theory.rs.
// =============================================================================

/// HS `comma = char ','`.
fn comma_doc() -> crate::pretty_hpj::Doc {
    crate::pretty_hpj::Doc::char(',')
}

/// Pretty-print a parser-AST term as a `pretty_hpj::Doc`.  Faithful to HS
/// `prettyTerm`.  `scope` carries bound-var display names (empty for rule
/// bodies; populated when rendering proof-tree/formula terms).
pub fn term_to_doc(t: &p::Term, scope: &[Bind]) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::Doc;
    use p::Term::*;
    match t {
        // Atomic / non-wrapping leaves: render via the existing string
        // printer (these never break internally in HS either).
        Var(_) | PubLit(_) | FreshLit(_) | NatLit(_) | Number(_) | NumberOne
        | NatOne | DhNeutral | PatMatch(_) => {
            let mut s = String::new();
            pp_term(t, TermPrec::Top, scope, &mut s);
            Doc::text(s)
        }
        Pair(items) => {
            // Flatten right-associative pairs exactly as HS `split` does
            // (Term/Term.hs:292-293), splicing a trailing Pair.
            let mut flat: Vec<&p::Term> = Vec::with_capacity(items.len());
            let mut cur: &[p::Term] = items;
            loop {
                let n = cur.len();
                if n == 0 { break; }
                for it in &cur[..n - 1] { flat.push(it); }
                let last = &cur[n - 1];
                if let Pair(inner) = last { cur = inner; } else { flat.push(last); break; }
            }
            pair_doc(&flat, scope)
        }
        App(name, args) => {
            if args.is_empty() {
                // HS `FApp (NoEq (f,_)) [] -> text f` (Term/Term.hs:278).
                Doc::text(name.clone())
            } else {
                fun_doc(name, args, scope)
            }
        }
        AlgApp(name, l, r) => fun_doc_two(name, l, r, scope),
        Diff(l, r) => fun_doc_two("diff", l, r, scope),
        BinOp(_, _, _) => {
            // exp/AC: never break in HS prettyTerm; render flat.
            let mut s = String::new();
            pp_term(t, TermPrec::Top, scope, &mut s);
            Doc::text(s)
        }
    }
}

/// HS `ppTerms ", " 1 "<" ">" flat` (Term/Term.hs:288-290) — a fcat of
/// `text "<"`, each element `nest 1`'d and comma-suffixed (except last),
/// and `text ">"`.
fn pair_doc(flat: &[&p::Term], scope: &[Bind]) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let n = flat.len();
    let mut parts: Vec<Doc> = Vec::with_capacity(n + 2);
    parts.push(Doc::text("<"));
    for (i, t) in flat.iter().enumerate() {
        // HS punctuates with `text ", "`, so all but the last get a
        // trailing ", "; then each is `nest 1`.
        let mut d = term_to_doc(t, scope);
        if i + 1 < n {
            d = d.beside(Doc::text(", "));
        }
        parts.push(d.nest(1));
    }
    parts.push(Doc::text(">"));
    hpj::fcat(parts)
}

/// HS `ppFun f ts = text (f ++ "(") <> fsep (punctuate comma (map ppTerm ts))
/// <> text ")"` (Term/Term.hs:295-296).
fn fun_doc(name: &str, args: &[p::Term], scope: &[Bind]) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let arg_docs: Vec<Doc> = args.iter().map(|a| term_to_doc(a, scope)).collect();
    let body = hpj::fsep(hpj::punctuate(comma_doc(), arg_docs));
    Doc::text(format!("{}(", name)).beside(body).beside(Doc::text(")"))
}

/// `fun_doc` for the binary algebraic / diff shapes that the parser stores
/// as boxed pairs rather than a `Vec`.
fn fun_doc_two(
    name: &str,
    l: &p::Term,
    r: &p::Term,
    scope: &[Bind],
) -> crate::pretty_hpj::Doc {
    let args = [l.clone(), r.clone()];
    fun_doc(name, &args, scope)
}

/// Pretty-print a fact as a `pretty_hpj::Doc`.  Faithful to HS `prettyFact`
/// / `ppFact` (Theory/Model/Fact.hs:539-544) with `nestShort'`
/// (Class.hs:218-223).
pub fn fact_to_doc(fa: &p::Fact, scope: &[Bind]) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let lead = {
        let mut s = String::new();
        if fa.persistent { s.push('!'); }
        s.push_str(&fa.name);
        s.push('(');
        s
    };
    let arg_docs: Vec<Doc> = fa.args.iter().map(|a| term_to_doc(a, scope)).collect();
    let body = hpj::fsep(hpj::punctuate(comma_doc(), arg_docs));
    let mut d = nest_short_doc(&lead, ")", body);
    // Fact annotations: `<> ppAnn an = brackets . fsep . punctuate comma`.
    if !fa.annotations.is_empty() {
        let mut ann = String::from("[");
        for (i, a) in fa.annotations.iter().enumerate() {
            if i > 0 { ann.push_str(", "); }
            ann.push_str(match a {
                p::FactAnnotation::SolveFirst => "+",
                p::FactAnnotation::SolveLast => "-",
                p::FactAnnotation::NoSources => "no_precomp",
            });
        }
        ann.push(']');
        d = d.beside(Doc::text(ann));
    }
    d
}

/// HS `nestShort' lead finish body =
///   nestShort (length lead + 1) (text lead) (text finish) body
///   = sep [ text lead $$ nest n (text finish-less body), text finish ]`
/// where `$$` is HughesPJ `above` (Class.hs:218-223).
fn nest_short_doc(lead: &str, finish: &str, body: crate::pretty_hpj::Doc) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let n = lead.chars().count() as isize + 1;
    let above = Doc::text(lead).above(body.nest(n));
    hpj::sep(vec![above, Doc::text(finish)])
}

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
            // HS `prettyTerm` (Term/Term.hs:277,292-293):
            //   `FApp pairSym _ -> ppTerms ", " 1 "<" ">" (split t)`
            //   `split (FPair t1 t2) = t1 : split t2`
            // HS's right-associative `tupleterm` parser
            // (Theory/Text/Parser/Term.hs:188) makes `<a, b, c>` into
            // `Pair(a, Pair(b, c))`. When the last item of a Pair is
            // itself a Pair (as in `<a, b, <c, d>>` →
            // `Pair(a, Pair(b, Pair(c, d)))`), HS's recursive `split`
            // walks the rightmost child and emits a flat
            // `<a, b, c, d>`. Mirror that here: splice the last item
            // when it's a Pair.
            let mut flat: Vec<&p::Term> = Vec::with_capacity(items.len());
            let mut cur: &[p::Term] = items;
            loop {
                let n = cur.len();
                if n == 0 { break; }
                for it in &cur[..n - 1] { flat.push(it); }
                let last = &cur[n - 1];
                if let Pair(inner) = last {
                    cur = inner;
                } else {
                    flat.push(last);
                    break;
                }
            }
            out.push('<');
            for (i, it) in flat.iter().enumerate() {
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
// HS-faithful wrapped layout for Guarded — Doc-engine path
// =============================================================================
//
// Build a `pretty_hpj::Doc` tree mirroring HS `prettyGuarded`
// (Guarded.hs:822-867) EXACTLY, then render it via the HughesPJ-faithful
// engine (`crate::pretty_hpj`).  The atoms/terms render to flat strings
// (HS `prettyNAtom` produces no internal sep/nest), so only the
// formula-structural nodes (GDisj/GConj/GGuarded) produce sep-Unions
// where the engine makes byte-exact wrap decisions.
//
// HS recurrences (Guarded.hs:830-866):
//   pp (GAto a)        = prettyNAtom (bvarToLVar a)            -- flat
//   pp (GDisj [])      = operator_ "⊥"
//   pp (GDisj xs)      = parens $ sep $ punctuate " ∨" (map opParens ps)
//   pp (GConj [])      = operator_ "⊤"
//   pp (GConj xs)      = sep $ punctuate " ∧" (map opParens ps)
//   pp (GGuarded ...)  = scopeFreshness $ ... with
//       dante      = nest 1 (pp (GConj antecedent))
//       quantifier = operator_ ppQ <-> ppVars vs <> operator_ "."
//       (Ex,_,GConj []) -> sep [quantifier, dante]
//       (All,[],GDisj []) | gfalse -> operator_ "¬" <> dante
//       _               -> dsucc = nest 1 (pp gf);
//                          sep [quantifier, sep [dante, connective, dsucc]]

/// HS `opParens d = operator_ "(" <> d <> operator_ ")"` — for the plain
/// `Doc` instance `operator_ = text` and `highlight = id`, so this is an
/// unconditional `"(" <> d <> ")"` (Highlight.hs:58-59).
fn gdoc_op_parens(d: crate::pretty_hpj::Doc) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::Doc;
    Doc::text("(").beside(d).beside(Doc::text(")"))
}

/// Build a `pretty_hpj::Doc` for a guarded formula, mirroring HS `pp`
/// inside `prettyGuarded` (Guarded.hs:830-866).  Threads the Precise
/// fresh `state` exactly as `pp_guarded_inner` does (scope-freshness at
/// each GGuarded), and reuses `pp_gatom`/`pp_binding_list_with_display`
/// for the flat atom and binder strings.
fn guarded_to_doc(
    g: &Guarded,
    scope: &[Vec<Bind>],
    state: &mut PreciseFreshState,
) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    match g {
        Guarded::Atom(a) => {
            // HS `pp (GAto a) = prettyNAtom (bvarToLVar a)` — flat atom.
            let mut s = String::new();
            pp_gatom(a, scope, &mut s);
            Doc::text(s)
        }
        Guarded::Disj(xs) if xs.is_empty() => Doc::text("\u{22A5}"), // ⊥
        Guarded::Conj(xs) if xs.is_empty() => Doc::text("\u{22A4}"), // ⊤
        Guarded::Disj(xs) => {
            // HS: `parens $ sep $ punctuate (operator_ " ∨") (map opParens ps)`.
            let ps: Vec<Doc> = xs.iter()
                .map(|x| gdoc_op_parens(guarded_to_doc(x, scope, state)))
                .collect();
            let punct = hpj::punctuate(Doc::text(" \u{2228}"), ps); // " ∨"
            // `parens` (Class.hs:149) is `"(" <> d <> ")"` (no space).
            Doc::text("(").beside(hpj::sep(punct)).beside(Doc::text(")"))
        }
        Guarded::Conj(xs) => {
            // HS: `sep $ punctuate (operator_ " ∧") (map opParens ps)`.
            let ps: Vec<Doc> = xs.iter()
                .map(|x| gdoc_op_parens(guarded_to_doc(x, scope, state)))
                .collect();
            let punct = hpj::punctuate(Doc::text(" \u{2227}"), ps); // " ∧"
            hpj::sep(punct)
        }
        Guarded::GGuarded { qua, vars, guards, body } => {
            // HS: `scopeFreshness $ do ...` (Guarded.hs:846-862).
            state.scope_freshness(|state| {
                gguarded_to_doc(qua, vars, guards, body, scope, state)
            })
        }
    }
}

/// Doc for a `GGuarded`, after `scopeFreshness` saved the Precise state.
/// Mirrors HS Guarded.hs:849-866.
fn gguarded_to_doc(
    qua: &Quant,
    vars: &[crate::guarded::GBinding],
    guards: &[crate::guarded::GAtom],
    body: &Guarded,
    scope: &[Vec<Bind>],
    state: &mut PreciseFreshState,
) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let alloc = allocate_guarded_binders(vars, scope, state);
    let mut new_scope: Vec<Vec<Bind>> = scope.to_vec();
    new_scope.push(alloc);

    // `dante = nest 1 $ pp (GConj (Conj antecedent))` (Guarded.hs:854).
    // The antecedent is `map (GAto ...) atoms`, so `pp (GConj ...)` =
    // `sep $ punctuate " ∧" (map opParens [GAto a])` — each guard is a
    // flat atom wrapped in opParens.
    let dante = {
        if guards.is_empty() {
            // `pp (GConj (Conj [])) = operator_ "⊤"`.
            Doc::text("\u{22A4}").nest(1)
        } else {
            let ps: Vec<Doc> = guards.iter()
                .map(|gd| {
                    let mut s = String::new();
                    pp_gatom(gd, &new_scope, &mut s);
                    gdoc_op_parens(Doc::text(s))
                })
                .collect();
            let punct = hpj::punctuate(Doc::text(" \u{2227}"), ps);
            hpj::sep(punct).nest(1)
        }
    };

    // `quantifier = operator_ ppQuant <-> ppVars vs <> operator_ "."`.
    // `<->` is `<+>` (beside with one space); `ppVars = fsep (map show)`.
    let sym = match qua { Quant::All => "\u{2200}", Quant::Ex => "\u{2203}" };
    let var_docs: Vec<Doc> = new_scope[scope.len()].iter()
        .map(|b| {
            let mut s = String::new();
            s.push_str(sort_prefix_from_hint(b.1));
            s.push_str(&b.2);
            Doc::text(s)
        })
        .collect();
    let ppvars = hpj::fsep(var_docs);
    // `operator_ sym <+> ppvars <> operator_ "."`
    let quantifier = Doc::text(sym).beside_sp(ppvars).beside(Doc::text("."));

    // Case analysis (Guarded.hs:855-862).
    let is_ex_trivial = matches!(qua, Quant::Ex) && body_is_true(body);
    let is_neg = matches!(qua, Quant::All) && vars.is_empty() && body_is_false(body);

    if is_neg {
        // `(All, [], GDisj []) | gf == gfalse -> operator_ "¬" <> dante`.
        Doc::text("\u{00AC}").beside(dante)
    } else if is_ex_trivial {
        // `(Ex, _, GConj []) -> sep [quantifier, dante]`.
        hpj::sep(vec![quantifier, dante])
    } else {
        // `_ -> dsucc = nest 1 (pp gf);
        //       sep [quantifier, sep [dante, connective, dsucc]]`.
        let connective = Doc::text(match qua {
            Quant::All => "\u{21D2}", // ⇒
            Quant::Ex => "\u{2227}",  // ∧
        });
        let dsucc = guarded_to_doc(body, &new_scope, state).nest(1);
        let inner = hpj::sep(vec![dante, connective, dsucc]);
        hpj::sep(vec![quantifier, inner])
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
    // Empty-arg case collapses to a single inner space — see `pp_fact`
    // for the HS citation.
    if fa.persistent { out.push('!'); }
    out.push_str(&fa.name);
    if fa.args.is_empty() {
        out.push_str("( )");
    } else {
        out.push_str("( ");
        for (i, t) in fa.args.iter().enumerate() {
            if i > 0 { out.push_str(", "); }
            pp_gterm(t, TermPrec::Top, scope, out);
        }
        out.push_str(" )");
    }
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
            // HS `prettyTerm` (Term/Term.hs:273-274,287-290):
            //   `FApp (AC o)   ts -> ppTerms (ppACOp o) 1 "(" ")" ts`
            //   `FApp (NoEq s) [t1,t2] | s == expSym -> ppTerm t1 <> "^" <> ppTerm t2`
            // AC ops (Mult/Union/Xor/NatPlus) ALWAYS print with a SINGLE
            // surrounding `(` `)` (the lead/finish in `ppTerms`) around the
            // whole FLAT n-ary chain; `exp` prints with no paren guard.
            // Our AST stores AC as binary `BinOp(op, l, r)`; flatten same-op
            // children and join under one paren-pair to match HS — without
            // this `('1'++x)++z` stayed nested instead of HS `('1'++x++z)`,
            // and `x++z = y` lost HS's outer `(x++z)` parens.  Mirror of the
            // parser-AST `pp_term` AC handling (this fn, ~l.1108).
            let is_exp = matches!(op, p::BinOp::Exp);
            if is_exp {
                pp_gterm(l, TermPrec::Top, scope, out);
                out.push_str(binop_symbol(*op));
                pp_gterm(r, TermPrec::Top, scope, out);
                let _ = prec;
                return;
            }
            fn flatten<'a>(
                op: p::BinOp,
                t: &'a crate::guarded::GTerm,
                out: &mut Vec<&'a crate::guarded::GTerm>,
            ) {
                match t {
                    crate::guarded::GTerm::BinOp(inner, l, r) if *inner == op => {
                        flatten(op, l, out);
                        flatten(op, r, out);
                    }
                    _ => out.push(t),
                }
            }
            let mut flat: Vec<&crate::guarded::GTerm> = Vec::new();
            flatten(*op, l, &mut flat);
            flatten(*op, r, &mut flat);
            out.push('(');
            let sym = binop_symbol(*op);
            for (i, child) in flat.iter().enumerate() {
                if i > 0 { out.push_str(sym); }
                pp_gterm(child, TermPrec::Top, scope, out);
            }
            out.push(')');
            let _ = prec;
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


