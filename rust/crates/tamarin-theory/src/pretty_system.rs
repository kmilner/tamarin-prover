//! Pretty-printer for the constraint `System`.
//!
//! Port of `prettyNonGraphSystem` from
//! `lib/theory/src/Theory/Constraint/System.hs:1673`.  Emits the same
//! ordered section list the Haskell interactive UI shows in its
//! "Constraint system" pane:
//!
//!   last:     ...
//!   formulas: ...
//!   subterms: ...
//!   equations: ...
//!   lemmas: ...
//!   allowed cases: ...
//!   solved formulas: ...
//!   unsolved constraints: ...
//!   solved constraints: ...
//!
//! NOTE: the `subterms` and `equations` section bodies are now faithful
//! ports of Haskell's `prettySubtermStore` (SubtermStore.hs:567-579) and
//! `prettyEqStore` (EquationStore.hs:566-586) — same `Contradictory` /
//! `CONTRADICTORY` headers, numbered keyword sections and `∃`-quantified
//! disjuncts — built on the `pretty_hpj` HughesPJ Doc engine.  The only
//! residual divergences are documented on `pretty_subterm_store` /
//! `pretty_eq_store` (flat-atom term rendering; derived term `Ord` for the
//! eq-store subst grouping).  These are interactive-UI diagnostic panes
//! only and do not affect proof results or golden `--prove` output.  The
//! inter-section blank lines that Haskell's `vsep`/`$--$` inserts between
//! non-empty top-level sections (Class.hs) are still not reproduced here.

use tamarin_term::pretty::{pp_lvar, pretty_lnterm};

use crate::pretty_hpj::{fsep, punctuate, Doc};
use crate::constraint::constraints::{Goal, NodeId};
use crate::constraint::system::{SourceKind, System};
use crate::fact::{fact_tag_name, LNFact};
use crate::guarded::Guarded;
use crate::pretty_formula::pretty_guarded;

/// Emit just the non-graph-part of the system, matching Haskell's
/// `prettyNonGraphSystem`.  See file-level docs for the section list.
pub fn pretty_non_graph_system(sys: &System) -> String {
    let mut out = String::new();
    section(&mut out, "last", &pretty_last(sys));
    section(&mut out, "formulas", &pretty_formula_set(&sys.formulas));
    section(&mut out, "subterms", &pretty_subterm_store(sys));
    section(&mut out, "equations", &pretty_eq_store(sys));
    section(&mut out, "lemmas", &pretty_formula_set(&sys.lemmas));
    section(&mut out, "allowed cases", &pretty_source_kind(sys.source_kind));
    section(&mut out, "solved formulas", &pretty_formula_set(&sys.solved_formulas));
    section(&mut out, "unsolved constraints", &pretty_goals(sys, false));
    section(&mut out, "solved constraints", &pretty_goals(sys, true));
    out
}

// ---------------------------------------------------------------------
// Section header helper
// ---------------------------------------------------------------------

fn section(out: &mut String, header: &str, body: &str) {
    out.push_str(header);
    out.push(':');
    if body.contains('\n') {
        out.push('\n');
        for line in body.lines() {
            out.push_str("  ");
            out.push_str(line);
            out.push('\n');
        }
    } else if body.is_empty() {
        out.push('\n');
    } else {
        out.push(' ');
        out.push_str(body);
        out.push('\n');
    }
}

// ---------------------------------------------------------------------
// last_atom
// ---------------------------------------------------------------------

fn pretty_last(sys: &System) -> String {
    match &sys.last_atom {
        None => "none".to_string(),
        Some(nid) => pretty_node_id(nid),
    }
}

// ---------------------------------------------------------------------
// formulas / lemmas / solved_formulas
// ---------------------------------------------------------------------

/// Render a guarded-formula collection whose Haskell counterpart is a
/// `S.Set LNGuarded` (System.hs:1679 renders `sLemmas` via `S.toList`,
/// i.e. ascending `Ord LNGuarded` with structural dedup).  RS stores
/// `sLemmas` as a `Vec<Guarded>` in *insertion* order (see
/// `System::insert_lemma`), so the raw Vec would render in a different
/// order than HS whenever two lemmas were inserted out of Ord order
/// (e.g. the two safety restrictions of `design-choices.spthy`).  Mirror
/// `S.toList` here by sorting a view of the Vec with the HS-faithful
/// `cmp_guarded` comparator (guarded.rs — the derived `Ord Guarded`) and
/// collapsing `Ord`-equal duplicates, exactly as the equivalent
/// sort+dedup in `rename_precise.rs` does for the live field.
///
/// This is a *render-time only* reordering: the live `sys.lemmas` Vec is
/// left untouched, so the constraint-solver iteration order (which some
/// implied-formula sites read in storage order) is unchanged and the
/// `--prove` byte-identity corpus is unaffected.  `prettyNonGraphSystem`
/// is reached only from the interactive/web constraint-system pane, never
/// from `--prove` output.
fn pretty_formula_set(items: &[Guarded]) -> String {
    if items.is_empty() { return String::new(); }
    let mut sorted: Vec<&Guarded> = items.iter().collect();
    sorted.sort_by(|a, b| crate::guarded::cmp_guarded(a, b));
    sorted.dedup_by(|a, b| crate::guarded::cmp_guarded(a, b) == std::cmp::Ordering::Equal);
    let mut s = String::new();
    for (i, g) in sorted.into_iter().enumerate() {
        if i > 0 { s.push('\n'); }
        s.push_str(&pretty_guarded(g));
    }
    s
}

// ---------------------------------------------------------------------
// subterm / equation stores
// ---------------------------------------------------------------------

// --- Doc helpers mirroring `Text.PrettyPrint.Class` -------------------

// HS `numbered vsep ds` (Class.hs:252-259): right-flushed 1-based indices,
// items joined vertically (`$-$`) with `vsep` interspersed between them.
fn numbered(vsep: Doc, ds: Vec<Doc>) -> Doc {
    if ds.is_empty() {
        return Doc::empty();
    }
    let n = ds.len();
    let n_width = n.to_string().len();
    let mut acc: Option<Doc> = None;
    for (i, d) in ds.into_iter().enumerate() {
        // `text (flushRight nWidth (show i)) <> d`
        let label = flush_right(n_width, &(i + 1).to_string());
        let item = Doc::text(label).beside(d);
        acc = Some(match acc {
            None => item,
            // intersperse vsep, fold with `$-$` (above_g)
            Some(prev) => prev.above_g(vsep.clone()).above_g(item),
        });
    }
    acc.unwrap_or_else(Doc::empty)
}

// HS `numbered'` (Class.hs:263-264): `numbered (text "") . map (". " <>)`.
// `text ""` is a zero-width text run (NOT `empty`); interspersed with `$-$`
// it inserts a *blank line* between numbered items.  `Doc::text("")`
// collapses to `Doc::Empty` (which would be dropped by `$-$`), so we build
// the zero-width text run explicitly via `blank_text`.
fn numbered_prime(ds: Vec<Doc>) -> Doc {
    let mapped: Vec<Doc> = ds
        .into_iter()
        .map(|d| Doc::text(". ").beside(d))
        .collect();
    numbered(blank_text(), mapped)
}

// HS `text ""` — a zero-width, zero-column text run.  Distinct from
// `Doc::Empty`: under `$$`/`$-$` it contributes a blank line, whereas
// `Empty` is the layout identity and collapses away.
fn blank_text() -> Doc {
    Doc::TextBeside(std::rc::Rc::from(""), 0, std::rc::Rc::new(Doc::Empty))
}

// HS `flushRight n str` (Extension.Prelude): left-pad with spaces to width n.
fn flush_right(n: usize, s: &str) -> String {
    let pad = n.saturating_sub(s.chars().count());
    let mut out = String::with_capacity(pad + s.len());
    for _ in 0..pad {
        out.push(' ');
    }
    out.push_str(s);
    out
}

// HS `combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]`
// (SubtermStore.hs:576 / EquationStore.hs:574).
fn combine(header: &str, d: Doc) -> Doc {
    fsep(vec![Doc::text(format!("{header}:")), d.nest(2)])
}

// Faithful port of Haskell `prettySubtermStore` (SubtermStore.hs:567-579).
// Emits an optional `Contradictory: yes` header, then (when the store is
// non-empty) three numbered keyword-headed sections `Negative Subterms` /
// `Subterms` / `Solved Subterms`, each item rendered as
// `prettyNTerm a $$ nest 3 (⊏ <-> prettyNTerm b)`.
//
// Known divergences (UI diagnostic pane only — not reached by raw
// `--prove` output):
//   * terms are rendered as flat `Doc::text` atoms (this crate exposes
//     only a `String` term printer, not a Doc one), so an individual term
//     wider than the line is not re-wrapped the way HS's `prettyNTerm` Doc
//     would;
//   * ordering is byte-faithful only for `neg_subterms`, which is kept
//     sorted by `add_neg`'s `binary_search` insert (matching HS `S.toList`
//     over the `negSt` Set). `subterms`/`solved_subterms` are `Vec`s in
//     insertion order (`.push()` in `add`/`conjoin`), whereas HS emits the
//     `posSt`/`solvedSt` Sets via `S.toList` in `Ord` order — so their
//     numbered ordering may differ from Haskell. Left as-is: sorting needs a
//     faithful `Ord LNTerm` (FunSym-by-name, like `guarded::cmp_term` but for
//     raw LNTerms); the derived `VTerm` Ord could flip a currently-matching
//     pane, so it is not safe to apply blindly. Tracked as a residual gap.
// Section structure, numbering and the `Contradictory` header are
// byte-faithful.
fn pretty_subterm_store(sys: &System) -> String {
    let st = &sys.subterm_store;

    // `ppSt (a,b) = prettyNTerm a $$ nest 3 (opSubterm <-> prettyNTerm b)`
    let pp_st = |small: &tamarin_term::lterm::LNTerm, big: &tamarin_term::lterm::LNTerm| {
        Doc::text(pretty_lnterm(small)).above(
            Doc::text("\u{228F}") // ⊏  (opSubterm)
                .beside_sp(Doc::text(pretty_lnterm(big)))
                .nest(3),
        )
    };

    let all_empty = st.neg_subterms.is_empty()
        && st.subterms.is_empty()
        && st.solved_subterms.is_empty();

    let mut sections: Vec<Doc> = Vec::new();
    if st.contradictory {
        sections.push(combine("Contradictory", Doc::text("yes")));
    }
    if !all_empty {
        let neg: Vec<Doc> = st
            .neg_subterms
            .iter()
            .map(|(a, b)| pp_st(a, b))
            .collect();
        sections.push(combine("Negative Subterms", numbered_prime(neg)));

        let pos: Vec<Doc> = st
            .subterms
            .iter()
            .map(|c| pp_st(&c.small, &c.big))
            .collect();
        sections.push(combine("Subterms", numbered_prime(pos)));

        let solved: Vec<Doc> = st
            .solved_subterms
            .iter()
            .map(|c| pp_st(&c.small, &c.big))
            .collect();
        sections.push(combine("Solved Subterms", numbered_prime(solved)));
    }

    // HS `vcat $ map combine [...]`.
    vcat_render(sections)
}

// Faithful port of Haskell `prettyEqStore` (EquationStore.hs:566-586).
// Emits a leading `CONTRADICTORY` line when `eqsIsFalse`, then a `subst:`
// section (`prettySubst (text.show) (text.show)`, i.e. `t <~ {vars}`
// lines) and a `conj:` section whose disjuncts are `N.` followed by
// `numbered'` of `∃ vars. a = b ∧ ...`.
//
// Known divergences (UI-only diagnostic pane, not raw `--prove` output):
//   * terms rendered as flat `Doc::text` atoms (no Doc term printer in
//     this crate), so over-wide terms aren't re-wrapped;
//   * the `prettySubst` grouping uses Rust's derived `Ord` on terms for
//     the `equivClasses` map iteration order, which may differ from
//     Haskell's `Ord (VTerm c v)` in edge cases.
fn pretty_eq_store(sys: &System) -> String {
    let eq = &sys.eq_store;
    let mut lines: Vec<Doc> = Vec::new();

    if eq.is_false() {
        lines.push(Doc::text("CONTRADICTORY"));
    } else {
        // HS prepends `emptyDoc`; vcat drops it.
        lines.push(Doc::empty());
    }

    // subst: vcat (prettySubst (text.show) (text.show) substFree)
    lines.push(combine("subst", vcat_doc(pretty_subst_free(&eq.subst))));

    // conj: vcat (map ppDisj disjs)
    let disjs: Vec<Doc> = eq.conj.iter().map(pp_disj).collect();
    lines.push(combine("conj", vcat_doc(disjs)));

    vcat_render(lines)
}

// HS `ppDisj (idx, substs) = text (show idx ++ ".") <-> numbered' conjs`
// where `conjs = map ppSubst (S.toList substs)`.
fn pp_disj(d: &crate::tools::equation_store::EqDisj) -> Doc {
    let conjs: Vec<Doc> = d.substs.iter().map(pp_subst_vfresh).collect();
    Doc::text(format!("{}.", d.split_id.0)).beside_sp(numbered_prime(conjs))
}

// HS `ppSubst subst = sep [ hsep (opExists : map prettyLVar (varsRangeVFresh subst)) <> opDot
//                         , nest 2 $ fsep $ intersperse opLAnd $ map ppEq (substToListVFresh subst) ]`
fn pp_subst_vfresh(subst: &crate::tools::equation_store::LNSubstVFresh) -> Doc {
    use crate::pretty_hpj::{hsep, sep};
    // hsep (opExists : map prettyLVar vars) <> opDot
    // opExists renders "∃ " (trailing space) as a single operator token.
    let mut quant_parts: Vec<Doc> = vec![Doc::text("\u{2203} ")]; // "∃ "
    for v in subst.vars_range() {
        quant_parts.push(Doc::text(lvar_to_string(&v)));
    }
    let quant = hsep(quant_parts).beside(Doc::text(".")); // opDot

    // fsep $ intersperse opLAnd $ map ppEq (substToListVFresh subst)
    let eqs: Vec<Doc> = subst
        .to_list()
        .into_iter()
        .map(|(v, t)| pp_eq(&v, &t))
        .collect();
    let body = fsep(intersperse(Doc::text("\u{2227}"), eqs)).nest(2); // ∧ (opLAnd)

    sep(vec![quant, body])
}

// HS `ppEq (a,b) = prettyNTerm (lit (Var a)) $$ nest 6 (opEqual <-> prettyNTerm b)`
fn pp_eq(a: &tamarin_term::lterm::LVar, b: &tamarin_term::vterm::VTerm<tamarin_term::lterm::Name, tamarin_term::lterm::LVar>) -> Doc {
    Doc::text(lvar_to_string(a)).above(
        Doc::text("=") // opEqual
            .beside_sp(Doc::text(pretty_lnterm(b)))
            .nest(6),
    )
}

// HS `prettySubst (text.show) (text.show) subst` (SubstVFree.hs:314-320):
//   map pp . M.toList . equivClasses . substToList
//   pp (t, vs) = prettyTerm t <-> " <~ {" <> fsep (punctuate comma (map ppVar vs)) <> "}"
// `equivClasses` groups vars by their mapped term; the map is keyed/ordered
// by the term, and each var-set is ordered by `Ord v`.
fn pretty_subst_free(subst: &crate::tools::equation_store::LNSubst) -> Vec<Doc> {
    use std::collections::BTreeMap;
    // Group by mapped term, preserving term Ord via BTreeMap; var-sets
    // sorted by LVar Ord.
    let mut groups: BTreeMap<
        tamarin_term::vterm::VTerm<tamarin_term::lterm::Name, tamarin_term::lterm::LVar>,
        std::collections::BTreeSet<tamarin_term::lterm::LVar>,
    > = BTreeMap::new();
    for (v, t) in subst.to_list() {
        groups.entry(t).or_default().insert(v);
    }
    groups
        .into_iter()
        .map(|(t, vs)| {
            let vars: Vec<Doc> = vs.iter().map(|v| Doc::text(lvar_to_string(v))).collect();
            // prettyTerm t <-> " <~ {" <> fsep (punctuate comma vars) <> "}"
            Doc::text(pretty_lnterm(&t))
                .beside_sp(Doc::text(" <~ {")) // operator_ " <~ {"
                .beside(fsep(punctuate(Doc::text(","), vars)))
                .beside(Doc::text("}"))
        })
        .collect()
}

// HS `intersperse sep xs`.
fn intersperse(sep: Doc, xs: Vec<Doc>) -> Vec<Doc> {
    let mut out = Vec::with_capacity(xs.len().saturating_mul(2).saturating_sub(1));
    for (i, x) in xs.into_iter().enumerate() {
        if i > 0 {
            out.push(sep.clone());
        }
        out.push(x);
    }
    out
}

// HS `vcat ds` of Docs, then render to a String.
fn vcat_render(ds: Vec<Doc>) -> String {
    vcat_doc(ds).render()
}

// HS `vcat ds`: fold with `$$` (above). Empty operands collapse, matching
// HughesPJ's `vcat = foldr (\p q -> Above p False q) empty`.
fn vcat_doc(ds: Vec<Doc>) -> Doc {
    crate::pretty_hpj::vcat(ds)
}

// ---------------------------------------------------------------------
// goals
// ---------------------------------------------------------------------

// Mirrors Haskell `prettyGoals` (System.hs:1735-1753):
//   (goal, status) <- M.toList sGoals          -- Goal-Ord iteration
//   guard (solved == gsSolved status)
//   prettyGoal goal <-> lineComment_
//       ("nr: " ++ show nr ++ sourceRule ++ loopBreaker ++ show useful)
// where `sourceRule = " (from rule "++getRuleName ru++")"` for the goal's
// node rule (goalRule), `loopBreaker` from `gsLoopBreaker`, and `useful`
// the KU-usefulness classification.  `show useful` wraps the annotation in
// literal double-quotes (HS `Show String`).  Goals are rendered through the
// SAME faithful `prettyGoal` Doc the `--prove` proof tree uses
// (`solve_goal_to_doc`), so fact spacing (`!KU( ~ltk )`) and LVar dots match.
fn pretty_goals(sys: &System, want_solved: bool) -> String {
    // `M.toList sGoals` yields Goal-Ord; RS stores goals in a Vec (creation
    // order), so sort by the solver's `goal_cmp` before rendering.
    let mut ordered: Vec<_> = sys.goals.iter()
        .filter(|(_, st)| st.solved == want_solved)
        .collect();
    ordered.sort_by(|a, b|
        crate::constraint::solver::goals::goal_cmp(&a.0, &b.0));
    let mut lines: Vec<String> = Vec::with_capacity(ordered.len());
    for (g, st) in ordered {
        // sourceRule = HS `goalRule sys goal` → `nodeRuleSafe (goalNodeId g)`.
        // `goalNodeId` is the node of a Premise/Action goal; other goals have
        // none (→ no sourceRule).
        let source_rule = match g {
            Goal::Action(i, _) | Goal::Premise((i, _), _) => sys
                .node_rule_safe(i)
                .map(|ru| format!(" (from rule {})", crate::rule::rule_name_string(ru)))
                .unwrap_or_default(),
            _ => String::new(),
        };
        let loop_breaker = if st.looping { " (loop breaker)" } else { "" };
        // `show useful` — HS wraps the annotation string in literal quotes.
        let useful = crate::constraint::solver::goals::goal_useful_annotation(
            g, st.looping, sys);
        // HS `prettyGoal goal <-> lineComment_ (...)` — the `<->`/`<+>`
        // operators each insert a single space (goal ` ` `//` ` ` text).
        lines.push(format!(
            "{} // nr: {}{}{}\"{}\"",
            crate::pretty_theory::solve_goal_to_doc(g).render(),
            st.nr, source_rule, loop_breaker, useful,
        ));
    }
    // HS `vsep = foldr ($--$)`, and `$--$` inserts a BLANK line between
    // adjacent goals (`d1 $-$ text "" $-$ d2`) — i.e. a double newline.
    lines.join("\n\n")
}

// ---------------------------------------------------------------------
// source kind
// ---------------------------------------------------------------------

fn pretty_source_kind(sk: Option<SourceKind>) -> String {
    // Matches Haskell `instance Show SourceKind` (System.hs:346-348):
    //   show RawSource     = "raw"
    //   show RefinedSource = "refined"
    // The Haskell field is non-optional; the `None` arm is a Rust-only
    // fallback for an unset source kind.
    match sk {
        None => "raw".to_string(),
        Some(SourceKind::RawSources) => "raw".to_string(),
        Some(SourceKind::RefinedSources) => "refined".to_string(),
    }
}

// ---------------------------------------------------------------------
// LNFact / RuleACInst rendering
// ---------------------------------------------------------------------

/// Pretty-print an `LNFact` exactly as Haskell `prettyLNFact` /
/// `prettyFact` (Fact.hs:537-552): `showFactTag tag` (with the persistent
/// `!` prefix), the term list in parentheses (always emitted, even for
/// zero-arity facts, matching `nestShort'`), and a trailing `[...]`
/// annotation block. Used by the proof pretty-printer here and by the
/// web DOT renderer (`tamarin-server`'s `dot::format_fact`).
pub fn pretty_fact(fa: &LNFact) -> String {
    use crate::fact::{fact_tag_multiplicity, FactAnnotation, Multiplicity};
    // Matches Haskell `showFactTag` (Fact.hs:519-523): the `!` prefix is
    // applied to any tag whose `factTagMultiplicity` is `Persistent`,
    // which includes KU/KD as well as persistent proto facts.
    let prefix = if fact_tag_multiplicity(&fa.tag) == Multiplicity::Persistent {
        "!"
    } else {
        ""
    };
    let name = fact_tag_name(&fa.tag);
    let args: Vec<String> = fa.terms.iter().map(pretty_lnterm).collect();
    let base = format!("{}{}({})", prefix, name, args.join(", "));
    // Matches Haskell `ppAnn` (Fact.hs:543-545): when annotations are
    // present, append `[a1, a2]` using `showFactAnnotation` for each.
    if fa.annotations.is_empty() {
        base
    } else {
        let anns: Vec<&str> = fa
            .annotations
            .iter()
            .map(|a| match a {
                FactAnnotation::SolveFirst => "+",
                FactAnnotation::SolveLast => "-",
                FactAnnotation::NoSources => "no_precomp",
            })
            .collect();
        format!("{}[{}]", base, anns.join(", "))
    }
}

fn pretty_node_id(nid: &NodeId) -> String {
    let mut s = String::new();
    pp_lvar(nid, &mut s);
    s
}

fn lvar_to_string(v: &tamarin_term::lterm::LVar) -> String {
    let mut s = String::new();
    pp_lvar(v, &mut s);
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraint::system::System;

    #[test]
    fn empty_system_renders_each_section() {
        let s = System::default();
        let out = pretty_non_graph_system(&s);
        for h in &[
            "last:", "formulas:", "subterms:", "equations:", "lemmas:",
            "allowed cases:", "solved formulas:", "unsolved constraints:",
            "solved constraints:",
        ] {
            assert!(out.contains(h), "missing header {} in:\n{}", h, out);
        }
        assert!(out.contains("none"));
    }

    #[test]
    fn subterm_store_numbered_sections_and_contradictory_header() {
        use crate::tools::subterm_store::{SubtermConstraint, SubtermStore};
        use tamarin_term::lterm::{LSort, LVar};
        use tamarin_term::vterm::var_term;

        let v = |n: &str, s: LSort| var_term(LVar::new(n, s, 0));
        let st = SubtermStore {
            subterms: vec![SubtermConstraint {
                small: v("x", LSort::Msg),
                big: v("y", LSort::Msg),
                propagated: false,
            }],
            solved_subterms: vec![SubtermConstraint {
                small: v("a", LSort::Msg),
                big: v("b", LSort::Msg),
                propagated: false,
            }],
            contradictory: true,
            neg_subterms: vec![(v("p", LSort::Msg), v("q", LSort::Msg))],
            old_neg_subterms: vec![],
        };
        let sys = System { subterm_store: std::sync::Arc::new(st), ..Default::default() };
        let out = pretty_subterm_store(&sys);
        // Contradictory header + all three numbered keyword sections.
        assert!(out.contains("Contradictory: yes"), "got:\n{out}");
        assert!(out.contains("Negative Subterms:"), "got:\n{out}");
        assert!(out.contains("Subterms:"), "got:\n{out}");
        assert!(out.contains("Solved Subterms:"), "got:\n{out}");
        // numbered' uses "1. " prefixes and the ⊏ operator.
        assert!(out.contains("1. "), "got:\n{out}");
        assert!(out.contains('\u{228F}'), "got:\n{out}");
    }

    #[test]
    fn eq_store_contradictory_and_sections() {
        use crate::tools::equation_store::{EqDisj, EquationStore, SplitId};

        let mut eq = EquationStore::empty();
        // An empty disjunction makes the store contradictory.
        eq.conj.push(EqDisj { split_id: SplitId(0), substs: vec![] });
        let sys = System { eq_store: std::sync::Arc::new(eq), ..Default::default() };
        let out = pretty_eq_store(&sys);
        assert!(out.contains("CONTRADICTORY"), "got:\n{out}");
        assert!(out.contains("subst:"), "got:\n{out}");
        assert!(out.contains("conj:"), "got:\n{out}");
        // The disjunction index is rendered with a trailing dot.
        assert!(out.contains("0."), "got:\n{out}");
    }
}
