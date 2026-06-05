//! Theory pretty-printer.  Port of Haskell's `prettyClosedTheory`
//! (ClosedTheory.hs:382) — top-level renderer for `--prove` output.
//!
//! Goal: byte-identical output to Haskell on the analyzed theory body.
//! The output layout:
//!
//! ```text
//! theory <name>
//!
//! begin
//!
//! // Function signature and definition of the equational theory E
//!
//! builtins: ...     (if any)
//! functions: ...
//! equations: ...
//!
//! rule (modulo E) <name>:
//!    [ <prems> ] --[ <acts> ]-> [ <concs> ]
//!
//!   /* has exactly the trivial AC variant */
//!
//! restriction <name>:
//!   "<formula>"
//!
//! lemma <name> [attrs]:
//!   <quant> "<formula>"
//! /*
//! guarded formula characterizing ...:
//! "<gformula>"
//! */
//! <proof body>
//!
//! /* All wellformedness checks were successful. */ (or warning block)
//!
//! /*
//! Generated from:
//! Tamarin version ...
//! Maude version ...
//! Git revision: ...
//! Compiled at: ...
//! */
//!
//! end
//! ```
//!
//! Each top-level item is separated by a blank line (HS uses `vsep`).

use crate::pretty_formula as pf;
use crate::theory::Theory;
use tamarin_parser::ast as p;

/// Build info passed in from the prover binary so the Generated-from
/// block reflects compile-time facts.
#[derive(Debug, Clone)]
pub struct BuildInfo {
    pub tamarin_version: String,
    pub maude_version: String,
    pub git_revision: String,
    pub git_branch: String,
    pub compiled_at: String,
}

/// Per-lemma proof result produced by the prover.  When `proof_body`
/// is `None` (e.g. when the user did not pass `--prove`), the lemma's
/// stored skeleton (`by sorry`) is rendered instead.
#[derive(Debug, Clone)]
pub struct ProvedLemma {
    pub name: String,
    /// Pre-rendered HS-faithful proof body (lines of text, no leading
    /// blank line, no trailing blank line).  See `pretty_proof_body`.
    pub proof_body: Option<String>,
}

/// Render the analyzed theory in HS's `prettyClosedTheory` shape.
pub fn pretty_closed_theory(
    parsed: &p::Theory,
    elaborated: &Theory,
    proved: &[ProvedLemma],
    wf_block: &str,
    build: &BuildInfo,
) -> String {
    let mut out = String::new();

    // theory <name>\n\nbegin\n\n
    out.push_str("theory ");
    out.push_str(&elaborated.name);
    out.push_str("\n\nbegin\n\n");

    // // Function signature and definition of the equational theory E\n\n
    out.push_str("// Function signature and definition of the equational theory E\n\n");

    // builtins / functions / equations — render_signature already ends
    // with a trailing '\n' after each line so we don't add another here.
    out.push_str(&render_signature(&elaborated.signature.maude_sig));

    // HS `prettyTheory` (TheoryObject.hs:741-751) emits, between the
    // signature and the cache block:
    //   - `heuristic: <ranking>` line (only if non-empty heuristic)
    //   - `ppCache` (the "looping facts with injective instances" comment).
    // Mirror that here.
    if !elaborated.heuristic.is_empty() {
        out.push('\n');
        out.push_str("heuristic: ");
        out.push_str(&elaborated.heuristic.join(""));
        out.push('\n');
    }
    let inj_block = render_injective_fact_insts(elaborated);
    if !inj_block.is_empty() {
        out.push('\n');
        out.push_str(&inj_block);
        out.push('\n');
    }

    // Iterate parsed.items, mapping to elaborated entities where needed.
    // HS preserves source order via vsep over `thyItems`.  Each item is
    // separated from the previous block by a blank line.
    //
    // HS-parallel: `lib/theory/src/TheoryObject.hs:744,752`
    //   `parMap rdeepseq ppItem (theoryItems thy)` (and `OpenTheory.hs:921,933`).
    // HS evaluates each item's `Doc` in parallel; the final `vsep`
    // (sequential concatenation) preserves source order.  We mirror via
    // rayon `par_iter().collect()` — parallel per-item render, sequential
    // string append.
    use rayon::prelude::*;
    let rendered: Vec<Option<String>> = parsed.items.par_iter()
        .map(|item| render_parsed_item(item, 0, parsed, elaborated, proved))
        .collect();
    for b in rendered.into_iter().flatten() {
        out.push('\n');
        out.push_str(&b);
        out.push('\n');
    }

    // Wellformedness block (already preformatted: either the "all
    // successful" line or the WARNING /* ... */ block).
    out.push('\n');
    out.push_str(wf_block);
    out.push('\n');

    // Generated-from block.
    out.push('\n');
    out.push_str(&render_generated_from(build));
    out.push('\n');

    // end
    out.push_str("\nend\n");

    out
}

/// Render HS `ppInjectiveFactInsts` (ClosedTheory.hs:413-418):
///
/// ```text
/// /* looping facts with injective instances: T1/n1, T2/n2, ... */
/// ```
///
/// Emits the empty string when no fact tags are injective.  Computes
/// the set on demand from the elaborated rules + reducible function
/// symbols — same call site as `ProofContext::new`
/// (`constraint/solver/context.rs:493-495`).
fn render_injective_fact_insts(elab: &Theory) -> String {
    use crate::fact::{FactTag, Multiplicity};
    let proto_rules: Vec<crate::rule::ProtoRuleE> = elab.rules()
        .map(|r| r.rule.clone())
        .collect();
    let tags = crate::tools::injective_fact_instances::simple_injective_fact_instances(
        &proto_rules,
        &elab.signature.maude_sig.reducible_fun_syms,
    );
    if tags.is_empty() { return String::new(); }
    // HS `showFactTagArity` (Fact.hs:526): persistent `!`-prefix + name
    // + `/` + arity.
    let label = |tag: &FactTag| -> String {
        let prefix = match tag {
            FactTag::Proto(Multiplicity::Persistent, _, _) => "!",
            _ => "",
        };
        format!("{}{}/{}",
            prefix,
            crate::fact::fact_tag_name(tag),
            crate::fact::fact_tag_arity(tag))
    };
    let parts: Vec<String> = tags.iter().map(|(t, _)| label(t)).collect();
    format!(
        "/* looping facts with injective instances: {} */",
        parts.join(", "),
    )
}

// =============================================================================
// Signature
// =============================================================================

fn render_signature(sig: &tamarin_term::maude_sig::MaudeSig) -> String {
    let mut out = String::new();

    // builtins: ...  (only if any enabled)
    let mut builtins: Vec<&str> = Vec::new();
    if sig.enable_dh { builtins.push("diffie-hellman"); }
    if sig.enable_bp { builtins.push("bilinear-pairing"); }
    if sig.enable_mset { builtins.push("multiset"); }
    if sig.enable_nat { builtins.push("natural-numbers"); }
    if sig.enable_xor { builtins.push("xor"); }
    if !builtins.is_empty() {
        out.push_str("builtins: ");
        out.push_str(&builtins.join(", "));
        out.push('\n');
    }

    // functions: ...
    let funs = render_fun_syms(sig);
    if !funs.is_empty() {
        out.push_str(&wrap_with_lead("functions:", &funs));
        out.push('\n');
    }

    // equations: ...
    let eqs = render_equations(sig);
    if !eqs.is_empty() {
        let key = if sig.eq_convergent { "equations [convergent]:" } else { "equations:" };
        // HS uses `sep [hdr, nest 2 (punctuate comma ds)]` for the
        // equations list — yields `hdr\n    eq1,\n    eq2,...` when
        // multiple equations.
        out.push_str(&sep_block_with_lead(key, &eqs));
        out.push('\n');
    }

    out
}

/// Render the function symbol list, sorted alphabetically by name (HS
/// uses `S.toList` over a Set ordered by the same key).
fn render_fun_syms(sig: &tamarin_term::maude_sig::MaudeSig) -> Vec<String> {
    use tamarin_term::function_symbols::{Constructability, Privacy};
    let mut items: Vec<(String, String)> = sig.st_fun_syms.iter().map(|sym| {
        let name = String::from_utf8_lossy(&sym.name).to_string();
        let arity = sym.arity;
        let attr = match (sym.privacy, sym.constructability) {
            (Privacy::Public, Constructability::Constructor) => "",
            (Privacy::Public, Constructability::Destructor) => "[destructor]",
            (Privacy::Private, Constructability::Constructor) => "[private,constructor]",
            (Privacy::Private, Constructability::Destructor) => "[private,destructor]",
        };
        let rendered = format!("{}/{}{}", name, arity, attr);
        (name, rendered)
    }).collect();
    items.sort_by(|a, b| a.0.cmp(&b.0));
    items.into_iter().map(|(_, s)| s).collect()
}

/// Render the equation list.  Each `CtxtStRule` has an LHS term and an
/// RHS term (after reading positions/term out of `StRhs`).  HS renders
/// `lhs = rhs`, sorted by some key (we use the `BTreeSet`'s natural
/// order which mirrors HS's `S.toList`).
fn render_equations(sig: &tamarin_term::maude_sig::MaudeSig) -> Vec<String> {
    let mut items: Vec<String> = Vec::new();
    for r in &sig.st_rules {
        let lhs = render_lnterm(&r.lhs);
        let rhs = render_lnterm(&r.rhs.term);
        items.push(format!("{} = {}", lhs, rhs));
    }
    // Sort by LHS string for stable HS-like ordering.
    items.sort();
    items
}

/// HS's `ppNonEmptyList` with `keyword <-> fsep . punctuate comma`:
/// when the line fits, emit `<lead> a, b, c`. When it overflows the
/// default 80-col width, wrap with continuation indent equal to
/// `length lead + 1`.  HS uses `text` width 80 (Pretty.hs default).
fn wrap_with_lead(lead: &str, items: &[String]) -> String {
    // Empty: emit nothing.
    if items.is_empty() { return String::new(); }
    // HS uses `defaultStyle = Style { lineLength = 76, .. }` (Pretty.hs)
    // for `fsep` / `sep` wrapping.
    const WIDTH: usize = 76;
    let lead_len = lead.chars().count();
    let cont_indent: String = " ".repeat(lead_len + 1);
    // First try: single line `lead a, b, c`.
    let joined = items.join(", ");
    let single = format!("{} {}", lead, joined);
    if single.chars().count() <= WIDTH {
        return single;
    }
    // Multi-line: greedy fill respecting WIDTH.  HS's `fsep` packs
    // tokens onto each line greedily.
    let mut out = String::new();
    out.push_str(lead);
    let mut cur_col = lead_len;
    for (i, it) in items.iter().enumerate() {
        let tok = if i + 1 < items.len() {
            format!("{},", it)
        } else {
            it.clone()
        };
        let need = tok.chars().count() + 1; // +1 for leading space
        if cur_col + need > WIDTH {
            // Wrap.
            out.push('\n');
            out.push_str(&cont_indent);
            out.push_str(&tok);
            cur_col = cont_indent.chars().count() + tok.chars().count();
        } else {
            out.push(' ');
            out.push_str(&tok);
            cur_col += need;
        }
    }
    out
}

/// `sep`-style layout matching HS's `sep [hdr, nest 2 (punctuate comma ds)]`:
/// try a single line `<lead> a, b, c`; if it overflows the 76-col
/// default-style width, fall back to a vertical layout
/// `<lead>\n    a,\n    b,\n    ...,\n    z`.
fn sep_block_with_lead(lead: &str, items: &[String]) -> String {
    if items.is_empty() { return String::new(); }
    const WIDTH: usize = 76;
    let joined = items.join(", ");
    let single = format!("{} {}", lead, joined);
    if single.chars().count() <= WIDTH {
        return single;
    }
    let mut out = String::new();
    out.push_str(lead);
    let indent = "    ";
    for (i, it) in items.iter().enumerate() {
        out.push('\n');
        out.push_str(indent);
        out.push_str(it);
        if i + 1 < items.len() {
            out.push(',');
        }
    }
    out
}

// =============================================================================
// Item dispatch
// =============================================================================

fn render_parsed_item(
    item: &p::TheoryItem,
    _idx: usize,
    _parsed: &p::Theory,
    elab: &Theory,
    proved: &[ProvedLemma],
) -> Option<String> {
    use p::TheoryItem::*;
    match item {
        Builtins(_) | Functions(_) | Equations { .. } | Options(_) | Heuristic(_) | Tactic(_) => {
            // These are absorbed into the signature/configuration headers.
            None
        }
        Rule(r) => Some(render_rule(r, elab)),
        IntrRule(_) => None,
        Lemma(l) => Some(render_parsed_lemma(l, proved)),
        Restriction(r) => Some(render_parsed_restriction(r)),
        Predicates(_) | Macros(_) => {
            // TODO: render predicates and macros (port HS prettyPredicate
            // and prettyMacros).  Not exercised by the simple test
            // theories yet — leave empty so output is well-formed.
            None
        }
        _ => None,
    }
}

// =============================================================================
// Rule
// =============================================================================

fn render_rule(parsed_rule: &p::Rule, elab: &Theory) -> String {
    let name = &parsed_rule.name;
    let mut out = String::new();
    out.push_str("rule (modulo E) ");
    out.push_str(name);
    out.push_str(":\n");
    // Desugar `let x = t in ...` bindings before rendering — HS does
    // this via `applyMacroInProtoRule`/`expandRuleLetBlock` so the
    // emitted rule contains no bound names from the `let` block.
    // Mirrors `apply_let_block` (`elaborate.rs:678`); same fix pattern
    // as the deriv-check (commit 3b0202bb).  HS site:
    // `lib/theory/src/TheoryObject.hs::prettyTheory` → `prettyRule` chain
    // which operates on the post-`applyMacroInProtoRule` rule.
    let desugared = crate::elaborate::apply_let_block(parsed_rule);
    let parsed_rule = &desugared;
    out.push_str(&render_rule_body(
        &parsed_rule.premises,
        &parsed_rule.actions,
        &parsed_rule.conclusions,
    ));

    // Look up the elaborated rule by name to decide between
    // "trivial AC variant" and the full `/* rule (modulo AC) ... */`
    // block.  HS-faithful: matches `prettyClosedProtoRule`
    // (ClosedTheory.hs:332-363).
    let elab_rule = elab.rules().find(|r| r.name() == name);
    let nontrivial = elab_rule
        .map(|r| !r.variant_substs.is_empty() && r.abstracted_rule.is_some()
            && r.variant_substs.iter().any(|s| !s.is_empty()))
        .unwrap_or(false);

    if !nontrivial {
        out.push_str("\n\n  /* has exactly the trivial AC variant */");
    } else if let Some(r) = elab_rule {
        out.push_str("\n\n");
        out.push_str(&render_ac_variants_block(name, r));
    }
    out
}

/// Render `[ prems ] --[ acts ]-> [ concs ]` body shared between the
/// modulo-E and modulo-AC renderers.  Tries single-line layout first;
/// when it overflows the 76-col threshold, wraps each clause to its own
/// line as HS's `prettyRuleRestrGen` does via `sep`.
fn render_rule_body(prems: &[p::Fact], acts: &[p::Fact], concs: &[p::Fact]) -> String {
    render_rule_body_at(prems, acts, concs, 3)
}

/// Render rule body at column `indent`.  Used by the AC variant block
/// (indent=5) and the top-level rule (indent=3).  The brackets, arrow,
/// and concs all sit at column `indent` when wrapped.
fn render_rule_body_at(prems: &[p::Fact], acts: &[p::Fact], concs: &[p::Fact], indent: usize) -> String {
    let pad = " ".repeat(indent);
    let pad_arrow = " ".repeat(indent.saturating_sub(1));
    // Single-line trial: render brackets inline (force no wrap by trying
    // a wide budget first; if any internal wrap happened the multi-line
    // path will catch it).
    let prems_inline = render_fact_brackets_inline(prems);
    let concs_inline = render_fact_brackets_inline(concs);
    let acts_inline_body = acts.iter().map(render_fact).collect::<Vec<_>>().join(", ");
    let single = if acts.is_empty() {
        format!("{}{} --> {}", pad, prems_inline, concs_inline)
    } else {
        format!("{}{} --[ {} ]-> {}", pad, prems_inline, acts_inline_body, concs_inline)
    };
    if !single.contains('\n') && single.chars().count() <= indent + RIBBON
        && !prems_inline.is_empty() && !concs_inline.is_empty()
    {
        return single;
    }
    // Multi-line clause layout (HS `sep [prems, arrow, concs]`).  Each
    // clause is rendered at column `indent` with internal wrap allowed.
    let prems_str = render_fact_brackets_at(prems, indent);
    let concs_str = render_fact_brackets_at(concs, indent);
    let mut out = String::new();
    out.push_str(&pad);
    out.push_str(&prems_str);
    out.push('\n');
    if acts.is_empty() {
        out.push_str(&pad_arrow);
        out.push_str("-->");
    } else {
        let acts_inline = format!("{}--[ {} ]->", pad_arrow, acts_inline_body);
        if !acts_inline.contains('\n') && acts_inline.chars().count() <= indent + RIBBON {
            out.push_str(&acts_inline);
        } else {
            // Multi-line action list — HS `fsep [text "--[", ppList acts,
            // text "]->"]` puts `--[` and `]->` on their own lines with
            // packed acts in between.  We match the previous shape: each
            // act on its own line under the `--[`, comma-suffixed.
            out.push_str(&pad_arrow);
            out.push_str("--[\n");
            for (i, a) in acts.iter().enumerate() {
                out.push_str(&pad_arrow);
                out.push_str(&render_fact_at(a, indent.saturating_sub(1)));
                if i + 1 < acts.len() { out.push(','); }
                out.push('\n');
            }
            out.push_str(&pad_arrow);
            out.push_str("]->");
        }
    }
    out.push('\n');
    out.push_str(&pad);
    out.push_str(&concs_str);
    out
}

/// Inline-only bracket list (no wrap).  Used to check single-line fit
/// of the rule body before deciding to wrap the inner brackets.
fn render_fact_brackets_inline(facts: &[p::Fact]) -> String {
    if facts.is_empty() {
        return "[ ]".to_string();
    }
    let mut s = String::from("[ ");
    for (i, f) in facts.iter().enumerate() {
        if i > 0 { s.push_str(", "); }
        // Use the indent-unaware path so each fact is also inline.
        s.push_str(&render_fact_inline(f));
    }
    s.push_str(" ]");
    s
}

fn render_fact_inline(fa: &p::Fact) -> String {
    let mut s = String::new();
    if fa.persistent { s.push('!'); }
    s.push_str(&fa.name);
    s.push_str("( ");
    for (i, t) in fa.args.iter().enumerate() {
        if i > 0 { s.push_str(", "); }
        s.push_str(&pf::pretty_term(t));
    }
    if fa.args.is_empty() {
        // Already opened `( `; just close with ` )` to give `Name(  )`?
        // No — match `Name( )` single-space form.  Pop the trailing
        // space and emit `)` directly.
        s.pop();
        s.push_str(" )");
    } else {
        s.push_str(" )");
    }
    s
}

/// Render the HS `/* rule (modulo AC) <name>: ... variants (modulo AC)
/// 1. ... */` comment block.  Mirrors `prettyClosedProtoRule`'s
/// `multiComment $ prettyProtoRuleAC ruAC` branch (ClosedTheory.hs:354).
fn render_ac_variants_block(name: &str, rule: &crate::theory::OpenProtoRule) -> String {
    let mut s = String::new();
    s.push_str("  /*\n");
    s.push_str(&format!("  rule (modulo AC) {}:\n", name));
    // Body of the abstracted rule.  Use the abstracted version when
    // available; fall back to the original facts.
    let prems = lnfacts_to_parser(&rule.abstracted_rule.as_ref()
        .map(|r| r.premises.clone()).unwrap_or_default());
    let acts = lnfacts_to_parser(&rule.abstracted_rule.as_ref()
        .map(|r| r.actions.clone()).unwrap_or_default());
    let concs = lnfacts_to_parser(&rule.abstracted_rule.as_ref()
        .map(|r| r.conclusions.clone()).unwrap_or_default());
    // Each line of the rule body needs an extra leading 2-space indent
    // (we're inside the comment block, which already has 2 spaces).
    let body = render_rule_body(&prems, &acts, &concs);
    for line in body.split('\n') {
        s.push_str("  ");
        s.push_str(line);
        s.push('\n');
    }
    s.push_str("    variants (modulo AC)\n");
    for (i, subst) in rule.variant_substs.iter().enumerate() {
        if i > 0 { s.push_str("    \n"); }
        s.push_str(&render_variant_subst(i + 1, subst));
    }
    s.push_str("  */");
    s
}

/// Render one entry of `prettyDisjLNSubstsVFresh`
/// (SubstVFresh.hs:223-229): the variant's number, then each domain var
/// followed by `= <range>`.  HS aligns the `=` at column 6 from the
/// entry's local origin when the var name is short, otherwise wraps to
/// a new line.
fn render_variant_subst(n: usize, subst: &tamarin_term::subst_vfresh::LNSubstVFresh) -> String {
    let mut s = String::new();
    let bindings = subst.to_list();
    for (i, (v, t)) in bindings.iter().enumerate() {
        let var_str = render_lvar(v);
        let term_str = render_lnterm(t);
        let prefix = if i == 0 { format!("    {}. ", n) } else { "       ".to_string() };
        // HS uses `prettyNTerm v $$ nest 6 (text "=" <-> prettyNTerm b)`:
        // if the var name fits in 5 chars, put `= term` at col 6 (within
        // the entry).  Otherwise wrap.
        if var_str.chars().count() <= 5 {
            // `var<padded to 5><sp>= term`
            let padded = format!("{:<5}", var_str);
            s.push_str(&prefix);
            s.push_str(&padded);
            s.push_str(" = ");
            s.push_str(&term_str);
            s.push('\n');
        } else {
            s.push_str(&prefix);
            s.push_str(&var_str);
            s.push('\n');
            // Continuation line at col 7 with `      = term`.
            let cont = if i == 0 { "             = " } else { "             = " };
            s.push_str(cont);
            s.push_str(&term_str);
            s.push('\n');
        }
    }
    s
}

fn render_lvar(v: &tamarin_term::lterm::LVar) -> String {
    use tamarin_term::lterm::LSort;
    let pre = match v.sort {
        LSort::Pub => "$",
        LSort::Fresh => "~",
        LSort::Node => "#",
        LSort::Nat => "%",
        LSort::Msg => "",
    };
    if v.idx == 0 { format!("{}{}", pre, v.name) }
    else { format!("{}{}.{}", pre, v.name, v.idx) }
}

/// Convert LNFacts (post-elaboration) to parser-AST Facts so we can
/// reuse `render_fact`.  Drops fact annotations.
fn lnfacts_to_parser(facts: &[crate::fact::LNFact]) -> Vec<p::Fact> {
    facts.iter().map(lnfact_to_parser).collect()
}

fn lnfact_to_parser(fa: &crate::fact::LNFact) -> p::Fact {
    use crate::fact::FactTag;
    let (name, persistent) = match &fa.tag {
        FactTag::Proto(crate::fact::Multiplicity::Persistent, n, _) => (n.clone(), true),
        FactTag::Proto(_, n, _) => (n.clone(), false),
        FactTag::Fresh => ("Fr".to_string(), false),
        FactTag::In => ("In".to_string(), false),
        FactTag::Out => ("Out".to_string(), false),
        FactTag::Ku => ("KU".to_string(), false),
        FactTag::Kd => ("KD".to_string(), false),
        FactTag::Ded => ("Ded".to_string(), false),
        FactTag::Term => ("Term".to_string(), false),
    };
    p::Fact {
        persistent,
        name,
        args: fa.terms.iter().map(lnterm_to_parser).collect(),
        annotations: Vec::new(),
    }
}

fn lnterm_to_parser(t: &tamarin_term::lterm::LNTerm) -> p::Term {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    use tamarin_term::lterm::LSort;
    match t {
        Term::Lit(Lit::Var(v)) => {
            let sort = match v.sort {
                LSort::Pub => p::SortHint::Pub,
                LSort::Fresh => p::SortHint::Fresh,
                LSort::Node => p::SortHint::Node,
                LSort::Nat => p::SortHint::Nat,
                LSort::Msg => p::SortHint::Msg,
            };
            p::Term::Var(p::VarSpec {
                name: v.name.clone(),
                idx: v.idx,
                sort,
                typ: None,
            })
        }
        Term::Lit(Lit::Con(n)) => {
            use tamarin_term::lterm::NameTag;
            match n.tag {
                NameTag::Pub => p::Term::PubLit(n.id.0.clone()),
                NameTag::Fresh => p::Term::FreshLit(n.id.0.clone()),
                NameTag::Nat => p::Term::NatLit(n.id.0.clone()),
                NameTag::Node => p::Term::PubLit(n.id.0.clone()),
            }
        }
        Term::App(FunSym::NoEq(sym), args) => {
            let name = String::from_utf8_lossy(&sym.name).to_string();
            // `exp` is the DH exponentiation infix operator — HS
            // `prettyTerm` (Term/Term.hs:274) renders `exp(a, b)` as `a^b`.
            // Surface as `p::Term::BinOp(Exp, ..)` so `pp_term`'s special
            // case applies.
            if name == "exp" && args.len() == 2 {
                return p::Term::BinOp(
                    p::BinOp::Exp,
                    Box::new(lnterm_to_parser(&args[0])),
                    Box::new(lnterm_to_parser(&args[1])),
                );
            }
            // `pair` chains flatten to n-ary tuple (HS `prettyTerm` at
            // Term/Term.hs:277,292-293: `split` walks the right child
            // while it is itself a pair).
            if name == "pair" && args.len() == 2 {
                let mut items: Vec<p::Term> = Vec::new();
                items.push(lnterm_to_parser(&args[0]));
                let mut tail = &args[1];
                loop {
                    match tail {
                        Term::App(FunSym::NoEq(s2), a2)
                            if a2.len() == 2 && String::from_utf8_lossy(&s2.name) == "pair" =>
                        {
                            items.push(lnterm_to_parser(&a2[0]));
                            tail = &a2[1];
                        }
                        _ => {
                            items.push(lnterm_to_parser(tail));
                            break;
                        }
                    }
                }
                return p::Term::Pair(items);
            }
            p::Term::App(name, args.iter().map(lnterm_to_parser).collect())
        }
        Term::App(FunSym::C(_), args) => {
            p::Term::App("em".to_string(), args.iter().map(lnterm_to_parser).collect())
        }
        Term::App(FunSym::Ac(ac), args) => {
            // Render AC as left-assoc binops to preserve display.
            let op = match ac {
                AcSym::Mult => p::BinOp::Mult,
                AcSym::Union => p::BinOp::Union,
                AcSym::NatPlus => p::BinOp::NatPlus,
                AcSym::Xor => p::BinOp::Xor,
            };
            let mut it = args.iter();
            let first = lnterm_to_parser(it.next().expect("AC needs at least one arg"));
            it.fold(first, |acc, next| {
                p::Term::BinOp(op, Box::new(acc), Box::new(lnterm_to_parser(next)))
            })
        }
        Term::App(FunSym::List, args) => {
            p::Term::App("LIST".to_string(), args.iter().map(lnterm_to_parser).collect())
        }
    }
}

/// HS ribbon width.  HS uses `lineWidth = 110` (Main/Console.hs:236)
/// with `defaultStyle`'s `ribbonsPerLine = 1.5` → ribbon length =
/// `floor(110/1.5) = 73`.  HughesPJ `fsep` uses the ribbon to decide
/// whether the next item fits on the current line:
///
///     current_line_length - line_start_indent + next_item_len  <= ribbon
///
/// i.e. the line content (past the leading indent) cannot exceed the
/// ribbon.  We model this by passing a target maximum end column of
/// `indent + RIBBON` to the wrap decisions.
const RIBBON: usize = 73;

/// Render `[ f1, f2, ... ]` with HS's fact spacing.  Inside the
/// brackets there is a single space pad; facts are separated by `, `.
/// HS emits `[ ]` (with single space) for an empty list.
///
/// Inline form `[ a, b, c ]` is tried first.  When it overflows the
/// ribbon (`indent + RIBBON`), falls back to HS's `ppFactsList`
/// multi-line layout (Rule.hs:1258 —
/// `fsep [operator_ "[", ppFacts' list, operator_ "]"]`):
///
/// ```text
/// [
/// f1, f2, f3,
/// f4
/// ]
/// ```
///
/// Each content line at `indent` (same as the `[`).  Facts pack
/// greedily; we punctuate with `, ` and break when the next fact would
/// push the current line past `indent + RIBBON`.
#[allow(dead_code)]
fn render_fact_brackets(facts: &[p::Fact]) -> String {
    render_fact_brackets_at(facts, 3)
}

fn render_fact_brackets_at(facts: &[p::Fact], indent: usize) -> String {
    if facts.is_empty() {
        return "[ ]".to_string();
    }
    // Try inline first.
    let inline = render_fact_brackets_inline(facts);
    if !inline.contains('\n') && indent + inline.chars().count() <= indent + RIBBON {
        return inline;
    }
    // Multi-line: each fact at column `indent`, packed greedily.
    // Each fact line starts at col `indent`, so line_start = indent.
    let items: Vec<String> = facts.iter()
        .map(|f| render_fact_at(f, indent))
        .collect();
    let body = fsep_pack(&items, indent, ", ", indent);
    let pad = " ".repeat(indent);
    format!("[\n{}{}\n{}]", pad, body, pad)
}


/// HS `prettyFact`: emit `Name( arg1, arg2 )` with spaces inside the
/// parens (from `nestShort'`), commas between args.  Mirrors
/// `prettyFact` (Fact.hs:537-542):
///
/// ```haskell
/// ppFact n ts = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppTerm ts
/// ```
///
/// `nestShort'` (Class.hs:221-223) produces:
///   - flat: `Name( a, b, c )`
///   - multi: lead and finish on separate lines surrounding the nested
///     body, with `$$` allowing lead and body's first line to overlap
///     when columns permit.
///
/// Our wrap-aware variant: try inline first; on overflow, emit
/// `Name( <first_arg>,\n<col_of_paren+1>more args fsep-packed\n<col_of_name>)`.
fn render_fact(fa: &p::Fact) -> String {
    // Indent-unaware entry-point used when called from generic code
    // (acts list join, AC variant body inline).  Uses a conservative
    // indent of 3 (the typical rule-body column).
    render_fact_at(fa, 3)
}

fn render_fact_at(fa: &p::Fact, indent: usize) -> String {
    let head = {
        let mut s = String::new();
        if fa.persistent { s.push('!'); }
        s.push_str(&fa.name);
        s.push('(');
        s
    };
    if fa.args.is_empty() {
        return format!("{} )", head);
    }
    // Try inline.
    let inline = {
        let mut s = head.clone();
        s.push(' ');
        for (i, t) in fa.args.iter().enumerate() {
            if i > 0 { s.push_str(", "); }
            s.push_str(&pf::pretty_term(t));
        }
        s.push_str(" )");
        s
    };
    if indent + inline.chars().count() <= indent + RIBBON && !inline.contains('\n') {
        return inline;
    }
    // Multi-line shape from `nestShort'`:
    //   Name( <first_arg>,
    //         <more_args fsep-packed>
    //   )
    // First-arg lands at col `indent + len(head) + 1` (the `$$` overlap
    // puts the body's first line right after `Name( `).  Continuation
    // lines at `indent + len(head) + 1`.  Close `)` on its own line at
    // `indent` (HS's outer `sep` finish position).
    let head_len = head.chars().count();
    let cont_indent = indent + head_len + 1;
    let item_strs: Vec<String> = fa.args.iter()
        .map(|t| render_term_at(t, cont_indent))
        .collect();
    // line_start = `indent` (where the fact's `Name(` opened); the
    // ribbon is measured from there for the FIRST line of args.  After
    // a break, fsep_pack uses cont_indent.
    let body = fsep_pack(&item_strs, cont_indent, ", ", indent);
    let pad = " ".repeat(indent);
    format!("{} {}\n{})", head, body, pad)
}

/// Render a parser-AST term with wrap-awareness.  The output's first
/// char will land at column `indent`; continuation lines (when the
/// term wraps internally) start at column `indent` too.
fn render_term_at(t: &p::Term, indent: usize) -> String {
    // Try inline first.
    let inline = pf::pretty_term(t);
    if inline.chars().count() <= RIBBON && !inline.contains('\n') {
        return inline;
    }
    // Decompose at the top-level constructor.
    match t {
        p::Term::Pair(items) => render_pair_at(items, indent),
        p::Term::App(name, args) if !args.is_empty() => {
            render_app_at(name, args, indent)
        }
        p::Term::AlgApp(name, l, r) => {
            // HS-faithful: `aenc{m}pk` surface form, but prettyTerm emits
            // it as `Name(m, pk)` — match `pretty_term`.
            render_app_at(name, &[(**l).clone(), (**r).clone()], indent)
        }
        p::Term::Diff(l, r) => {
            render_app_at("diff", &[(**l).clone(), (**r).clone()], indent)
        }
        p::Term::BinOp(p::BinOp::Exp, l, r) => {
            // Exp `a^b` can't be broken at the `^` — leave inline.
            // (Constituents may individually be long, but HS also
            // doesn't break exp.)
            let _ = (l, r);
            inline
        }
        _ => inline,
    }
}

/// Render `<a, b, c, ...>` at `indent`, wrapping inside `<...>` when
/// overflowing.  HS uses `ppTerms ", " 1 "<" ">" (split t)` which is
/// `fcat . (text "<" :) . (++[text ">"]) . map (nest 1) . punctuate
/// comma . map ppTerm` (Term/Term.hs:288-290).  fcat is greedy-fill.
///
/// Layout when wrapping:
/// ```text
/// <first_arg, second_arg,
///  third_arg,
///  fourth_arg
/// >
/// ```
/// First arg on same line as `<`; continuation at col-of-`<` + 1.
/// Close `>` on own line at col-of-`<` when body wrapped to multiple
/// lines; inline otherwise.
fn render_pair_at(items: &[p::Term], indent: usize) -> String {
    if items.is_empty() {
        return "<>".to_string();
    }
    let inline = {
        let mut s = String::from("<");
        for (i, t) in items.iter().enumerate() {
            if i > 0 { s.push_str(", "); }
            s.push_str(&pf::pretty_term(t));
        }
        s.push('>');
        s
    };
    if inline.chars().count() <= RIBBON && !inline.contains('\n') {
        return inline;
    }
    let cont_indent = indent + 1;
    let item_strs: Vec<String> = items.iter()
        .map(|t| render_term_at(t, cont_indent))
        .collect();
    // HS observed behavior:
    //   - When the first item is multi-line, fcat breaks BEFORE it
    //     (placing `<` alone on its own line, item 0 on next line at
    //     `cont_indent`).  This is fcat's "can't inline a multi-line
    //     doc after `<`" rule.
    //   - When the first item is single-line, fcat inlines it after `<`
    //     and greedily packs subsequent items.
    //   - When any item is multi-line, the closing `>` goes on its own
    //     line at col-of-`<`.
    // first_is_multiline triggers the `<\n<inner_pad><body>>` layout
    // (HS break-before-first-item when item 0 can't fit inline after `<`).
    // We also trigger this when the FIRST item, while single-line, would
    // overflow the ribbon at the pair's items col — keeping `<X` inline
    // would force the line past `indent + RIBBON`, so HS breaks at `<`
    // and starts the item on its own fresh line at cont_indent (where
    // its continuation lines align).
    let first_is_too_wide = item_strs.first().map(|s| {
        let first_line_len = match s.find('\n') {
            Some(j) => s[..j].chars().count(),
            None => s.chars().count(),
        };
        cont_indent + first_line_len > indent + RIBBON
    }).unwrap_or(false);
    let first_is_multiline = item_strs.first().map(|s| s.contains('\n')).unwrap_or(false)
        || first_is_too_wide;
    let last_is_multiline = item_strs.last().map(|s| s.contains('\n')).unwrap_or(false);
    // For the inner-pair body fsep, line_start is the column where
    // the outer `<` was opened — that's the OUTER `indent` (the
    // render_pair_at caller's indent), since `<` is the first char
    // of its output line.  (When the pair itself is on a continuation
    // line, that line started at the pair's indent.)
    let body = fsep_pack_pair(&item_strs, cont_indent, indent);
    let pad = " ".repeat(indent);
    let inner_pad = " ".repeat(cont_indent);
    // HS-observed rule for close `>` placement:
    //   - If the LAST item is multi-line, `>` goes on its own line at
    //     col-of-`<` (the outer pair's indent).  HS examples:
    //     wireguard L_State outer pair (line 105-121), Out pair where
    //     last item is multi-line aead.
    //   - If the last item is single-line, `>` attaches to body's last
    //     line if it fits in the ribbon.  HS example: wireguard Out
    //     pair where last items `$mac1, $mac2` pack onto a line.
    let body_last_line_len = match body.rfind('\n') {
        Some(j) => body[j + 1..].chars().count(),
        None => body.chars().count(),
    };
    let close_fits = !last_is_multiline && body_last_line_len + 1 <= RIBBON;
    if first_is_multiline {
        // `<\n<inner_pad><body>\n<pad>>` (close on own line when last
        // is multi-line; attached when fits).
        if close_fits {
            format!("<\n{}{}>", inner_pad, body)
        } else {
            format!("<\n{}{}\n{}>", inner_pad, body, pad)
        }
    } else if close_fits {
        format!("<{}>", body)
    } else {
        format!("<{}\n{}>", body, pad)
    }
}

/// Render `Name( a, b, c, ... )` at `indent`, wrapping inside the
/// parens when overflowing.  Mirrors HS `ppFun` (Term/Term.hs:295-296):
///   `ppFun f ts = text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"`.
fn render_app_at(name: &str, args: &[p::Term], indent: usize) -> String {
    let head = format!("{}(", name);
    let inline = {
        let mut s = head.clone();
        for (i, t) in args.iter().enumerate() {
            if i > 0 { s.push_str(", "); }
            s.push_str(&pf::pretty_term(t));
        }
        s.push(')');
        s
    };
    if inline.chars().count() <= RIBBON && !inline.contains('\n') {
        return inline;
    }
    // HS `ppFun` uses `text (f ++ "(") <> fsep (...)  <> text ")"` (no
    // `nestShort'`).  The `fsep` starts right after `Name(` and lays
    // out items.  When wrapping, items continue at col-of-`(` + 1.
    // Close `)` attaches to last line (since the `<>` glues it on).
    let cont_indent = indent + head.chars().count();
    let item_strs: Vec<String> = args.iter()
        .map(|t| render_term_at(t, cont_indent))
        .collect();
    // line_start = indent (where the `Name(` opened on the current line).
    let body = fsep_pack(&item_strs, cont_indent, ", ", indent);
    format!("{}{})", head, body)
}

/// Greedy fsep packer.  Given pre-rendered items (each starting at
/// column 0 of its first line; continuation lines already pre-indented
/// to `indent`), join them with `sep` (typically `", "`) and break to a
/// new line at column `indent` when the next item would push the
/// current line past the ribbon budget.
///
/// `line_start`: the column where the CURRENT line started (= the
/// outer caller's leading indent).  For HS-faithful behavior, ribbon
/// fits are measured from `line_start` (not `indent`) on the first
/// line; from `indent` on subsequent (broken) lines.
///
/// `trim_break_space`: when true, the trailing space in `sep` (e.g. the
/// ` ` in `", "`) is TRIMMED before the line break — HS's `fsep` with
/// `punctuate comma` produces `f1,\n<indent>f2` shape (no trailing
/// space after the comma).  When false, the full `sep` is kept at end
/// of broken line — matches HS's pair-fcat shape `f1, \n<indent>f2`.
///
/// Returns the packed body (no leading newline, no leading indent
/// before the first item).
fn fsep_pack(items: &[String], indent: usize, sep: &str, line_start: usize) -> String {
    fsep_pack_inner(items, indent, sep, line_start, /*trim_break_space=*/true)
}

fn fsep_pack_inner(items: &[String], indent: usize, sep: &str, line_start: usize, trim_break_space: bool) -> String {
    if items.is_empty() {
        return String::new();
    }
    let sep_chars = sep.chars().count();
    let break_sep: String = if trim_break_space {
        sep.trim_end().to_string()
    } else {
        sep.to_string()
    };
    let mut out = String::new();
    let mut col = indent;
    // `cur_line_start` is the col where the CURRENT line started.  On
    // the very first iteration this is `line_start` (the outer caller's
    // line start, possibly less than `indent`).  After a break this is
    // `indent`.
    let mut cur_line_start = line_start;
    // After a multi-line item, the next item ALWAYS starts on a new
    // line (HS observed behavior: fsep doesn't pack items onto the
    // last line of a multi-line predecessor).
    let mut force_break = false;
    for (i, item) in items.iter().enumerate() {
        let first_line_len = match item.find('\n') {
            Some(j) => item[..j].chars().count(),
            None => item.chars().count(),
        };
        let last_line_len = match item.rfind('\n') {
            Some(j) => item[j + 1..].chars().count(),
            None => item.chars().count(),
        };
        let is_multiline = item.contains('\n');
        // HS-faithful ribbon constraint: line content past
        // `cur_line_start` cannot exceed RIBBON.
        let max_col = cur_line_start + RIBBON;
        if i == 0 {
            // First item lands at current col (= indent).  Multi-line
            // items' continuation lines are pre-indented to `indent`,
            // matching the line's absolute indent.
            out.push_str(item);
            col = if is_multiline { last_line_len } else { col + first_line_len };
            if is_multiline { cur_line_start = indent; force_break = true; }
        } else {
            // Fit check: `col + sep + item_first_line_len <= max_col`.
            // For multi-line items, also require they land at a fresh
            // break (col == indent) so continuation lines' pre-indent
            // matches the absolute col.  Otherwise force a break.
            let inline_fits = !force_break
                && col + sep_chars + first_line_len <= max_col
                && (!is_multiline || col + sep_chars == indent);
            if inline_fits {
                out.push_str(sep);
                out.push_str(item);
                col = if is_multiline { last_line_len } else { col + sep_chars + first_line_len };
                if is_multiline { cur_line_start = indent; force_break = true; }
                else { force_break = false; }
            } else {
                out.push_str(&break_sep);
                out.push('\n');
                out.push_str(&" ".repeat(indent));
                out.push_str(item);
                col = if is_multiline { last_line_len } else { indent + first_line_len };
                cur_line_start = indent;
                force_break = is_multiline;
            }
        }
    }
    out
}

/// Variant of `fsep_pack` for pair `<...>` body — uses HS's `fcat`
/// behaviour where the comma separator is `", "` (with trailing space)
/// and the break point keeps the trailing space at end of broken line.
/// HS output for pair body has the quirk that broken lines end with
/// `", "` (space then newline), then next line at `indent`.
fn fsep_pack_pair(items: &[String], indent: usize, line_start: usize) -> String {
    fsep_pack_inner(items, indent, ", ", line_start, /*trim_break_space=*/false)
}

// =============================================================================
// Lemma
// =============================================================================

fn render_parsed_lemma(lem: &p::Lemma, proved: &[ProvedLemma]) -> String {
    let mut out = String::new();
    out.push_str("lemma ");
    out.push_str(&lem.name);
    let attrs = render_lemma_attrs(&lem.attributes);
    if !attrs.is_empty() {
        out.push_str(" [");
        out.push_str(&attrs);
        out.push(']');
    }
    out.push_str(":\n");

    // Lemma body shape from HS `prettyLemma` (Lemma.hs:117-127):
    //   `sep [<quantifier>, doubleQuotes <formula>]`, all under `nest 2`.
    // When the combined fits on a single line, lay out as
    //   `  <quant> "<formula>"`
    // Otherwise wrap to:
    //   `  <quant>
    //   "<formula>"`
    // Within the formula, recursively wrap on the same width budget.
    let quant = quantifier_keyword(&lem.trace_quantifier);
    let flat_formula = pf::pretty_formula(&lem.formula);
    let one_line = format!("  {} \"{}\"", quant, flat_formula);
    if one_line.chars().count() <= pf::WRAP_WIDTH {
        out.push_str(&one_line);
    } else {
        // The formula starts at column 3 (`  "` prefix).  Width 76 means
        // the formula's content has `76 - 3 = 73` cols available
        // before wrap.  But the outer `"` should also fit, so allow up
        // to 75 chars total inside the quotes — i.e. wrap at indent 3.
        let wrapped = pf::pretty_formula_wrapped(&lem.formula, 3, pf::WRAP_WIDTH);
        out.push_str("  ");
        out.push_str(quant);
        out.push_str("\n  \"");
        out.push_str(&wrapped);
        out.push('"');
    }
    out.push('\n');

    // /* guarded formula characterizing ... */
    out.push_str(&render_guarded_block(lem));

    // Proof body — either the prover's result (if --prove ran) or
    // the lemma's stored skeleton.
    let proof = proved.iter().find(|p| p.name == lem.name);
    let body = match proof.and_then(|p| p.proof_body.as_ref()) {
        Some(b) => b.clone(),
        None => "by sorry".to_string(),
    };
    out.push('\n');
    out.push_str(&body);
    out
}

fn render_lemma_attrs(attrs: &[p::LemmaAttr]) -> String {
    let mut parts: Vec<String> = Vec::new();
    for a in attrs {
        use p::LemmaAttr::*;
        match a {
            Sources => parts.push("sources".into()),
            Reuse => parts.push("reuse".into()),
            DiffReuse => parts.push("diff_reuse".into()),
            UseInduction => parts.push("use_induction".into()),
            HideLemma(s) => parts.push(format!("hide_lemma={}", s)),
            Heuristic(s) => parts.push(format!("heuristic={}", s)),
            Output(modules) => {
                parts.push(format!("output=[{}]", modules.join(",")))
            }
            Left => parts.push("left".into()),
            Right => parts.push("right".into()),
            _ => {}
        }
    }
    parts.join(", ")
}

fn quantifier_keyword(q: &p::TraceQuantifier) -> &'static str {
    match q {
        p::TraceQuantifier::AllTraces => "all-traces",
        p::TraceQuantifier::ExistsTrace => "exists-trace",
    }
}

fn render_guarded_block(lem: &p::Lemma) -> String {
    let header = match &lem.trace_quantifier {
        p::TraceQuantifier::ExistsTrace => "guarded formula characterizing all satisfying traces:",
        p::TraceQuantifier::AllTraces => "guarded formula characterizing all counter-examples:",
    };
    let gf = match crate::guarded::formula_to_guarded(&lem.formula) {
        Ok(g) => g,
        Err(e) => {
            // HS renders `/* conversion to guarded formula failed: ... */`.
            return format!("/*\nconversion to guarded formula failed:\n  {}\n*/", e);
        }
    };
    // For all-traces lemmas, HS prints the negated guarded formula
    // (`gnot gf`).  The result is the "counter-example" form.
    //
    // The guarded block is rendered inside `multiComment` at col 0 with
    // the formula wrapped in `doubleQuotes` — so the formula's first
    // char sits at col 1 (right after the `"`).  We pass indent=1 so
    // the sep/nest wrap-points align with HS output (Lemma.hs:131-141).
    let to_render = match &lem.trace_quantifier {
        p::TraceQuantifier::ExistsTrace => gf,
        p::TraceQuantifier::AllTraces => crate::guarded::gnot(&gf),
    };
    let gtext = pf::pretty_guarded_wrapped(&to_render, 1, pf::WRAP_WIDTH);
    format!("/*\n{}\n\"{}\"\n*/", header, gtext)
}

// =============================================================================
// Restriction
// =============================================================================

fn render_parsed_restriction(r: &p::Restriction) -> String {
    let mut out = String::new();
    out.push_str("restriction ");
    out.push_str(&r.name);
    out.push_str(":\n  \"");
    let formula_str = pf::pretty_formula(&r.formula);
    out.push_str(&formula_str);
    out.push('"');
    // HS's `prettyRestriction`:
    //   `nest 2 (if safety then "// safety formula" else emptyDoc)`
    //   `case ogFormula of Just _ -> /* expanded formula: "..." */`
    // We treat every parsed restriction as having Just ogFormula (the
    // parser always stores it), so always emit the expanded block.
    if is_safety_formula(&r.formula) {
        out.push_str("\n  // safety formula");
    }
    out.push_str("\n\n  /*\n  expanded formula:\n  \"");
    out.push_str(&formula_str);
    out.push_str("\"\n  */");
    out
}

/// HS `isSafetyFormula` (Guarded.hs:156): closed formula with no
/// existential under any all-quantifier.
fn is_safety_formula(f: &p::Formula) -> bool {
    let gf = match crate::guarded::formula_to_guarded(f) {
        Ok(g) => g,
        Err(_) => return false,
    };
    no_existential(&gf)
}

fn no_existential(g: &crate::guarded::Guarded) -> bool {
    use crate::guarded::{Guarded, Quant};
    match g {
        Guarded::Atom(_) => true,
        Guarded::GGuarded { qua: Quant::Ex, .. } => false,
        Guarded::GGuarded { qua: Quant::All, body, .. } => no_existential(body),
        Guarded::Disj(xs) => xs.iter().all(no_existential),
        Guarded::Conj(xs) => xs.iter().all(no_existential),
    }
}

// =============================================================================
// LNTerm rendering (for equations)
// =============================================================================

fn render_lnterm(t: &tamarin_term::lterm::LNTerm) -> String {
    use tamarin_term::function_symbols::{AcSym, FunSym};
    use tamarin_term::term::Term;
    use tamarin_term::vterm::Lit;
    match t {
        Term::Lit(Lit::Var(v)) => {
            // `x.1`, `~k.2`, `$a`, `#i`, `%n` etc.  Maps `LSort` to
            // the HS sort prefix.
            let prefix = match v.sort {
                tamarin_term::lterm::LSort::Pub => "$",
                tamarin_term::lterm::LSort::Fresh => "~",
                tamarin_term::lterm::LSort::Node => "#",
                tamarin_term::lterm::LSort::Nat => "%",
                tamarin_term::lterm::LSort::Msg => "",
            };
            if v.idx == 0 {
                format!("{}{}", prefix, v.name)
            } else {
                format!("{}{}.{}", prefix, v.name, v.idx)
            }
        }
        Term::Lit(Lit::Con(n)) => {
            // HS-faithful constant rendering (Term/Term.hs::prettyTerm
            // via the Show instance on `Name`): single-quoted literal
            // with sort-prefix sigil.  `'g'`, `~'name'`, `%'n'`.
            use tamarin_term::lterm::NameTag;
            let prefix = match n.tag {
                NameTag::Pub => "",
                NameTag::Fresh => "~",
                NameTag::Nat => "%",
                NameTag::Node => "#",
            };
            format!("{}'{}'", prefix, n.id.0)
        }
        Term::App(FunSym::NoEq(sym), args) => {
            let name = String::from_utf8_lossy(&sym.name);
            // Special-case `exp` → `<a>^<b>` (infix DH exponentiation).
            // Mirrors HS `prettyTerm` (Term/Term.hs:274):
            //   `FApp (NoEq s) [t1,t2] | s == expSym -> ppTerm t1 <> text "^" <> ppTerm t2`
            if &*name == "exp" && args.len() == 2 {
                return format!("{}^{}", render_lnterm(&args[0]), render_lnterm(&args[1]));
            }
            // Special-case `pair` → `<a, b, c, ...>` (right-nested pair
            // chains flattened to n-ary tuple).  Mirrors HS `prettyTerm`
            // (Term/Term.hs:277,292-293):
            //   `FApp (NoEq s) _ | s == pairSym -> ppTerms ", " 1 "<" ">" (split t)`
            //   `split (viewTerm2 -> FPair t1 t2) = t1 : split t2`
            //   `split t                          = [t]`
            if &*name == "pair" && args.len() == 2 {
                let mut parts: Vec<String> = Vec::new();
                parts.push(render_lnterm(&args[0]));
                let mut tail = &args[1];
                loop {
                    match tail {
                        Term::App(FunSym::NoEq(s2), a2)
                            if a2.len() == 2 && &*String::from_utf8_lossy(&s2.name) == "pair" =>
                        {
                            parts.push(render_lnterm(&a2[0]));
                            tail = &a2[1];
                        }
                        _ => {
                            parts.push(render_lnterm(tail));
                            break;
                        }
                    }
                }
                return format!("<{}>", parts.join(", "));
            }
            let inner: Vec<String> = args.iter().map(render_lnterm).collect();
            if inner.is_empty() {
                name.to_string()
            } else {
                format!("{}({})", name, inner.join(", "))
            }
        }
        Term::App(FunSym::Ac(ac), args) => {
            // HS `prettyTerm` (Term/Term.hs:273):
            //   `FApp (AC o) ts -> ppTerms (ppACOp o) 1 "(" ")" ts`
            // Note the `"("`/`")"` lead/finish — AC products always
            // print fully parenthesised (e.g. `'g'^(~ekI*~ltkB)`).
            let op = match ac {
                AcSym::Mult => "*",
                AcSym::Union => "++",
                AcSym::NatPlus => "%+",
                AcSym::Xor => "\u{2295}",
            };
            format!("({})", args.iter().map(render_lnterm).collect::<Vec<_>>().join(op))
        }
        Term::App(FunSym::C(sym), args) => {
            // `C` is the commutative-builtin family — currently just `em`.
            let name = match sym {
                tamarin_term::function_symbols::CSym::EMap => "em",
            };
            let inner: Vec<String> = args.iter().map(render_lnterm).collect();
            if inner.is_empty() {
                name.to_string()
            } else {
                format!("{}({})", name, inner.join(", "))
            }
        }
        Term::App(FunSym::List, args) => {
            let inner: Vec<String> = args.iter().map(render_lnterm).collect();
            format!("LIST({})", inner.join(", "))
        }
    }
}

// =============================================================================
// Proof body
// =============================================================================

/// Render a proof tree in HS's `prettyProofWith` shape:
///
/// - `Finished Solved` with no children → `SOLVED // trace found`
/// - No children otherwise               → `by <step>` (e.g. `by contradiction`)
/// - One unnamed child                   → `<step>\n<recurse>`
/// - Multiple children                   → `<step>\n  case A\n  ...\nnext\n  case B\n  ...\nqed`
///
/// Mirrors `Theory.Proof.prettyProofWith` (Proof.hs:1073-1095).
pub fn pretty_proof_body(node: &crate::constraint::solver::search::ProofNode) -> String {
    let mut out = String::new();
    pp_proof(node, &mut out, 0);
    out
}

fn pp_proof(
    node: &crate::constraint::solver::search::ProofNode,
    out: &mut String,
    depth: usize,
) {
    use crate::constraint::solver::proof_method::{ProofMethod, Result as MR};
    // The step's first char lands at col `depth*2` (proof body uses
    // 2-space indent per nesting level).
    let step = pp_step_at(&node.method, depth * 2);
    let cases: Vec<(&String, &crate::constraint::solver::search::ProofNode)> =
        node.children.iter().collect();

    match (&node.method, cases.as_slice()) {
        (ProofMethod::Finished(MR::Solved), []) => {
            out.push_str(&step);
        }
        (_, []) => {
            // No children: `by <step>` form.
            out.push_str("by ");
            out.push_str(&step);
        }
        (_, [(label, child)]) if label.is_empty() => {
            out.push_str(&step);
            out.push('\n');
            pp_proof(child, out, depth);
        }
        (_, multi) => {
            out.push_str(&step);
            for (i, (name, child)) in multi.iter().enumerate() {
                if i > 0 {
                    out.push_str("\nnext");
                }
                out.push('\n');
                let pad = "  ".repeat(depth + 1);
                out.push_str(&pad);
                out.push_str("case ");
                out.push_str(name);
                out.push('\n');
                out.push_str(&pad);
                pp_proof(child, out, depth + 1);
            }
            out.push('\n');
            out.push_str(&"  ".repeat(depth));
            out.push_str("qed");
        }
    }
}

/// Render a single proof method.  Mirrors `prettyProofMethod`
/// (ProofMethod.hs:1486).
#[allow(dead_code)]
fn pp_step(m: &crate::constraint::solver::proof_method::ProofMethod) -> String {
    pp_step_at(m, 0)
}

fn pp_step_at(m: &crate::constraint::solver::proof_method::ProofMethod, indent: usize) -> String {
    use crate::constraint::solver::proof_method::{ProofMethod as PM, Result as MR};
    match m {
        PM::Simplify => "simplify".to_string(),
        PM::Induction => "induction".to_string(),
        PM::Sorry(reason) => match reason {
            Some(r) => format!("sorry /* {} */", r),
            None => "sorry".to_string(),
        },
        PM::Finished(MR::Solved) => "SOLVED // trace found".to_string(),
        PM::Finished(MR::Unfinishable) => {
            "UNFINISHABLE // reducible operator in subterm".to_string()
        }
        PM::Finished(MR::Contradictory(reason)) => match reason {
            Some(c) => format!("contradiction /* {} */", pp_contradiction(c)),
            None => "contradiction".to_string(),
        },
        PM::SolveGoal(g) => {
            // HS `prettyProofMethod` (ProofMethod.hs:1494):
            //   SolveGoal goal ->
            //     keyword_ "solve(" <-> prettyGoal goal <-> keyword_ ")"
            // `<->` is hsep-with-space → `solve( <goal> )` (one space
            // after `(` and before `)`).
            // The goal lands at col `indent + len("solve( ")` = `indent + 7`.
            // Pass that as the goal's indent for wrap purposes.
            let goal_str = render_goal_at(g, indent + 7);
            if goal_str.contains('\n') {
                // Multi-line goal — keep the `solve( ` prefix attached to
                // the goal's first line; the close `)` goes on its own
                // line at the goal's last-line continuation indent (the
                // indent where `solve(` was) — HS uses sep semantics.
                let pad = " ".repeat(indent);
                format!("solve( {}\n{})", goal_str, pad)
            } else {
                format!("solve( {} )", goal_str)
            }
        }
        PM::Invalidated => {
            // HS `prettyProofMethod` (ProofMethod.hs):
            //   Invalidated -> lineComment_
            //     "proof may have been invalidated by editing a reuse lemma above. You should "
            // Note the trailing space inside the string literal — HS
            // `lineComment_` renders the verbatim text after `// `.
            "// proof may have been invalidated by editing a reuse lemma above. You should ".to_string()
        }
    }
}

/// Render a `Goal` for `solve(...)` output.  Mirrors HS `prettyGoal`
/// (Constraints.hs:267-282).
#[allow(dead_code)]
fn render_goal(g: &crate::constraint::constraints::Goal) -> String {
    render_goal_at(g, 0)
}

/// Wrap-aware goal renderer.  `indent` is the column where the goal's
/// first character will land — used so internal facts/terms can decide
/// to wrap when their inline form overflows the ribbon.
fn render_goal_at(g: &crate::constraint::constraints::Goal, indent: usize) -> String {
    use crate::constraint::constraints::Goal;
    use crate::rule::PremIdx;
    match g {
        // `prettyGoal (ActionG i fa) = prettyNAtom (Action (varTerm i) fa)`
        // which expands (Atom.hs:214-215) to `prettyFact ppT fa <-> opAction <-> text (show v)`.
        // `<->` is hsep-with-space → `<fact> @ <node-id>`.
        Goal::Action(i, fa) =>
            format!("{} @ {}", render_lnfact_at(fa, indent), render_node_id(i)),
        // `prettyGoal (ChainG c p) = prettyNodeConc c <-> operator_ "~~>" <-> prettyNodePrem p`
        Goal::Chain(c, p) =>
            format!("{} ~~> {}", render_node_conc(c), render_node_prem(p)),
        // `prettyGoal (PremiseG (i, PremIdx v) fa) =
        //    prettyLNFact fa <-> text ("▶" ++ subscript (show v)) <-> prettyNodeId i`
        Goal::Premise((i, PremIdx(v)), fa) =>
            format!("{} \u{25B6}{} {}",
                render_lnfact_at(fa, indent), goal_subscript(*v), render_node_id(i)),
        // `prettyGoal (SplitG x) = text "splitEqs" <> parens (text $ show (unSplitId x))`
        // `<>` is `<>` (no space) so it's `splitEqs(<n>)`.
        Goal::Split(id) => format!("splitEqs({})", id.0),
        // `prettyGoal (DisjG (Disj [])) = text "Disj" <-> operator_ "(⊥)"`
        // → `Disj (⊥)` (one space, from `<->`).
        Goal::Disj(d) if d.0.is_empty() => "Disj (\u{22A5})".to_string(),
        // `prettyGoal (DisjG (Disj gfs)) =
        //    fsep $ punctuate (operator_ "  ∥") (map (nest 1 . parens . prettyGuarded) gfs)`
        // `punctuate` puts the separator AFTER each non-last element,
        // and `fsep` joins with a space.  Result: each alt wrapped in
        // parens, joined by `  ∥` (two spaces + ∥) plus the fsep space →
        // `(<g1>)  ∥ (<g2>)  ∥ (<g3>)`.
        Goal::Disj(d) => {
            let parts: Vec<String> = d.0.iter()
                .map(|c| format!("({})", crate::pretty_formula::pretty_guarded(c)))
                .collect();
            parts.join("  \u{2225} ")
        }
        // `prettyGoal (SubtermG (l,r)) =
        //    prettyLNTerm l <-> operator_ "⊏" <-> prettyLNTerm r`
        Goal::Subterm((l, r)) =>
            format!("{} \u{228F} {}", render_lnterm(l), render_lnterm(r)),
    }
}

/// Render an `LNFact` for goal output.  Mirrors HS `prettyFact`
/// (Fact.hs:537-544) via `nestShort'` (Class.hs:218-223): in single-line
/// form the body is sandwiched with spaces — `Name( arg1, arg2 )`.
/// For arity-0: `Name( )`.  Persistent tags get a `!` prefix via
/// `showFactTag` (Fact.hs:519-523).
#[allow(dead_code)]
fn render_lnfact(fa: &crate::fact::LNFact) -> String {
    render_lnfact_at(fa, 0)
}

/// Wrap-aware variant.  When the inline form exceeds the ribbon from
/// `indent`, lays out the args with HS-faithful `nestShort'` semantics
/// (see `render_fact_at` for the parser-AST equivalent).
fn render_lnfact_at(fa: &crate::fact::LNFact, indent: usize) -> String {
    use crate::fact::Multiplicity;
    let prefix = match &fa.tag {
        crate::fact::FactTag::Proto(Multiplicity::Persistent, _, _) => "!",
        // HS `factTagMultiplicity` (Fact.hs:340-344): KU/KD are persistent.
        crate::fact::FactTag::Ku | crate::fact::FactTag::Kd => "!",
        _ => "",
    };
    let name = crate::fact::fact_tag_name(&fa.tag);
    if fa.terms.is_empty() {
        return format!("{}{}( )", prefix, name);
    }
    // Convert to parser-AST and reuse the wrap-aware fact renderer.
    let pfa = p::Fact {
        persistent: prefix == "!",
        name: name.to_string(),
        args: fa.terms.iter().map(lnterm_to_parser).collect(),
        annotations: Vec::new(),
    };
    render_fact_at(&pfa, indent)
}

/// Render a `NodeId` (`LVar` of Node sort).  HS `prettyNodeId`
/// (LTerm.hs:848-849) is `text . show`, where `Show LVar`
/// (LTerm.hs:525-532) yields `<sortPrefix><name>` (or `<...>.<idx>`).
fn render_node_id(nid: &crate::constraint::constraints::NodeId) -> String {
    render_lvar(nid)
}

/// Render a `NodeConc`.  Mirrors HS `prettyNodeConc`
/// (Constraints.hs:250-251): `parens (prettyNodeId v <> comma <-> int i)`.
/// `<>` joins with no space; `<->` adds a space — `(#i, 0)`.
fn render_node_conc(c: &crate::constraint::constraints::NodeConc) -> String {
    format!("({}, {})", render_node_id(&c.0), (c.1).0)
}

/// Render a `NodePrem`.  Mirrors HS `prettyNodePrem`
/// (Constraints.hs:254-255): same layout as `prettyNodeConc`.
fn render_node_prem(p: &crate::constraint::constraints::NodePrem) -> String {
    format!("({}, {})", render_node_id(&p.0), (p.1).0)
}

/// Unicode-subscript digits for a non-negative integer.  Mirrors HS
/// `subscript` used by `prettyGoal (PremiseG …)` in Constraints.hs:273.
fn goal_subscript(n: usize) -> String {
    n.to_string().chars().map(|c| match c {
        '0' => '\u{2080}', '1' => '\u{2081}', '2' => '\u{2082}',
        '3' => '\u{2083}', '4' => '\u{2084}', '5' => '\u{2085}',
        '6' => '\u{2086}', '7' => '\u{2087}', '8' => '\u{2088}',
        '9' => '\u{2089}', _ => c,
    }).collect()
}

fn pp_contradiction(c: &crate::constraint::solver::contradictions::Contradiction) -> String {
    use crate::constraint::solver::contradictions::Contradiction as C;
    // HS `prettyContradiction` (Contradictions.hs:493-511).
    match c {
        C::Cyclic => "cyclic".to_string(),
        // HS: `SubtermCyclic -> text "contradictory subterm store"`
        C::SubtermCyclic => "contradictory subterm store".to_string(),
        C::IncompatibleEqs => "incompatible equalities".to_string(),
        C::NonNormalTerms => "non-normal terms".to_string(),
        // HS: `ForbiddenExp -> text "non-normal exponentiation rule instance"`
        C::ForbiddenExp => "non-normal exponentiation rule instance".to_string(),
        // HS: `ForbiddenBP -> text "non-normal bilinear pairing rule instance"`
        C::ForbiddenBP => "non-normal bilinear pairing rule instance".to_string(),
        // HS: `ForbiddenKD -> text "forbidden KD-fact"`
        C::ForbiddenKD => "forbidden KD-fact".to_string(),
        C::ForbiddenChain => "forbidden chain".to_string(),
        C::ImpossibleChain => "impossible chain".to_string(),
        // HS: `NonInjectiveFactInstance cex -> text $ "non-injective facts " ++ show cex`
        // where `cex :: (NodeId, NodeId, NodeId)`.  HS `Show` for a
        // tuple yields `(a,b,c)` (no spaces after commas), with each
        // component rendered by `Show LVar` (LTerm.hs:525-532) — which
        // is identical to our `render_lvar`.
        C::NonInjectiveFactInstance(a, b, c) =>
            format!("non-injective facts ({},{},{})",
                render_lvar(a), render_lvar(b), render_lvar(c)),
        C::FormulasFalse => "from formulas".to_string(),
        // HS: `SuperfluousLearn m v ->
        //        doubleQuotes (prettyLNTerm m) <->
        //        text "derived before and after" <->
        //        doubleQuotes (prettyNodeId v)`
        // → `"<m>" derived before and after "<v>"`.
        C::SuperfluousLearn(m, v) =>
            format!("\"{}\" derived before and after \"{}\"",
                render_lnterm(m), render_node_id(v)),
        // HS: `NodeAfterLast (i,j) ->
        //        text $ "node " ++ show j ++ " after last node " ++ show i`
        // Note HS reverses the order: `j` first in the message, then `i`.
        C::NodeAfterLast(i, j) =>
            format!("node {} after last node {}",
                render_lvar(j), render_lvar(i)),
    }
}

// =============================================================================
// Generated-from
// =============================================================================

fn render_generated_from(build: &BuildInfo) -> String {
    format!(
        "/*\nGenerated from:\nTamarin version {}\nMaude version {}\nGit revision: {}, branch: {}\nCompiled at: {}\n*/",
        build.tamarin_version,
        build.maude_version,
        build.git_revision,
        build.git_branch,
        build.compiled_at,
    )
}
