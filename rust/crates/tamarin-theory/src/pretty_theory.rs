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

    // Iterate parsed.items, mapping to elaborated entities where needed.
    // HS preserves source order via vsep over `thyItems`.  Each item is
    // separated from the previous block by a blank line.
    for item in parsed.items.iter() {
        if let Some(b) = render_parsed_item(item, 0, parsed, elaborated, proved) {
            out.push('\n');
            out.push_str(&b);
            out.push('\n');
        }
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
    let prems_str = render_fact_brackets(prems);
    let concs_str = render_fact_brackets(concs);
    const WIDTH: usize = 76;
    let mut out = String::new();
    let single = if acts.is_empty() {
        format!("   {} --> {}", prems_str, concs_str)
    } else {
        format!("   {} --[ {} ]-> {}",
            prems_str,
            acts.iter().map(render_fact).collect::<Vec<_>>().join(", "),
            concs_str)
    };
    if single.chars().count() <= WIDTH {
        out.push_str(&single);
    } else {
        out.push_str("   ");
        out.push_str(&prems_str);
        out.push('\n');
        if acts.is_empty() {
            out.push_str("  -->");
        } else {
            let acts_inline = format!("  --[ {} ]->",
                acts.iter().map(render_fact).collect::<Vec<_>>().join(", "));
            if acts_inline.chars().count() <= WIDTH {
                out.push_str(&acts_inline);
            } else {
                out.push_str("  --[\n");
                for (i, a) in acts.iter().enumerate() {
                    out.push_str("  ");
                    out.push_str(&render_fact(a));
                    if i + 1 < acts.len() { out.push(','); }
                    out.push('\n');
                }
                out.push_str("  ]->");
            }
        }
        out.push('\n');
        out.push_str("   ");
        out.push_str(&concs_str);
    }
    out
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
            if name == "pair" && args.len() == 2 {
                return p::Term::Pair(args.iter().map(lnterm_to_parser).collect());
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

/// Render `[ f1, f2, ... ]` with HS's fact spacing.  Inside the
/// brackets there is a single space pad; facts are separated by `, `.
/// HS emits `[ ]` (with single space) for an empty list.
fn render_fact_brackets(facts: &[p::Fact]) -> String {
    if facts.is_empty() {
        return "[ ]".to_string();
    }
    let mut out = String::new();
    out.push_str("[ ");
    for (i, f) in facts.iter().enumerate() {
        if i > 0 { out.push_str(", "); }
        out.push_str(&render_fact(f));
    }
    out.push_str(" ]");
    out
}

/// HS `prettyFact`: emit `Name( arg1, arg2 )` with spaces inside the
/// parens (from `nestShort'`), commas between args.  Empty-arg fact
/// is `Name( )` ... actually HS uses `nestShort'` which calls `sep`
/// with the body — when the body is empty, `fsep . punctuate comma []`
/// is `emptyDoc`, and `sep [text "Name(" $$ nest 6 empty, text ")"]`
/// fits to `Name( )`.  We mirror that here for arity-0 facts.
fn render_fact(fa: &p::Fact) -> String {
    let mut out = String::new();
    if fa.persistent { out.push('!'); }
    out.push_str(&fa.name);
    out.push_str("( ");
    for (i, t) in fa.args.iter().enumerate() {
        if i > 0 { out.push_str(", "); }
        out.push_str(&pf::pretty_term(t));
    }
    if fa.args.is_empty() {
        // Empty body: HS still renders `Name( )`.  But pop the trailing
        // space we already added and replace with a single space — the
        // `( )` form keeps a single internal space.
    }
    out.push_str(" )");
    out
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
            // Named constant.  Render via Debug for now.
            format!("{:?}", n)
        }
        Term::App(FunSym::NoEq(sym), args) => {
            let name = String::from_utf8_lossy(&sym.name);
            // Special-case `pair` → `<a, b>`.
            if &*name == "pair" && args.len() == 2 {
                return format!("<{}, {}>", render_lnterm(&args[0]), render_lnterm(&args[1]));
            }
            let inner: Vec<String> = args.iter().map(render_lnterm).collect();
            if inner.is_empty() {
                name.to_string()
            } else {
                format!("{}({})", name, inner.join(", "))
            }
        }
        Term::App(FunSym::Ac(ac), args) => {
            let op = match ac {
                AcSym::Mult => "*",
                AcSym::Union => "++",
                AcSym::NatPlus => "%+",
                AcSym::Xor => "\u{2295}",
            };
            args.iter().map(render_lnterm).collect::<Vec<_>>().join(op)
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
    let step = pp_step(&node.method);
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
fn pp_step(m: &crate::constraint::solver::proof_method::ProofMethod) -> String {
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
        PM::SolveGoal(_g) => {
            // Goal pretty-print is complex; render a placeholder for
            // now.  TODO: port `prettyGoal` for HS-faithful output.
            "solve(...)".to_string()
        }
        PM::Invalidated => {
            "// proof may have been invalidated by editing a reuse lemma above. You should".to_string()
        }
    }
}

fn pp_contradiction(c: &crate::constraint::solver::contradictions::Contradiction) -> String {
    use crate::constraint::solver::contradictions::Contradiction as C;
    match c {
        C::Cyclic => "cyclic".to_string(),
        C::SubtermCyclic => "subterm cyclic".to_string(),
        C::IncompatibleEqs => "incompatible equalities".to_string(),
        C::FormulasFalse => "from formulas".to_string(),
        C::SuperfluousLearn(_, _) => "non-normal terms".to_string(),
        C::NonNormalTerms => "non-normal terms".to_string(),
        C::ForbiddenExp => "non-normal terms".to_string(),
        C::ForbiddenBP => "non-normal terms".to_string(),
        C::ForbiddenKD => "intruder knows constructed message".to_string(),
        C::ForbiddenChain => "forbidden chain".to_string(),
        C::ImpossibleChain => "impossible chain".to_string(),
        C::NonInjectiveFactInstance(_, _, _) =>
            "non-injective fact instance".to_string(),
        C::NodeAfterLast(_, _) => "node after last".to_string(),
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
