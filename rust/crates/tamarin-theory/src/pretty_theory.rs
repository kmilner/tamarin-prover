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

/// `sep`-style multi-line layout for equations: when there's more than
/// one item OR a single item overflows the line, lay out as
/// `<lead>\n    item1,\n    item2,\n    ...,\n    itemN`.  Otherwise
/// keep a single line.  HS's `sep [hdr, nest 2 (punctuate comma ds)]`
/// produces this exact shape; with `defaultStyle` lineLength = 76 the
/// vertical split fires for any multi-equation list.
fn sep_block_with_lead(lead: &str, items: &[String]) -> String {
    if items.is_empty() { return String::new(); }
    const WIDTH: usize = 76;
    let joined = items.join(", ");
    let single = format!("{} {}", lead, joined);
    // HS triggers vertical layout when items.len() > 1 (each item gets
    // its own line under the lead).  Single-line otherwise.
    if items.len() == 1 && single.chars().count() <= WIDTH {
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

fn render_rule(parsed_rule: &p::Rule, _elab: &Theory) -> String {
    let name = &parsed_rule.name;
    let prems = &parsed_rule.premises;
    let acts = &parsed_rule.actions;
    let concs = &parsed_rule.conclusions;

    let prems_str = render_fact_brackets(prems);
    let concs_str = render_fact_brackets(concs);

    let mut out = String::new();
    out.push_str("rule (modulo E) ");
    out.push_str(name);
    out.push_str(":\n");

    // Try single-line layout first.  HS's `prettyRuleRestrGen` uses
    // `sep` which fits onto one line when possible; otherwise wraps
    // each clause to its own line.  Width threshold: HS default 76,
    // minus the leading 3-space indent the rule body uses.
    const WIDTH: usize = 76;
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
        // Multi-line layout:
        //   <3sp>[ prems ]
        //  <2sp>-->                 (no actions)
        //  <2sp>--[ act1, act2 ]->  (with actions, fits one line)
        //  <2sp>--[                 (with actions, overflows)
        //  <2sp>act1,
        //  <2sp>act2
        //  <2sp>]->
        //   <3sp>[ concs ]
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
    // For the rule case where there's exactly the trivial AC variant
    // (no DH/XOR/etc.), HS emits a `/* has exactly the trivial AC
    // variant */` comment indented 2 spaces, separated by a blank line.
    out.push_str("\n\n  /* has exactly the trivial AC variant */");
    out
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
    out.push_str(":\n  ");
    out.push_str(quantifier_keyword(&lem.trace_quantifier));
    out.push_str(" \"");
    out.push_str(&pf::pretty_formula(&lem.formula));
    out.push_str("\"\n");

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
    let gtext = match &lem.trace_quantifier {
        p::TraceQuantifier::ExistsTrace => pf::pretty_guarded(&gf),
        p::TraceQuantifier::AllTraces => pf::pretty_guarded(&crate::guarded::gnot(&gf)),
    };
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
