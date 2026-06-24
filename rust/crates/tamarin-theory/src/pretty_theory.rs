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

// =============================================================================
// Heuristic / GoalRanking rendering
// =============================================================================

/// Compute the default oracle name for a theory file.
///
/// Mirrors HS `defaultOracleNames` (System.hs:551-561): when an oracle
/// ranking carries no explicit relative-path, the name is derived from the
/// theory file path by the following algorithm (faithful port of the HS
/// `groupBy` computation):
///
/// 1. Take the prefix before the first `.` in `in_file`.
/// 2. Take the suffix after the last `/` in that prefix.
/// 3. Append `".oracle"`.
/// 4. If that file exists on disk → use it; otherwise → fall back to `"oracle"`.
///
/// For absolute paths the step-2 suffix starts with `/` (e.g. `/defaultoracle`),
/// so the resulting path `"/defaultoracle.oracle"` almost never exists, and the
/// function returns `"oracle"` — matching observed HS behaviour.
pub(crate) fn oracle_name_for_theory(in_file: &str) -> String {
    // Step 1: HS `head $ groupBy (\_ b -> b /= '.') srcThyInFileName`.
    // `groupBy` always keeps the first character in the head group, then
    // extends it up to (not including) the first '.' at position >= 1.  So
    // a LEADING '.' (e.g. "./foo.spthy") belongs to the prefix and is NOT a
    // terminator — the prefix is "./foo".  Mirror that by ignoring a '.' at
    // char-position 0.
    let split = in_file
        .char_indices()
        .enumerate()
        .find(|(pos, (_, ch))| *pos >= 1 && *ch == '.')
        .map(|(_, (byte, _))| byte)
        .unwrap_or(in_file.len());
    let before_dot = &in_file[..split];
    // Step 2: suffix after last '/' in before_dot.
    // HS `groupBy (\_ b -> b /= '/') s` splits `s` at every '/', then `last`
    // takes the final segment.  For absolute paths this segment starts with
    // '/' (e.g. "/defaultoracle"), so `inFileOracleName` is "/defaultoracle.oracle".
    let after_slash = match before_dot.rfind('/') {
        Some(i) => &before_dot[i..],   // includes the '/' prefix, mirroring HS
        None => before_dot,
    };
    // Step 3: append ".oracle"
    let candidate = format!("{}.oracle", after_slash);
    // Step 4: existence check
    if std::path::Path::new(&candidate).exists() {
        candidate
    } else {
        "oracle".to_string()
    }
}

/// Render a single `GoalRanking` token from the raw heuristic string.
///
/// Mirrors HS `prettyGoalRanking` (System.hs:710-728):
/// - `OracleRanking`/`OracleSmartRanking` → `<char> "<oraclename>"`
/// - `InternalTacticRanking`              → `{<name>}`
/// - all others                           → single char
///
/// `oracle_name` is the already-computed default oracle name for the theory
/// (from `oracle_name_for_theory`); it is used when the ranking carries no
/// explicit name.
fn render_single_ranking(ch: char, explicit_oracle: Option<&str>, oracle_name: &str) -> String {
    match ch {
        'o' | 'O' => {
            let name = explicit_oracle.unwrap_or(oracle_name);
            format!("{} \"{}\"", ch, name)
        }
        _ => ch.to_string(),
    }
}

/// Parse a raw heuristic string and re-render it in HS style.
///
/// Mirrors `prettyGoalRankings rs = unwords (map prettyGoalRanking rs)`
/// (System.hs:707-708).  The raw string is the verbatim text stored after
/// `heuristic:` / `heuristic=` in the source file.  It may be compact
/// (`"osopo"`) or already-expanded (`"o \"oracle\" s"`).
///
/// Grammar (mirrors HS `goalRanking` in Signature.hs:293-311):
///   rankings     ::= ranking+
///   ranking      ::= oracle_ranking | tactic_ranking | letter
///   oracle_ranking ::= ('o' | 'O') ws* ('"' name '"' ws*)?
///   tactic_ranking ::= '{' [^}]* '}'
///   letter       ::= [a-zA-Z] ws*
pub fn pretty_goal_rankings(raw: &str, in_file: &str) -> String {
    let oracle_name = oracle_name_for_theory(in_file);
    let mut result = Vec::new();
    let chars: Vec<char> = raw.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        // Skip comments.  HS's lexer consumes `/* … */` block and `// …`
        // line comments BETWEEN ranking tokens before parsing them, so a
        // heuristic like `p /* note for SAPIC */` parses to just `[p]`.
        // The raw string RS stores is read verbatim to end-of-line, so we
        // must skip comments here too — otherwise the comment's letters are
        // mis-tokenised as bogus rankings (and an `o` even as an oracle).
        if c == '/' && i + 1 < chars.len() && chars[i + 1] == '*' {
            i += 2;
            while i + 1 < chars.len() && !(chars[i] == '*' && chars[i + 1] == '/') {
                i += 1;
            }
            i = (i + 2).min(chars.len()); // consume closing `*/`
            continue;
        }
        if c == '/' && i + 1 < chars.len() && chars[i + 1] == '/' {
            // Line comment runs to the end of the (single-line) raw string.
            break;
        }
        if c == '{' {
            // Tactic ranking: `'{' ++ _name tactic ++ "}"` (System.hs:714).
            // HS's parser does `string "{" <* skipMany (char ' ')` before
            // capturing `tacticName <- many1 (noneOf "\"\n\r{}")`
            // (Signature.hs:298-303), so it STRIPS leading space(s) after `{`
            // but PRESERVES any trailing space (`noneOf` does not exclude
            // space).  Mirror that: skip leading spaces, then re-emit the rest
            // verbatim up to `}`.
            i += 1; // consume '{'
            while i < chars.len() && chars[i] == ' ' { i += 1; }
            let name_start = i;
            while i < chars.len() && chars[i] != '}' {
                i += 1;
            }
            let name: String = chars[name_start..i].iter().collect();
            if i < chars.len() {
                i += 1; // consume '}'
            }
            result.push(format!("{{{}}}", name));
        } else if c == 'o' || c == 'O' {
            i += 1;
            // Skip whitespace
            while i < chars.len() && chars[i] == ' ' { i += 1; }
            // Look for optional quoted oracle name
            if i < chars.len() && chars[i] == '"' {
                i += 1; // consume opening '"'
                let name_start = i;
                while i < chars.len() && chars[i] != '"' && chars[i] != '\n' && chars[i] != '\r' {
                    i += 1;
                }
                let explicit_name: String = chars[name_start..i].iter().collect();
                if i < chars.len() && chars[i] == '"' { i += 1; } // consume closing '"'
                result.push(render_single_ranking(c, Some(&explicit_name), &oracle_name));
            } else {
                result.push(render_single_ranking(c, None, &oracle_name));
            }
        } else if c.is_ascii_alphabetic() {
            result.push(c.to_string());
            i += 1;
        } else {
            // Unknown character — skip
            i += 1;
        }
    }
    result.join(" ")
}

// =============================================================================

/// Render the analyzed theory in HS's `prettyClosedTheory` shape.
pub fn pretty_closed_theory(
    parsed: &p::Theory,
    elaborated: &Theory,
    proved: &[ProvedLemma],
    wf_block: &str,
    build: &BuildInfo,
    in_file: &str,
    auto_sources: bool,
) -> String {
    let mut out = String::new();

    // HS `prettyTheory` (TheoryObject.hs:741-756):
    //   vsep [ kwTheoryName name
    //        , ...configBlocks...  (filter isConfigBlock thyItems, before begin)
    //        , kwTheoryBegin, ... ]
    // ConfigBlocks: `prettyConfigBlock cb = text "configuration: " <> doubleQuotes (text cb)`
    // RS stores the configuration string directly in `parsed.configuration`.
    out.push_str("theory ");
    out.push_str(&elaborated.name);
    if let Some(cfg) = &parsed.configuration {
        // HS: `text "configuration: " <> doubleQuotes (text cb)`
        // = `configuration: "<cb>"`
        // Emitted via vsep (blank-line separated from theory name and begin).
        out.push_str("\n\nconfiguration: \"");
        out.push_str(cfg);
        out.push('"');
    }
    out.push_str("\n\nbegin\n\n");

    // // Function signature and definition of the equational theory E\n\n
    out.push_str("// Function signature and definition of the equational theory E\n\n");

    // builtins / functions / equations — render_signature already ends
    // with a trailing '\n' after each line so we don't add another here.
    out.push_str(&render_signature(&elaborated.signature.maude_sig));

    // HS `prettyTheory` (TheoryObject.hs:741-751) emits, between the
    // signature and the cache block, in this order:
    //   - `vcat $ map prettyTactic thyT` (only if non-empty tactics)
    //   - `heuristic: <ranking>` line (only if non-empty heuristic)
    //   - `ppCache` (the "looping facts with injective instances" comment).
    // `vsep` separates each non-empty element with a blank line.
    // Mirror that here.
    if !elaborated.tactic.is_empty() {
        // `vcat $ map prettyTactic thyT`: tactics joined by a single
        // newline (no blank line between them).
        let blocks: Vec<String> = elaborated.tactic.iter().map(|t| t.render()).collect();
        out.push('\n');
        out.push_str(&blocks.join("\n"));
        out.push('\n');
    }
    if !elaborated.heuristic.is_empty() {
        // HS `TheoryObject.hs:749`: `text "heuristic: " <> text (prettyGoalRankings thyH)`
        // where `prettyGoalRankings = unwords . map prettyGoalRanking` (System.hs:707-708).
        // Each ranking in the Vec is a raw heuristic string; join their expansions with a
        // space.  (In practice there is only one `heuristic:` item per theory.)
        let rendered: Vec<String> = elaborated.heuristic.iter()
            .map(|raw| pretty_goal_rankings(raw, in_file))
            .collect();
        out.push('\n');
        out.push_str("heuristic: ");
        out.push_str(&rendered.join(" "));
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
    // Collect macros once (mirrors HS `applyMacroInRestriction` /
    // `parseLemmaWithMacros`): the restriction/lemma renderers apply them to
    // get the expanded formula.  Computed here (not per item) so it is not
    // re-collected and cloned for every theory item.
    let macros: Vec<p::Macro> = parsed.items.iter()
        .filter_map(|i| if let p::TheoryItem::Macros(ms) = i { Some(ms.as_slice()) } else { None })
        .flatten()
        .cloned()
        .collect();
    // Collect predicate declarations once.  HS `expandRestriction` /
    // `expandLemma` (TheoryObject.hs:430-446) predicate-expand BOTH the
    // main and original formulas of every restriction/lemma against the
    // theory's predicates (which includes the builtin `Smaller`/multiset-
    // `(<)`), so the displayed formula is always the expanded one.  The
    // parse already succeeded, so every referenced predicate is defined;
    // using the full set for display-time expansion is safe.
    let predicates: Vec<p::Predicate> = parsed.items.iter()
        .filter_map(|i| if let p::TheoryItem::Predicates(ps) = i { Some(ps.as_slice()) } else { None })
        .flatten()
        .cloned()
        .collect();
    // Names of arity-1 NoEq function symbols.  Depends only on the
    // (immutable) elaborated signature, so compute it once here and thread
    // it through to every per-item renderer rather than recomputing (and
    // re-cloning the signature) for each rule/lemma/restriction/predicate.
    let arity1 = arity1_noeq_names(elaborated);
    // HS `prettyClosedTheory` (ClosedTheory.hs:383) switches the WHOLE theory
    // to the open-as-closed renderer when `containsManualRuleVariants` holds,
    // which suppresses loop-breaker comments on trivial-AC-variant rules.
    let manual_variants = contains_manual_rule_variants(parsed, elaborated, auto_sources);
    let rendered: Vec<Option<String>> = parsed.items.par_iter()
        .map(|item| render_parsed_item(item, &macros, &predicates, elaborated, proved, in_file, &arity1, manual_variants, auto_sources))
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
/// /*
/// looping facts with injective instances:
///   T1/n1, T2/n2, ...
/// */
/// ```
///
/// HS:
/// ```haskell
/// multiComment $ sep
///   [ text "looping facts with injective instances:"
///   , nest 2 $ fsepList (text . showFactTagArity) (map fst tags) ]
/// ```
/// where `multiComment d = comment $ fsep [text "/*", d, text "*/"]`
/// (Pretty.hs:102-103) and `fsepList pp = fsep . punctuate comma . map pp`
/// (Pretty.hs:88-89).
///
/// Emits the empty string when no fact tags are injective.  Computes
/// the set on demand from the elaborated rules + reducible function
/// symbols — same call site as `ProofContext::new`
/// (`constraint/solver/context.rs:493-495`).
fn render_injective_fact_insts(elab: &Theory) -> String {
    use crate::pretty_hpj::{self as hpj, Doc, punctuate};
    use crate::fact::{FactTag, Multiplicity};
    let proto_rules: Vec<&crate::rule::ProtoRuleE> = elab.rules()
        .map(|r| &r.rule)
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
    let tag_docs: Vec<Doc> = tags.iter().map(|(t, _)| Doc::text(label(t))).collect();
    // fsepList (text . showFactTagArity) (map fst tags)
    let list_doc = hpj::fsep(punctuate(Doc::text(","), tag_docs));
    // sep [text "looping facts...", nest 2 list_doc]
    let inner = hpj::sep(vec![
        Doc::text("looping facts with injective instances:"),
        list_doc.nest(2),
    ]);
    // multiComment inner = comment $ fsep [text "/*", inner, text "*/"]
    let doc = hpj::fsep(vec![Doc::text("/*"), inner, Doc::text("*/")]);
    doc.render()
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
        // HS renders builtins via the same `ppNonEmptyList'` as functions:
        // `(keyword_ "builtins:" <->) . fsep . punctuate comma`
        // (Term/Maude/Signature.hs:220,229-231) — so the list wraps through
        // the HughesPJ engine, not a flat join.
        out.push_str(&wrap_with_lead("builtins:", &builtins));
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
/// `prettyCtxtStRule $ S.toList (stRules sig)` (Term/Maude/Signature.hs:226),
/// i.e. equations in `S.toList` order.  `CtxtStRule` derives structural `Ord`,
/// so we emit them in the `st_rules` `BTreeSet` iteration order, which mirrors
/// HS's `S.toList` exactly.  We must NOT re-sort by the rendered pretty-string,
/// since that diverges from the structural (term-tree) order (e.g. AC products
/// pretty-print with a leading `(`, `exp` as infix `a^b`).
///
/// Each side is returned as a HughesPJ `Doc` (not a flat string) so that wide
/// function applications wrap at the ribbon width exactly as HS
/// `prettyCtxtStRule`/`prettyLNTerm` (SubtermRule.hs:122-123, Term.hs:295-296)
/// — the `ppFun f ts = text (f++"(") <> fsep (punctuate comma …) <> ")"` `fsep`
/// breaks at argument boundaries when the term overruns.  We reach the Doc path
/// by converting the `LNTerm` to a parser-AST `p::Term` (`lnterm_to_parser`,
/// the same conversion already used elsewhere) and rendering it through
/// `pf::term_doc` (= HS `prettyTerm`).
fn render_equations(sig: &tamarin_term::maude_sig::MaudeSig) -> Vec<(crate::pretty_hpj::Doc, crate::pretty_hpj::Doc)> {
    let mut items = Vec::new();
    for r in &sig.st_rules {
        let lhs = pf::term_doc(&lnterm_to_parser(&r.lhs));
        let rhs = pf::term_doc(&lnterm_to_parser(&r.rhs.term));
        items.push((lhs, rhs));
    }
    items
}

/// HS `ppNonEmptyList' name pp xs = (keyword_ name <->) . fsep $
/// punctuate comma (map pp xs)` (Term/Maude/Signature.hs:229-231).
/// `<->` is HughesPJ `<+>` (beside-with-space), and `fsep` is the
/// fill-paragraph combinator, so the wrap decisions must come from the
/// ported HughesPJ Doc engine (LINE_LENGTH=110, RIBBON=73) — not a
/// hand-rolled greedy fill at a guessed width.  Route through `pretty_hpj`.
fn wrap_with_lead<S: AsRef<str>>(lead: &str, items: &[S]) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    if items.is_empty() { return String::new(); }
    let docs: Vec<Doc> = items.iter().map(Doc::text).collect();
    let body = hpj::fsep(hpj::punctuate(Doc::char(','), docs));
    Doc::text(lead).beside_sp(body).render()
}

/// HS `equations:` layout (Term/Maude/Signature.hs:224-225):
///   `P.sep ( keyword_ "equations:" : map (P.nest 2) ds )`
/// where `ds = P.punctuate P.comma (map prettyCtxtStRule rules)` — i.e. the
/// comma is appended to the END of each equation doc (all but the last), and
/// each resulting doc is `nest 2`'d, then `sep`-joined.
///
/// Each equation doc is itself (SubtermRule.hs:121-123):
///   `prettyCtxtStRule r = sep [ nest 2 (prettyLNTerm lhs)
///                             , operator_ "=" <-> prettyLNTerm rhs ]`
/// — so the LHS carries an *inner* `nest 2`.  When the outer `sep` breaks and
/// lays each equation on its own line at indent 2, the inner `nest 2` adds a
/// further 2, yielding the 4-space indent HS emits.  Reproducing that requires
/// the structured doc, not a pre-joined `lhs = rhs` string.  Route through the
/// ported HughesPJ engine so the break decision and indentation are HS-exact.
///
/// `items` carries the LHS/RHS as already-built term `Doc`s (HS `prettyLNTerm`)
/// so the inner function-application `fsep` wrapping survives — passing flat
/// strings would defeat the engine and emit over-long single lines for wide
/// equations (e.g. BP `idverify(idsign(…), m, IBPub(…))`).
fn sep_block_with_lead(lead: &str, items: &[(crate::pretty_hpj::Doc, crate::pretty_hpj::Doc)]) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    if items.is_empty() { return String::new(); }
    let n = items.len();
    let mut docs: Vec<Doc> = Vec::with_capacity(n + 1);
    docs.push(Doc::text(lead));
    for (i, (lhs, rhs)) in items.iter().enumerate() {
        // prettyCtxtStRule: sep [ nest 2 lhs, "=" <-> rhs ]
        let lhs_doc = lhs.clone().nest(2);
        let eq_doc = Doc::text("=").beside_sp(rhs.clone());
        let mut d = hpj::sep(vec![lhs_doc, eq_doc]);
        if i + 1 < n {
            d = d.beside(Doc::char(','));
        }
        docs.push(d.nest(2));
    }
    hpj::sep(docs).render()
}

// =============================================================================
// Item dispatch
// =============================================================================

#[allow(clippy::too_many_arguments)]
fn render_parsed_item(
    item: &p::TheoryItem,
    macros: &[p::Macro],
    predicates: &[p::Predicate],
    elab: &Theory,
    proved: &[ProvedLemma],
    in_file: &str,
    arity1: &std::collections::HashSet<String>,
    manual_variants: bool,
    auto_sources: bool,
) -> Option<String> {
    use p::TheoryItem::*;
    // `macros` is collected once by the caller (mirrors HS
    // `applyMacroInRestriction` + `parseLemmaWithMacros`, which store the
    // expanded formula separately from the original).
    match item {
        Builtins(_) | Functions(_) | Equations { .. } | Options(_) | Heuristic(_) | Tactic(_) => {
            // These are absorbed into the signature/configuration headers.
            None
        }
        Rule(r) => {
            // HS closeProtoRule (Rule.hs:97-98): `ClosedProtoRule ruE <$>
            // maybeToList (variantsProtoRule hnd ruE)` — a rule with no
            // variants yields NO closed rule, so it is absent from the
            // closed theory and never rendered.  Such rules are removed
            // from the elaborated theory in run.rs; mirror the absence here.
            if elab.rules().any(|er| er.name() == r.name) {
                Some(render_rule(r, elab, macros, arity1, manual_variants, auto_sources))
            } else {
                None
            }
        }
        IntrRule(_) => None,
        Lemma(l) => Some(render_parsed_lemma(l, macros, predicates, proved, in_file, elab, arity1)),
        Restriction(r) => Some(render_parsed_restriction(r, macros, predicates, elab, arity1)),
        Predicates(preds) => {
            // HS `prettyTheory` folds each `PredicateItem` through
            // `prettyPredicate` (TheoryObject.hs:764, 802-806):
            //   prettyPredicate p = kwPredicate <> colon <-> text (factstr ++ "<=>" ++ formulastr)
            //     factstr    = render $ prettyFact prettyLVar (pFact p)
            //     formulastr = render $ prettyLNFormula      (pFormula p)
            // `kwPredicate = keyword_ "predicate"`, `<>` is no-space append and
            // `<->` is beside-with-space, so each predicate renders on its own
            // line as `predicate: <fact><=><formula>`.
            // Each `predicate` in a `predicates:` block is added as a SEPARATE
            // `PredicateItem` in HS (commaSep1 + foldM liftedAddPredicate,
            // Parser/Signature.hs:267-268), so the theory `vsep` separates them
            // with a blank line.  The Rust parser groups them into one
            // `Predicates` item, so we reproduce that blank-line separation by
            // joining the per-predicate lines with `\n\n`.
            if preds.is_empty() {
                return None;
            }
            let lines: Vec<String> = preds.iter()
                .map(|pr| render_predicate(pr, arity1))
                .collect();
            Some(lines.join("\n\n"))
        }
        Macros(macros) => {
            if macros.is_empty() { return None; }
            Some(render_parsed_macros(macros))
        }
        FormalComment { header, body } => {
            // HS `prettyFormalComment` (lib/theory/src/Pretty.hs:19-21):
            //   prettyFormalComment ""     body = multiComment_ [body]
            //   prettyFormalComment header body = text $ header ++ "{*" ++ body ++ "*}"
            // User `section{* .. *}` / `text{* .. *}` items always carry a
            // non-empty header, so they render verbatim as
            // `header{*body*}`.  (An empty header only arises from
            // machine-injected comments via `addComment`.)
            if header.is_empty() {
                Some(format!("/*\n{}\n*/", body))
            } else {
                Some(format!("{}{{*{}*}}", header, body))
            }
        }
        IfDef { then_items, else_items, .. } => {
            // HS preprocesses `#ifdef` at the text level, so by parse time
            // the surviving branch's items are ordinary top-level theory
            // items.  RS's parser instead keeps the `#ifdef` structure as an
            // `IfDef` node, populating ONLY the live branch (`then_items` XOR
            // `else_items`).  Render that live branch in place — recursively,
            // since a branch may hold nested `#ifdef`s / rules / lemmas —
            // mirroring the same flattening `elaborate_items` does for the
            // solver (elaborate.rs:732-738).  Without this the nested rules
            // solve but never print (e.g. testParser/define.spthy).
            let mut active: Vec<&p::TheoryItem> = then_items.iter().collect();
            if let Some(else_b) = else_items { active.extend(else_b.iter()); }
            let blocks: Vec<String> = active.iter()
                .filter_map(|it| render_parsed_item(it, macros, predicates, elab, proved, in_file, arity1, manual_variants, auto_sources))
                .collect();
            if blocks.is_empty() { None } else { Some(blocks.join("\n\n")) }
        }
        _ => None,
    }
}

// =============================================================================
// Rule
// =============================================================================

/// Names of arity-1 NoEq function symbols in the closed theory signature.
/// Mirrors HS `lookupArity` reading the parser-state signature for
/// `naryOpApp`'s `k == 1` tuple-folding (Theory/Text/Parser/Term.hs:58-93).
fn arity1_noeq_names(elab: &Theory) -> std::collections::HashSet<String> {
    crate::elaborate::arity1_noeq_names(elab.signature.maude_sig())
}

/// HS `openProtoRule` (Rule.hs:65-72) returns `OpenProtoRule ruE ruleAC`
/// where `ruleAC = []` iff `equalUpToTerms cprRuleAC cprRuleE` (i.e. the
/// closed rule's AC and E forms agree on fact TAGS + lengths,
/// Theory/Model/Rule.hs:887-895), else `ruleAC = [cprRuleAC]`.
///
/// `containsManualRuleVariants` (OpenTheory.hs:584-589) is True iff some
/// (merged) rule has a non-empty `ruleAC` — i.e. some rule's `openProtoRule`
/// yields the `[cprRuleAC]` branch.  `prettyClosedTheory`
/// (ClosedTheory.hs:383) uses that to switch the WHOLE theory to the
/// "open-as-closed" renderer `prettyOpenProtoRuleAsClosedRule`
/// (OpenTheory.hs:827-851), which — for the `OpenProtoRule ruE []` (empty)
/// branch — emits NO `prettyLoopBreakers` line ("cannot show loop breakers
/// here, as we do not have the information"), whereas the
/// `OpenProtoRule _ [ruAC]` (non-empty) branch KEEPS the loop breakers.
///
/// This predicate is RS's per-rule mirror of "would `openProtoRule` yield a
/// non-empty `ruleAC`":
///   * Manual variants: a parsed `variants (modulo AC)` block on the input
///     rule produces `OpenProtoRule ruE (non-empty)` directly — always
///     counts, with or without `--auto-sources`.
///   * `--auto-sources`: `closeTheoryWithMaude` adds the synthetic
///     `AUTO_IN_*`/`AUTO_OUT_*` action facts to `cprRuleAC` ONLY (NOT
///     `cprRuleE` — `addActionClosedProtoRule`, Rule.hs:186-189), so an
///     AUTO-annotated rule has AC ≠ E up to fact tags → `equalUpToTerms`
///     False → non-empty `ruleAC`.  AC-variant substitution itself never
///     changes a fact's TAG, so the AUTO action is the only operation that
///     makes `equalUpToTerms` False here; "the elaborated rule carries an
///     `AUTO_*` action" is therefore exactly the auto-path discriminant.
///
/// Used both to compute the theory-level gate (OR over all rules) and, in
/// `render_rule`, to decide whether a trivial-AC-variant rule keeps or drops
/// its loop-breaker comment under the open renderer.
fn rule_open_ac_nonempty(
    parsed_rule: &p::Rule,
    elab_rule: Option<&crate::theory::OpenProtoRule>,
    auto_sources: bool,
) -> bool {
    // Manual `variants (modulo AC)` block on the input rule.
    if !parsed_rule.variants.is_empty() {
        return true;
    }
    if !auto_sources {
        // Non-auto path: HS does NOT unfold computed variants, and every
        // closed rule's AC form agrees with its E form up to terms, so
        // `openProtoRule` is always the empty branch.  Computed AC variants
        // do not count.
        return false;
    }
    // Auto path: the rule's AC form differs from its E form up to tags iff it
    // received an `AUTO_*` action.
    match elab_rule {
        None => false,
        Some(r) => r.rule.actions.iter().any(|f| {
            matches!(&f.tag, crate::fact::FactTag::Proto(_, name, _)
                if name.starts_with("AUTO_IN_") || name.starts_with("AUTO_OUT_"))
        }),
    }
}

/// HS `containsManualRuleVariants mergedRules` (OpenTheory.hs:584-589) as
/// computed by `prettyClosedTheory` (ClosedTheory.hs:383, 402): True iff any
/// rule's `openProtoRule` yields a non-empty AC list.  See
/// [`rule_open_ac_nonempty`].  When True the theory renders via the
/// open-as-closed path, which suppresses loop-breaker comments on
/// trivial-AC-variant rules whose AC form equals their E form.
fn contains_manual_rule_variants(
    parsed: &p::Theory,
    elaborated: &Theory,
    auto_sources: bool,
) -> bool {
    parsed.items.iter().any(|item| {
        if let p::TheoryItem::Rule(r) = item {
            let elab_rule = elaborated.rules().find(|er| er.name() == r.name);
            rule_open_ac_nonempty(r, elab_rule, auto_sources)
        } else {
            false
        }
    })
}

/// Apply the arity-1 surplus-arg pair-fold (HS `naryOpApp` `k == 1`,
/// Term.hs:84-87) to every term in a parser-AST fact.  Thin alias over the
/// shared [`crate::elaborate::rewrite_arity1_fact`] so the rule
/// pretty-printer and the lemma/formula paths share one implementation.
fn rewrite_arity1_fact(
    fa: &p::Fact,
    arity1: &std::collections::HashSet<String>,
) -> p::Fact {
    crate::elaborate::rewrite_arity1_fact(fa, arity1)
}

/// HS `prettyMacros` / `prettyMacro` (TheoryObject.hs:819-840).
///
/// HS: `prettyMacros m = keyword_ "macros:" $$ nest 4 (vcat [macros...])`
/// HS: `prettyMacro (op, args, out) =
///       vcat [ppNonEmptyList (\ds -> sep (map (nest 4) ds)) text [op++"("]
///             <-> prettyVarList args <-> text ") = " <-> prettyTerm show out]`
///
/// `ppNonEmptyList hdr pp [x] = hdr [pp x] = sep [nest 4 (text x)]`
/// = `nest 4 (text (name++"("))`.
///
/// With `keyword_ "macros:" $$ nest 4 (nest 4 "name(" <+> args <+> ") = " <+> body)`:
/// the double-nest (8 total) combined with `keyword_`'s 7-char width makes
/// `nil_above_nest` inline the content (k = -7+8 = 1 > 0), putting everything
/// on ONE line: `macros: name( args ) =  body`.
///
/// For multiple macros, each is nested 4 levels inside the outer `nest 4`,
/// giving 8-space indent on subsequent lines.
fn render_parsed_macros(macros: &[p::Macro]) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};

    let last_idx = macros.len() - 1;
    let macro_docs: Vec<Doc> = macros.iter().enumerate().map(|(i, m)| {
        // HS: `ppNonEmptyList (\ds -> sep (map (nest 4) ds)) text [op++"("]`
        // = `sep [nest 4 (text (op ++ "("))]` = `nest 4 (text (op ++ "("))`.
        let name_open = Doc::text(format!("{}(", m.name)).nest(4);
        // HS: `prettyVarList args = fsep . punctuate comma . map prettyLVar`
        // For macro args (bare LVar names, sort-prefix from hint):
        let args_parts: Vec<String> = m.args.iter().map(|v| {
            let mut s = pf::sort_prefix_from_hint(v.sort).to_string();
            s.push_str(&v.name);
            if v.idx > 0 { s.push('.'); s.push_str(&v.idx.to_string()); }
            s
        }).collect();
        let args_str = args_parts.join(", ");
        // HS: `prettyTerm (text . show) body`
        let body_str = pf::pretty_term(&m.body);
        // Build: `nest 4 "name(" <+> args <+> ") = " <+> body`
        // HS <-> = HughesPJ <+> (beside with space = beside_sp).
        let mut doc = name_open;
        if !m.args.is_empty() {
            doc = doc.beside_sp(Doc::text(args_str));
        }
        doc = doc.beside_sp(Doc::text(") = "));
        doc = doc.beside_sp(Doc::text(body_str));
        // HS: last macro has no trailing comma
        if i < last_idx {
            doc.beside(Doc::text(","))
        } else {
            doc
        }
    }).collect();

    // HS: `keyword_ "macros:" $$ nest 4 (vcat macro_docs)`
    let body = hpj::vcat(macro_docs).nest(4);
    let header = Doc::text("macros:");
    header.above(body).render()
}

/// Render a rule's attribute block `[...]`, mirroring HS `prettyRuleAttributes`
/// / `prettyRuleAttribute` (Model/Rule.hs:1191-1205).  HS emits a FIXED-order
/// `catMaybes [color, process, no_derivcheck, issapicrule, role]` joined by
/// `fsep . punctuate comma` (", "), wrapped in `[`..`]`; empty → nothing.
/// External (`x-…`) attributes are NOT in HS's list, so they are dropped.
/// Build HS `prettyRuleAttribute`'s ordered part list (Model/Rule.hs:1192-1198).
///
/// HS stores the parsed attribute LIST folded into a `RuleAttributes` STRUCT via
/// its `Semigroup` (Model/Rule.hs:370-385): for the `Maybe`-typed fields
/// (`ruleColor`, `role`) `preferRight a b = if isJust b then b else a` ⇒ the
/// LAST occurrence wins.  RS therefore takes the LAST match, not the first
/// (`rev().find_map(..)`).  `no_derivcheck`/`issapicrule` are booleans combined
/// with `||`, so order-independent (`.any(..)`).
///
/// Render order is the `catMaybes [color, process, no_derivcheck, issapicrule,
/// role]` of `prettyRuleAttribute`.  HS's attribute parser `parseAndIgnore`s
/// `process=` (Parser/Rule.hs:72), so a user-written `process=` never sets
/// `ruleProcess` and is never rendered; RS mirrors this by discarding `process=`
/// at parse time (no `RuleAttr::Process` variant exists).  `process=` is only
/// emitted by HS for SAPIC-translation-generated rules (via `ruleProcess`),
/// which RS does not yet translate, so there is nothing to render here.
fn rule_attribute_parts(attrs: &[p::RuleAttr]) -> Vec<String> {
    let mut parts: Vec<String> = Vec::new();
    // color= : HS `text "color=" <> text (rgbToHex c)`; `rgbToHex` is
    // `'#':` + lowercase 2-digit-per-channel hex (Data/Color.hs:141).
    if let Some(hex) = attrs.iter().rev().find_map(|a| match a {
        p::RuleAttr::Color(c) => Some(c), _ => None }) {
        parts.push(format!("color=#{}", hex.trim_start_matches('#').to_lowercase()));
    }
    if attrs.iter().any(|a| matches!(a, p::RuleAttr::NoDerivCheck)) {
        parts.push("no_derivcheck".to_string());
    }
    if attrs.iter().any(|a| matches!(a, p::RuleAttr::IsSapicRule)) {
        parts.push("issapicrule".to_string());
    }
    if let Some(r) = attrs.iter().rev().find_map(|a| match a {
        p::RuleAttr::Role(r) => Some(r), _ => None }) {
        parts.push(format!("role='{}'", r));
    }
    parts
}

/// Build the `prettyRuleAttributes` Doc (Model/Rule.hs:1207-1211):
///   `mempty == ruleAttributes ⇒ emptyDoc`,
///   else `hcat [text "[", prettyRuleAttribute ru, text "]"]`,
/// where `prettyRuleAttribute = fsep $ punctuate comma [..]`.  Returning a Doc
/// (not a flat string) lets the enclosing rule-header line wrap the attribute
/// list via `fsep` at the ribbon width, exactly as HughesPJ does for HS.
fn rule_attributes_doc(attrs: &[p::RuleAttr]) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let parts = rule_attribute_parts(attrs);
    if parts.is_empty() {
        return Doc::empty();
    }
    let part_docs: Vec<Doc> = parts.into_iter().map(Doc::text).collect();
    // `fsep $ punctuate comma [..]` — comma is `text ","`, and the `fsep`
    // continuation hangs at the column right after `[` (beside, no space).
    let inner = hpj::fsep(hpj::punctuate(Doc::text(","), part_docs));
    Doc::text("[").beside(inner).beside(Doc::text("]"))
}

/// Flat `[a, b, c]` rendering of the rule attributes (no `fsep` wrapping).
/// Used for the `/* rule (modulo AC) … */` comment block, whose surrounding
/// layout is built by string concatenation rather than the Doc engine.  Shares
/// the last-wins / `process=`-dropping logic via [`rule_attribute_parts`].
fn render_rule_attributes(attrs: &[p::RuleAttr]) -> String {
    let parts = rule_attribute_parts(attrs);
    if parts.is_empty() { String::new() } else { format!("[{}]", parts.join(", ")) }
}

fn render_rule(parsed_rule: &p::Rule, elab: &Theory, macros: &[p::Macro], arity1: &std::collections::HashSet<String>, manual_variants: bool, auto_sources: bool) -> String {
    let name = &parsed_rule.name;
    let mut out = String::new();
    // HS rule-header line (`prettyNamedRule`, Model/Rule.hs:1285):
    //   `prefix <-> prettyRuleName ru <> prettyRuleAttributes ru <> colon`
    // i.e. `"rule (modulo E)" <+> name <> [attrs] <> ":"`.  Routed through the
    // HughesPJ-faithful Doc engine so the attribute list's `fsep` wraps at the
    // ribbon width (the continuation hangs right after the `[`), byte-identical
    // to HS.  `<->`/`<+>` = space, `<>` = no space.
    {
        use crate::pretty_hpj::Doc;
        let header = Doc::text("rule (modulo E)")
            .beside_sp(Doc::text(name.clone()))
            .beside(rule_attributes_doc(&parsed_rule.attributes))
            .beside(Doc::text(":"));
        out.push_str(&header.render());
        out.push('\n');
    }
    // Desugar `let x = t in ...` bindings before rendering — HS does
    // this via `applyMacroInProtoRule`/`expandRuleLetBlock` so the
    // emitted rule contains no bound names from the `let` block.
    // Mirrors `apply_let_block` (`elaborate.rs:678`); same fix pattern
    // as the deriv-check (commit 3b0202bb).  HS site:
    // `lib/theory/src/TheoryObject.hs::prettyTheory` → `prettyRule` chain
    // which operates on the post-`applyMacroInProtoRule` rule.
    let desugared = crate::elaborate::apply_let_block(parsed_rule);
    // HS-faithful: an arity-1 function applied with a comma list, `f(a,b,c)`,
    // is folded by `naryOpApp`'s `k == 1` branch into `f(<a,b,c>)`
    // (Theory/Text/Parser/Term.hs:84-87).  RS's term parser keeps the surplus
    // args, so re-fold here before rendering.  See `rewrite_arity1_term`.
    // `arity1` is computed once by the caller and threaded in.
    let premises: Vec<p::Fact> =
        desugared.premises.iter().map(|f| rewrite_arity1_fact(f, arity1)).collect();
    let actions: Vec<p::Fact> =
        desugared.actions.iter().map(|f| rewrite_arity1_fact(f, arity1)).collect();
    let conclusions: Vec<p::Fact> =
        desugared.conclusions.iter().map(|f| rewrite_arity1_fact(f, arity1)).collect();
    out.push_str(&render_rule_body(
        &premises,
        &actions,
        &conclusions,
    ));

    // Look up the elaborated rule by name to decide between
    // "trivial AC variant" and the full `/* rule (modulo AC) ... */`
    // block.  HS-faithful: matches `prettyClosedProtoRule`
    // (ClosedTheory.hs:332-363).
    //
    // HS `isTrivialProtoVariantAC` (Rule.hs:761-764):
    //   variants == [emptySubstVFresh] && ps == ps' && cs == cs' && as == as' && nvs == nvs'
    //
    // i.e. trivial iff (a) the variant disjunction is just the identity
    // AND (b) the AC-normalised rule body equals the E-rule body
    // structurally.  Even when there are NO non-trivial substitutions
    // to enumerate, the AC normalisation may have rewritten terms
    // (e.g. `'g'^~ltkB^~ltkA` → `'g'^(~ltkA*~ltkB)` under DH), in which
    // case HS prints the AC body as a comment block rather than the
    // trivial-variant annotation.
    //
    // MACRO CASE (ClosedTheory.hs:334 + Rule.hs:762-764): When the theory
    // uses macros, HS's `cprRuleE` keeps the MACRO form of the rule while
    // `cprRuleAC` has the EXPANDED form (closeProtoRule runs
    // `applyMacroInRule` before `variantsProtoRule` but stores the original
    // `ruE` untouched — Rule.hs:96-98).  `isTrivialProtoVariantAC` then
    // returns `False` because `ps != ps'` (macro term ≠ expanded term).
    // RS's `opr.rule` stores the EXPANDED form (post-`expand_theory_macros`)
    // so we must additionally check whether the DISPLAY form (parsed_rule,
    // which still has macro calls) matches the elaborated body.  If they
    // differ, even a rule with no AC variants must show the AC comment block
    // containing the expanded form.
    let elab_rule = elab.rules().find(|r| r.name() == name);
    let trivial = elab_rule
        .map(|r| {
            let no_residual_substs = r.variant_substs.iter().all(|s| s.is_empty());
            // HS `isTrivialProtoVariantAC` (Rule.hs:761-764):
            //   variants == [emptySubstVFresh] && ps == ps' && as == as' && cs == cs' && nvs == nvs'
            //
            // In HS, `cprRuleE` (E-rule) and `cprRuleAC` (AC-rule) live in
            // the SAME term universe — AC smart-constructors normalise at
            // construction time everywhere, so the only difference between
            // them arises from (a) genuine non-trivial AC variants or (b)
            // macro expansion changing terms.
            //
            // In RS: `abstracted_rule = Some(ac)` iff Maude found a
            // non-trivial abstraction (reducible sub-terms, yielding a
            // different AC form) — compare the E-rule against the abstracted
            // AC form via `same_rule_body`.
            // `abstracted_rule = None` means `abstract_rule_and_variants`
            // returned `Ok(None)` (common_subst empty AND no residual
            // substs) — i.e., the AC form IS the E form.  The only remaining
            // source of divergence is macro expansion: if the display body
            // (`premises`/`actions`/`conclusions`, from `parsed_rule` before
            // macro expansion) contains macro calls, it differs from the
            // elaborated form and HS's `ps != ps'` would fire.  Detect this
            // by applying macros to the display facts and checking whether
            // any term changed (HS `applyMacroInRule` / Rule.hs:98).
            //
            // Crucially: do NOT compare rendered text across AST↔LN spaces —
            // AC ordering and nat-constant representation differ between the
            // parsed form and `lnfacts_to_parser(r.rule.*)`, producing false
            // negatives for plain rules like those in ParserTests.spthy.
            // HS `isTrivialProtoVariantAC` (Rule.hs:762-764) compares the AC
            // rule body against the E rule body (`ps==ps' && as==as' &&
            // cs==cs' && nvs==nvs'`).  `closeProtoRule` stores `cprRuleE`
            // (the ORIGINAL rule, WITH macro calls) untouched and computes
            // `cprRuleAC` from the macro-EXPANDED, variant-base rule
            // (Rule.hs:96-98).  So a macro call makes `ps != ps'` and the
            // rule is NOT trivial — it must render the AC block showing the
            // expanded body.  Detect a macro in the display (E) body by
            // expanding it: if anything changes, the E (macro) form differs
            // from the AC (expanded) form.  This holds REGARDLESS of whether
            // Maude abstracted the rule, so it gates BOTH branches below —
            // the previous code only checked it in the `None` branch, so a
            // rule that was both macro-using AND abstracted (e.g. a `^`/DH
            // rule whose body is a macro call) was wrongly called trivial
            // (regression/trace/issue777: `pk(x)='g'^x`, `Out(pk(~x))`).
            // Fast path: with no macro definitions, `apply_macros_fact` is an
            // identity rebuild (no macro can match), so the comparison below is
            // always `true`.  Skip the three deep-clone passes entirely.
            let no_macro_in_display = macros.is_empty() || {
                let mp: Vec<p::Fact> = premises.iter()
                    .map(|f| crate::macro_expand::apply_macros_fact(macros, f)).collect();
                let ma: Vec<p::Fact> = actions.iter()
                    .map(|f| crate::macro_expand::apply_macros_fact(macros, f)).collect();
                let mc: Vec<p::Fact> = conclusions.iter()
                    .map(|f| crate::macro_expand::apply_macros_fact(macros, f)).collect();
                mp == premises && ma == actions && mc == conclusions
            };
            let ac_body_matches = match &r.abstracted_rule {
                // No Maude abstraction: AC form == E form structurally, so
                // trivial iff no macro changes the display body.
                None => no_macro_in_display,
                // Maude abstracted the rule: the AC (abstracted) body must
                // match the elaborated body AND no macro may differ between
                // the display (E) and expanded (AC) forms.
                Some(ac) => same_rule_body(&r.rule, ac) && no_macro_in_display,
            };
            no_residual_substs && ac_body_matches
        })
        // INVARIANT: `render_rule` is only called when the caller has confirmed
        // `elab.rules().any(|er| er.name() == r.name)` (see `render_parsed_item`'s
        // `Rule` arm), so `elab_rule` is always `Some` here.  The `unwrap_or(true)`
        // fallback is therefore unreachable; it is retained only as a defensive
        // default (and `outer_loop_breaker`'s `unwrap_or_default()` similarly).
        .unwrap_or(true);

    // HS `prettyClosedProtoRule` (ClosedTheory.hs:337-339, 352-354) emits
    // `prettyLoopBreakers` at `nest 2` BEFORE the trailing
    // `multiComment_` (trivial) or `multiComment (prettyProtoRuleAC ...)`
    // (non-trivial) block.  We emit the same `  // loop breaker: [<n>]`
    // / `  // loop breakers: [<n>,<m>]` line here when non-empty.
    //
    // HS gate (ClosedTheory.hs:383): when `containsManualRuleVariants` holds
    // the whole theory renders via `prettyOpenProtoRuleAsClosedRule`
    // (OpenTheory.hs:827-851).  Its trivial-AC-variant branch
    // `(OpenProtoRule ruE [])` (OpenTheory.hs:828-835) shows NO loop-breaker
    // line ("cannot show loop breakers here, as we do not have the
    // information"), while the `(OpenProtoRule _ [ruAC])` branch
    // (OpenTheory.hs:836-843) KEEPS them.  A rule lands in the empty branch
    // iff its `openProtoRule` AC list is empty — see `rule_open_ac_nonempty`.
    // So under the gate, suppress the loop-breaker comment on a
    // trivial-AC-variant rule whose AC form equals its E form (no manual
    // variants, no AUTO action).  Without the gate the closed renderer
    // (`prettyClosedProtoRule`) always shows them — unchanged.
    let open_ac_nonempty = rule_open_ac_nonempty(parsed_rule, elab_rule, auto_sources);
    let show_loop_breakers = !manual_variants || open_ac_nonempty;
    let outer_loop_breaker = if show_loop_breakers {
        elab_rule
            .map(|r| render_loop_breakers_line(&r.loop_breakers, 2))
            .unwrap_or_default()
    } else {
        String::new()
    };
    if trivial {
        out.push_str("\n\n");
        out.push_str(&outer_loop_breaker);
        out.push_str("  /* has exactly the trivial AC variant */");
    } else if let Some(r) = elab_rule {
        out.push_str("\n\n");
        out.push_str(&outer_loop_breaker);
        out.push_str(&render_ac_variants_block(name, r, &parsed_rule.attributes));
    }
    out
}

/// Render HS's `prettyLoopBreakers` (Rule.hs:1295-1299):
///
/// ```haskell
/// prettyLoopBreakers i = case breakers of
///     []  -> emptyDoc
///     [_] -> lineComment_ $ "loop breaker: "  ++ show breakers
///     _   -> lineComment_ $ "loop breakers: " ++ show breakers
///   where breakers = getPremIdx <$> L.get pracLoopBreakers i
/// ```
///
/// `lineComment_ s = comment $ text "//" <-> text s` → `// <s>`.  Haskell
/// `show` on `[Int]` produces `[i,j,k]` with NO spaces after commas.
/// The trailing `\n` lets the next line attach.
fn render_loop_breakers_line(breakers: &[crate::rule::PremIdx], indent: usize) -> String {
    if breakers.is_empty() {
        return String::new();
    }
    let pad = " ".repeat(indent);
    let mut s = String::new();
    s.push_str(&pad);
    s.push_str(if breakers.len() == 1 {
        "// loop breaker: ["
    } else {
        "// loop breakers: ["
    });
    for (i, b) in breakers.iter().enumerate() {
        if i > 0 { s.push(','); }
        s.push_str(&b.0.to_string());
    }
    s.push_str("]\n");
    s
}

/// Compare the `(premises, conclusions, actions, new_vars)` of two
/// `ProtoRuleE` rules structurally.  Mirrors HS's
/// `isTrivialProtoVariantAC` body equality check (Rule.hs:764):
/// `ps == ps' && cs == cs' && as == as' && nvs == nvs'`.
///
/// Used by `render_rule` to decide whether the AC-normalised rule body
/// differs from the E-rule body — when it does, even an empty variant
/// disjunction must be rendered as a `/* rule (modulo AC) ... */`
/// comment block (since the AC form is observably different).
fn same_rule_body(
    a: &crate::rule::ProtoRuleE,
    b: &crate::rule::ProtoRuleE,
) -> bool {
    use crate::fact::LNFact;
    let same_facts = |xs: &[LNFact], ys: &[LNFact]| {
        xs.len() == ys.len()
            && xs.iter().zip(ys.iter()).all(|(f1, f2)| {
                f1.tag == f2.tag && f1.terms == f2.terms
            })
    };
    same_facts(&a.premises, &b.premises)
        && same_facts(&a.conclusions, &b.conclusions)
        && same_facts(&a.actions, &b.actions)
        && a.new_vars == b.new_vars
}

/// Render `[ prems ] --[ acts ]-> [ concs ]` body shared between the
/// modulo-E and modulo-AC renderers.  Tries single-line layout first;
/// when it overflows the 76-col threshold, wraps each clause to its own
/// line as HS's `prettyRuleRestrGen` does via `sep`.
fn render_rule_body(prems: &[p::Fact], acts: &[p::Fact], concs: &[p::Fact]) -> String {
    // AC-canonicalise the rule body BEFORE rendering — the parser produces
    // left-associative nested `BinOp(Xor, BinOp(Xor, na, k), nb)` for
    // `na ⊕ k ⊕ nb`, but HS's `fAppAC` at parse time flattens and sorts
    // the multiset, producing a different visual order (`k ⊕ nb ⊕ na`).
    // We apply the same canonicalisation to the parser AST so the rendered
    // rule body matches HS byte-for-byte.  `term_to_lnterm` already
    // canonicalises on the LNTerm path; this fixes the parser-AST path.
    use crate::elaborate::canonicalize_ac_in_pfact;
    let prems2: Vec<p::Fact> = prems.iter().map(canonicalize_ac_in_pfact).collect();
    let acts2:  Vec<p::Fact> = acts.iter().map(canonicalize_ac_in_pfact).collect();
    let concs2: Vec<p::Fact> = concs.iter().map(canonicalize_ac_in_pfact).collect();
    render_rule_body_at(&prems2, &acts2, &concs2, 3)
}

/// Render rule body at column `indent`.  Used by the AC variant block
/// (via `render_rule_body`, which prepends 2 spaces) and the top-level
/// rule (indent=3).
///
/// HS `prettyNamedRule` wraps the body as `nest 2 (prettyRule ...)`
/// (Theory/Model/Rule.hs:1286-1287), and `prettyRuleRestrGen`
/// (Rule.hs:1254-1262) lays out `sep [nest 1 (ppFactsList prems), arrow,
/// nest 1 (ppFactsList concls)]`.  The combined `nest 2 + nest 1` puts
/// the bracket `[` at col 3, the arrow at col 2.  We build the whole body
/// as one `pretty_hpj::Doc` (`rule_body_to_doc`) nested by `indent - 1`
/// (== 2 for indent=3) so the HughesPJ engine makes the `sep`/`fsep`
/// wrap decisions byte-identically to HS, instead of the hand-rolled
/// string packers.
fn render_rule_body_at(prems: &[p::Fact], acts: &[p::Fact], concs: &[p::Fact], indent: usize) -> String {
    let nest = indent.saturating_sub(1) as isize;
    pf::rule_body_to_doc(prems, acts, concs).nest(nest).render()
}

/// Render the HS `/* rule (modulo AC) <name>: ... variants (modulo AC)
/// 1. ... */` comment block.  Mirrors `prettyClosedProtoRule`'s
/// `multiComment $ prettyProtoRuleAC ruAC` branch (ClosedTheory.hs:354).
///
/// HS `prettyProtoRuleACInfo` (Rule.hs:1284-1290) emits the variants
/// sub-block via `ppVariants`, which returns `emptyDoc` when the
/// disjunction is exactly `[emptySubstVFresh]`.  So when RS's
/// `variant_substs` is empty (== HS's `[empty]`) or every subst is
/// itself empty, we emit only the rule body — no `variants (modulo AC)`
/// header — matching HS byte-for-byte for the AddPublicKey-style case
/// where the AC body differs from the E body but no residual variant
/// disjunction remains.
fn render_ac_variants_block(name: &str, rule: &crate::theory::OpenProtoRule, attrs: &[p::RuleAttr]) -> String {
    let mut s = String::new();
    s.push_str("  /*\n");
    s.push_str(&format!("  rule (modulo AC) {}{}:\n", name, render_rule_attributes(attrs)));
    // Body of the abstracted rule.  Use the abstracted rule's facts when
    // available; when `abstracted_rule` is `None` (no reducible-headed
    // sub-terms), fall back to the ELABORATED rule's facts (`rule.rule`).
    // This is the macro case: the elaborated facts have macro calls expanded
    // (e.g. `aenc(~k, pkS)` instead of `encrypt(~k, pkS)`) — exactly what HS's
    // `cprRuleAC` holds after `variantsProtoRule (applyMacroInRule macros ruE)`.
    let ac_rule = rule.abstracted_rule.as_ref().unwrap_or(&rule.rule);
    let prems = lnfacts_to_parser(&ac_rule.premises);
    let acts = lnfacts_to_parser(&ac_rule.actions);
    let concs = lnfacts_to_parser(&ac_rule.conclusions);
    // The comment block sits inside HS's `nest 2 (multiComment
    // (prettyNamedRule …))` (ClosedTheory.hs:354), so the rule body's
    // facts land at absolute column 5 (2 comment + 2 rule nest + 1
    // bracket).  CRITICAL: render the body with the ENGINE aware of the
    // full indent (nest 4 via indent=5) rather than rendering at the
    // modulo-E indent and prepending 2 literal spaces per line — the
    // prepend shifted every line +2 columns AFTER the HughesPJ width
    // decisions were made, so lines within 2 columns of the boundary
    // kept elements HS breaks (the spdm R_KE_Response tuple at visual
    // col 111 vs HS's break at 95).
    use crate::elaborate::canonicalize_ac_in_pfact;
    let prems2: Vec<p::Fact> = prems.iter().map(canonicalize_ac_in_pfact).collect();
    let acts2:  Vec<p::Fact> = acts.iter().map(canonicalize_ac_in_pfact).collect();
    let concs2: Vec<p::Fact> = concs.iter().map(canonicalize_ac_in_pfact).collect();
    let body = render_rule_body_at(&prems2, &acts2, &concs2, 5);
    s.push_str(&body);
    if !body.ends_with('\n') { s.push('\n'); }
    // HS `ppVariants (Disj [subst]) | subst == emptySubstVFresh = emptyDoc`
    // (Rule.hs:1289): skip the variants sub-block when there's no
    // residual disjunction beyond the identity.
    let has_residual_variants = rule.variant_substs.iter().any(|sub| !sub.is_empty());
    if has_residual_variants {
        s.push_str("    variants (modulo AC)\n");
        // HS `prettyDisjLNSubstsVFresh = numbered' (map ppConj substs)`
        // (SubstVFresh.hs:223-227).  Built and rendered as ONE Doc at
        // `nest 4` so the `text i <> ". " <> vcat` beside-onto-multiline
        // ribbon interaction is HS-faithful — see `variant_subst_doc`.
        s.push_str(&render_variant_substs_block(&rule.variant_substs));
    }
    // HS `prettyProtoRuleACInfo i = ppVariants ... $-$ prettyLoopBreakers i`
    // (Rule.hs:1284-1287): the loop-breaker line also appears INSIDE the
    // `multiComment` AC block, at the same nest-2 column as the rule
    // body (= absolute column 4 here, since the outer block is itself
    // at indent 2 inside `nest 2 (multiComment ...)`).
    s.push_str(&render_loop_breakers_line(&rule.loop_breakers, 4));
    s.push_str("  */");
    s
}

/// Render one entry of `prettyDisjLNSubstsVFresh` (SubstVFresh.hs:223-229)
/// as a Doc: the variant's number, then each domain var followed by
/// `= <range>`.  `n_width` is the width of the largest variant number
/// (HS `numbered`'s `nWidth = length (show n)`, Class.hs:258); each
/// variant's number is right-flushed in that width so dots line up.
///
/// HS `numbered` (Class.hs:252-259) renders each variant as
/// `pp (i, d) = text (flushRight nWidth (show i)) <> d` where `d` is
/// `text ". " <> vcat (map prettyEq bindings)`.  The whole `numbered'`
/// block sits at `nest 4` inside the rule's `multiComment`.
///
/// CRITICAL: the `text ". " <>` is a BESIDE onto the multi-line `vcat`.
/// In HughesPJ the ribbon budget for the inner (wrapped) lines is then
/// measured from the OUTER line start (the `text i` column), not from the
/// var column.  Rendering each binding STANDALONE (`entry.nest(col)`)
/// instead measures the ribbon from the var column, shifting wrap
/// decisions for terms sitting within a few columns of the ribbon
/// boundary — e.g. an 11-tuple `<x.16, …, x.26>` whose `x.26>` packs onto
/// the overflow line standalone but breaks BEFORE `x.26` (gluing `>`)
/// under the HS structure (pkcs11-templates `cannot_obtain_key` et al.).
/// So build the whole numbered conjunction as ONE Doc and render it at
/// `nest 4`, mirroring HS byte-for-byte.
fn variant_subst_doc(
    n: usize,
    subst: &tamarin_term::subst_vfresh::LNSubstVFresh,
    n_width: usize,
) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::{self as hpj, Doc};
    let bindings = subst.to_list();
    // HS `prettyEq (a,b) = prettyNTerm (Var a) $$ nest 6 (text "="
    // <-> prettyNTerm b)` (SubstVFresh.hs:228-229).  `<->` is `<+>`
    // (beside-with-space).
    let eq_docs: Vec<Doc> = bindings.iter().map(|(v, t)| {
        let term_doc = pf::term_to_doc(&lnterm_to_parser(t), &[]);
        let rhs = Doc::text("=").beside_sp(term_doc).nest(6);
        Doc::text(render_lvar(v)).above(rhs)
    }).collect();
    let conj = hpj::vcat(eq_docs);
    // HS `pp (i, d) = text (flushRight nWidth (show i)) <> d`, with
    // `d = text ". " <> conj` (from `numbered' = numbered (text "")
    // . map (text ". " <>)`).
    let label = format!("{:>width$}", n, width = n_width);
    Doc::text(label).beside(Doc::text(". ").beside(conj))
}

/// Render the full `prettyDisjLNSubstsVFresh` (numbered') block.  HS
/// `numbered vsep ds = foldr1 ($-$) $ intersperse vsep $ map pp ...` with
/// `vsep = text ""` (a blank separator line at the block's nest).
///
/// Each numbered conjunction is an independent Doc rendered at `nest 4`
/// (the `multiComment` indent) — they don't interact across the blank
/// separators, so rendering them individually is faithful — and joined by
/// the blank `"    \n"` line (HS `text ""` at nest 4).  Building each
/// conjunction as a single Doc (not per-binding) is what reproduces the
/// `text i <> ". " <> vcat` beside-onto-multiline ribbon decision.
fn render_variant_substs_block(
    substs: &[tamarin_term::subst_vfresh::LNSubstVFresh],
) -> String {
    let n_width = substs.len().to_string().len();
    let mut s = String::new();
    for (i, subst) in substs.iter().enumerate() {
        if i > 0 {
            // HS `intersperse (text "")` → a blank line at nest 4.
            s.push_str("    \n");
        }
        let mut rendered = variant_subst_doc(i + 1, subst, n_width).nest(4).render();
        rendered.push('\n');
        s.push_str(&rendered);
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

/// Render a timepoint / node id from a (root-name, idx) pair the way HS's
/// `Show LVar` (Node sort) does: `#name` for idx 0, else `#name.idx`.
/// Mirrors [`render_lvar`] for a `LSort::Node` var without constructing one;
/// used by `raw_goal_to_doc` to re-render an unannotated goal head with its
/// timepoint index preserved (HS `prettyGoal`'s `show i`).
fn render_node_id_str(name: &str, idx: u32) -> String {
    if idx == 0 { format!("#{}", name) }
    else { format!("#{}.{}", name, idx) }
}

/// Convert LNFacts (post-elaboration) to parser-AST Facts so we can
/// reuse the parser-AST fact rendering path.  Drops fact annotations.
fn lnfacts_to_parser(facts: &[crate::fact::LNFact]) -> Vec<p::Fact> {
    facts.iter().map(lnfact_to_parser).collect()
}

pub(crate) fn lnfact_to_parser(fa: &crate::fact::LNFact) -> p::Fact {
    use crate::fact::FactTag;
    let (name, persistent) = match &fa.tag {
        FactTag::Proto(crate::fact::Multiplicity::Persistent, n, _) => (n.clone(), true),
        FactTag::Proto(_, n, _) => (n.clone(), false),
        FactTag::Fresh => ("Fr".to_string(), false),
        FactTag::In => ("In".to_string(), false),
        FactTag::Out => ("Out".to_string(), false),
        // KU and KD are Persistent per factTagMultiplicity (Model/Fact.hs:358-359).
        FactTag::Ku => ("KU".to_string(), true),
        FactTag::Kd => ("KD".to_string(), true),
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

/// HughesPJ default-`style` line length used by the oracle/tactic
/// ranking path.  HS `render = P.render` (`Text.PrettyPrint.Class`
/// re-exports `P.render` from HughesPJ — Class.hs:77-78), and `P.render`
/// uses HughesPJ's default `style { lineLength = 100 }`.  This is
/// DISTINCT from the `--prove` DISPLAY width (`pretty_hpj::LINE_LENGTH`
/// = 110, set by `defaultStyle { lineLength = 110 }` in Console.hs:392).
const ORACLE_LINE_LENGTH: usize = 100;

/// HughesPJ default-`style` ribbon length used by the oracle/tactic
/// path: `ribbonsPerLine = 1.5` → `round(100/1.5) = round(66.67) = 67`.
/// DISTINCT from the display ribbon `pretty_hpj::RIBBON` = 73.
const ORACLE_RIBBON: usize = 67;

// =============================================================================
// Lemma
// =============================================================================

fn render_parsed_lemma(lem: &p::Lemma, macros: &[p::Macro], predicates: &[p::Predicate], proved: &[ProvedLemma], in_file: &str, _elab: &Theory, arity1: &std::collections::HashSet<String>) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    let mut out = String::new();
    // HS `prettyLemmaName` (Lemma.hs:91-95):
    //   `text name <-> brackets (fsep (punctuate comma attrs))`
    // The whole header line is:
    //   `kwLemma <-> prettyLemmaName lem <> colon`
    // Rendered via HughesPJ so `fsep` wraps the attributes list when the
    // line is long (e.g. `[heuristic={…}, use_induction,\n<col>reuse]`).
    let kw = Doc::text("lemma");
    let name_doc = Doc::text(lem.name.clone());
    let header_doc = if lem.attributes.is_empty() {
        kw.beside_sp(name_doc).beside(Doc::text(":"))
    } else {
        let attr_docs: Vec<Doc> = lemma_attr_docs(&lem.attributes, in_file);
        // `brackets (fsep (punctuate comma attrs))` — no space after `[`
        // (beside, not beside_sp) so fsep's continuation aligns with the
        // first attr character (i.e. right after `[`).
        let attrs_fsep = hpj::fsep(hpj::punctuate(Doc::text(","), attr_docs));
        let brackets = Doc::text("[").beside(attrs_fsep).beside(Doc::text("]"));
        kw.beside_sp(name_doc).beside_sp(brackets).beside(Doc::text(":"))
    };
    out.push_str(&header_doc.render());
    out.push('\n');

    // Lemma body shape from HS `prettyLemma` (Lemma.hs:119-122):
    //   `nest 2 $ sep [ prettyTraceQuantifier, doubleQuotes (prettyLNFormula f) ]`
    // Routed through the HS-faithful Doc engine so the quant-vs-formula
    // `sep` wrap, the formula's internal `sep`/`nest` wrapping, and the
    // continuation indents are byte-identical to HS.  The `nest 2` indent
    // is included in the rendered output (HS renders it at theory col 0).
    let quant = quantifier_keyword(&lem.trace_quantifier);
    // HS folds surplus args of arity-1 functions into a pair at parse time
    // (`naryOpApp` `k == 1`, Term.hs:84-87) — e.g. `h(H, x)` → `h(<H, x>)` —
    // so the rendered formula must do the same.  Apply BEFORE the AC sort so
    // the canonicaliser sees the folded `h(<…>)` shape.
    // `arity1` is computed once by the caller and threaded in.
    // HS `expandLemma` (TheoryObject.hs:439-446) predicate-expands the lemma
    // formula before it is stored/printed (e.g. multiset `(<)` → `∃ z. …`).
    let expanded_formula = expand_predicates_for_display(&lem.formula, predicates);
    let folded_formula = crate::elaborate::rewrite_arity1_formula(&expanded_formula, arity1);
    // HS sorts AC arguments at parse time when building `LNTerm` via `fAppAC`
    // (Term/Term/Raw.hs:118-122); our parser keeps `BinOp` trees in written
    // order, so re-establish the canonical AC operand order on the formula
    // before rendering the header (matches the guarded-block path which
    // already canonicalises via guarded.rs:684).
    let canon_formula = crate::elaborate::canonicalize_ac_in_formula(&folded_formula);
    out.push_str(&pf::lemma_header_line(quant, &canon_formula));
    out.push('\n');

    // /* guarded formula characterizing ... */
    out.push_str(&render_guarded_block(lem, macros, predicates, arity1));

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

/// Build `Doc` nodes for each lemma attribute.  Mirrors HS
/// `prettyLemmaAttribute` (Lemma.hs:97-107): each attribute becomes a
/// `text "..."` Doc; these are assembled into
/// `brackets (fsep (punctuate comma docs))` by the caller.
fn lemma_attr_docs(attrs: &[p::LemmaAttr], in_file: &str) -> Vec<crate::pretty_hpj::Doc> {
    use crate::pretty_hpj::Doc;
    let mut out = Vec::new();
    for a in attrs {
        use p::LemmaAttr::*;
        let s: Option<String> = match a {
            Sources => Some("sources".into()),
            Reuse => Some("reuse".into()),
            DiffReuse => Some("diff_reuse".into()),
            UseInduction => Some("use_induction".into()),
            HideLemma(s) => Some(format!("hide_lemma={}", s)),
            // HS `prettyLemmaAttribute (LemmaHeuristic h)` (Lemma.hs:103):
            //   `text ("heuristic=" ++ prettyGoalRankings h)`
            // Mirror space-separated, oracle-name-expanded rendering.
            Heuristic(s) => Some(format!("heuristic={}", pretty_goal_rankings(s, in_file))),
            Output(modules) => Some(format!("output=[{}]", modules.join(","))),
            Left => Some("left".into()),
            Right => Some("right".into()),
            _ => None,
        };
        if let Some(s) = s { out.push(Doc::text(s)); }
    }
    out
}

fn quantifier_keyword(q: &p::TraceQuantifier) -> &'static str {
    match q {
        p::TraceQuantifier::AllTraces => "all-traces",
        p::TraceQuantifier::ExistsTrace => "exists-trace",
    }
}

fn render_guarded_block(lem: &p::Lemma, macros: &[p::Macro], predicates: &[p::Predicate], arity1: &std::collections::HashSet<String>) -> String {
    let header = match &lem.trace_quantifier {
        p::TraceQuantifier::ExistsTrace => "guarded formula characterizing all satisfying traces:",
        p::TraceQuantifier::AllTraces => "guarded formula characterizing all counter-examples:",
    };
    // HS `parseLemmaWithMacros` (Theory/Text/Parser.hs:97-105) applies macros
    // to the lemma formula before converting to guarded form.  The guarded
    // block displays the EXPANDED formula so that macro calls like
    // `A( m(x) )` become `A( x )` (when `m(x) = x`).
    let expanded_formula = if macros.is_empty() {
        lem.formula.clone()
    } else {
        crate::macro_expand::apply_macros_formula(macros, &lem.formula)
    };
    // HS `expandLemma` predicate-expands before guarded conversion, so
    // `Pred` sugar and multiset `(<)` never reach `formulaToGuarded`.
    let expanded_formula = expand_predicates_for_display(&expanded_formula, predicates);
    // Fold surplus args of arity-1 functions into a pair (HS `naryOpApp`
    // `k == 1`, Term.hs:84-87) so the guarded form carries `h(<…>)` not
    // `h(…)`.  Same fold as the header path above.
    let expanded_formula = crate::elaborate::rewrite_arity1_formula(&expanded_formula, arity1);
    let gf = match crate::guarded::formula_to_guarded(&expanded_formula) {
        Ok(g) => g,
        Err(e) => {
            // HS Lemma.hs:132-134: `multiComment (text "conversion to
            // guarded formula failed:" $$ nest 2 err)` where `err` is the
            // full `ppError` doc (Guarded.hs:479): the error text, the
            // quoted failing sub-formula (Guarded.hs:508-514/561-563 both
            // include `ppFormula f0`), then "in the formula" + the quoted
            // formula passed to `formulaToGuarded` (nest 2 . doubleQuotes).
            let mut block = String::from("/*\nconversion to guarded formula failed:\n");
            for line in e.message.lines() {
                block.push_str("  ");
                block.push_str(line);
                block.push('\n');
            }
            let full_text = crate::pretty_formula::pretty_formula(&expanded_formula);
            let sub_text = e.subject_formula.as_ref()
                .map(crate::pretty_formula::pretty_formula)
                .unwrap_or_else(|| full_text.clone());
            block.push_str("    \"");
            block.push_str(&sub_text);
            block.push_str("\"\n  in the formula\n    \"");
            block.push_str(&full_text);
            block.push_str("\"\n*/");
            return block;
        }
    };
    // For all-traces lemmas, HS prints the negated guarded formula
    // (`gnot gf`).  The result is the "counter-example" form.
    //
    // The guarded block is rendered inside `multiComment` at col 0 with
    // the formula wrapped in `doubleQuotes` (HS Lemma.hs:138/141:
    // `doubleQuotes (prettyGuarded gf)`).  `pretty_guarded_doublequoted`
    // models the `"` as a real `Doc` `beside`, so HughesPJ's column-shift
    // puts continuation lines at the formula's start column (1) — exactly
    // like HS's `"\"" <> prettyGuarded <> "\""`.
    let to_render = match &lem.trace_quantifier {
        p::TraceQuantifier::ExistsTrace => gf,
        p::TraceQuantifier::AllTraces => crate::guarded::gnot(&gf),
    };
    let quoted = pf::pretty_guarded_doublequoted(&to_render);
    format!("/*\n{}\n{}\n*/", header, quoted)
}

// =============================================================================
// Restriction
// =============================================================================

/// Predicate-expand a formula for DISPLAY, mirroring HS `expandFormula`
/// (Theory/Syntactic/Predicate.hs:82-93) as applied by `expandRestriction` /
/// `expandLemma` (TheoryObject.hs:430-446).  This rewrites `Pred` sugar — and
/// the builtin multiset `(<)` / `Smaller` — into the surviving atom forms, so
/// the displayed lemma/restriction text matches HS byte-for-byte.  The parse
/// already succeeded (so every referenced predicate is defined and arities
/// match); should expansion nonetheless error, fall back to the un-expanded
/// formula rather than panic.
fn expand_predicates_for_display(f: &p::Formula, predicates: &[p::Predicate]) -> p::Formula {
    crate::predicate_expand::expand_formula(f, predicates).unwrap_or_else(|_| f.clone())
}

fn render_parsed_restriction(r: &p::Restriction, macros: &[p::Macro], predicates: &[p::Predicate], _elab: &Theory, arity1: &std::collections::HashSet<String>) -> String {
    // HS `prettyRestriction` (TheoryObject.hs:846-857):
    //   The `Restriction` carries two formulas after `applyMacroInRestriction`:
    //   - `_rstrFormula`         = macro-EXPANDED formula  (displayed in expanded block)
    //   - `_rstrOriginalFormula` = original macro-form     (displayed on top)
    //   HS always has `ogFormula = Just _` (applyMacroInRestriction sets it
    //   even when there are no macros: `Just $ maybe f id ofm`).
    //
    // RS's `r.formula` is the parser-form (macro calls present).  Apply
    // the theory's macros to get the expanded formula used in the block.
    // Fold arity-1 surplus args into a pair first (HS `naryOpApp` `k == 1`,
    // Term.hs:84-87), exactly as the parser would — applies to BOTH the
    // original and expanded displays since HS folds at parse time.
    //
    // HS `expandRestriction` (TheoryObject.hs:430-437) predicate-expands BOTH
    // formulas (`f'`, `ofm'`), so e.g. the multiset `(<)` operator is rewritten
    // to `∃ z. r = l ++ z` BEFORE the formula is stored — and thus before it is
    // printed.  Mirror that here on both displayed formulas.
    // `arity1` is computed once by the caller and threaded in.
    let original = crate::elaborate::rewrite_arity1_formula(
        &expand_predicates_for_display(&r.formula, predicates), arity1);
    let expanded = if macros.is_empty() {
        original.clone()
    } else {
        crate::elaborate::rewrite_arity1_formula(
            &expand_predicates_for_display(
                &crate::macro_expand::apply_macros_formula(macros, &r.formula), predicates),
            arity1)
    };
    let mut out = String::new();
    out.push_str("restriction ");
    out.push_str(&r.name);
    out.push_str(":\n");
    // Top-level display: original formula (macro form) — `fromMaybe expandedFormula ogFormula`.
    // Since ogFormula = Just original, this always shows `r.formula` (macro form).
    out.push_str(&pf::formula_doublequoted_nested(&original, 2));
    // Safety annotation: `if safety then "// safety formula" else emptyDoc`.
    // HS checks `isSafetyFormula (formulaToGuarded_ expandedFormula)`.
    if is_safety_formula(&expanded) {
        out.push_str("\n  // safety formula");
    }
    // Expanded formula block (always emitted — HS always has ogFormula = Just _).
    out.push_str("\n\n  /*\n  expanded formula:\n");
    out.push_str(&pf::formula_doublequoted_nested(&expanded, 2));
    out.push_str("\n  */");
    out
}

/// Render one predicate item, mirroring HS `prettyPredicate`
/// (TheoryObject.hs:802-806):
///   prettyPredicate p = kwPredicate <> colon <-> text (factstr ++ "<=>" ++ formulastr)
///     factstr    = render $ prettyFact prettyLVar (pFact p)
///     formulastr = render $ prettyLNFormula      (pFormula p)
/// `kwPredicate <> colon` is `predicate:` (no space), `<->` adds one space,
/// then the combined `<fact><=><formula>` text (no spaces around `<=>`).
/// The fact/formula terms are arity-1 folded (HS `naryOpApp` k==1 at parse
/// time), matching the rule/restriction renderers.
fn render_predicate(pr: &p::Predicate, arity1: &std::collections::HashSet<String>) -> String {
    let fact = crate::elaborate::rewrite_arity1_fact(&pr.fact, arity1);
    let formula = crate::elaborate::rewrite_arity1_formula(&pr.formula, arity1);
    // HS `render` lays each sub-doc out at width 110 from column 0 (factstr and
    // formulastr are rendered INDEPENDENTLY, then concatenated as plain text),
    // so route the formula through the Doc engine starting at column 0.
    let factstr = reparse_fact_doc(&fact).render();
    let formulastr = pf::pretty_formula_wrapped(&formula, 0);
    format!("predicate: {}<=>{}", factstr, formulastr)
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

pub(crate) fn render_lnterm(t: &tamarin_term::lterm::LNTerm) -> String {
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
    //
    // HS `prettyIncrementalProof` (ProofSkeleton.hs:80-84) renders each
    // step as `sep [prettyProofMethod, if Nothing then "/* unannotated
    // */" else empty]`.  A step whose constraint system could not be
    // re-attached during the close-time `checkProof` replay
    // (`annotated == false`) gets the `/* unannotated */` comment beside
    // its method.  Fully-searched / successfully-replayed steps stay
    // `Just System` (annotated == true) and render without it.
    // HS `prettyIncrementalProof.ppStep` (ProofSkeleton.hs:80-84) wraps
    // every step as `sep [prettyProofMethod, comment-or-empty]`, where
    // `comment = multiComment_ ["unannotated"]` iff `psInfo == Nothing`
    // (`annotated == false`).  `sep` lays method+comment inline when they
    // fit the ribbon, else drops the comment to its OWN line at the
    // step's base indent (`depth*2`).  We build the method as a Doc and
    // run it through the same HughesPJ engine so the break is
    // byte-identical to HS — replacing the prior literal-string append
    // that always kept the comment inline.
    let base = depth * 2;
    let annotated = node.annotated;
    let cases: Vec<(&String, &crate::constraint::solver::search::ProofNode)> =
        node.children.iter().collect();

    match (&node.method, cases.as_slice()) {
        (ProofMethod::Finished(MR::Solved), []) => {
            let doc = pp_step_doc(&node.method, base, "");
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, ""));
        }
        (_, []) => {
            // No children: `by <step>` form.  HS `ppCases ps [] =
            // prettyCase ps (kwBy <> text " ") <> prettyStep ps` (non-diff
            // `prettyProofWith`, Proof.hs:1065-1066) — `<>` is beside, so the
            // `prettyStep` Doc is laid
            // out BESIDE `by `.  For a `SolveGoal` step the goal can wrap, and
            // HughesPJ counts the `by ` (3 cols) toward the ribbon when
            // deciding the `fsep`/`sep` break — so we must render `by ` as
            // line CONTENT, not as part of the indent (see `solve_line_render`;
            // the NAXOS/KAS2 `Match( a,` / `<…>` divergence).  The `by `
            // prefix is laid out by `step_line_with_unann` BESIDE the WHOLE
            // `sep [method, comment]` (HS `prettyCase ps (kwBy<>" ") <>
            // prettyStep ps`), so a dropped `/* unannotated */` aligns at
            // `base + len("by ")` (= +3), not `base`.  `beside` still shifts
            // the method's own wrapped continuation columns by the prefix
            // width and counts it toward the ribbon, so the method lines stay
            // byte-identical to the old baked-in layout.
            let doc = pp_step_doc(&node.method, base, "");
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, "by "));
        }
        (_, [(label, child)]) if label.is_empty() => {
            let doc = pp_step_doc(&node.method, base, "");
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, ""));
            out.push('\n');
            // HS `ppCases ps [("", prf)] = prettyStep ps $-$ ppPrf prf`
            // (non-diff `prettyProofWith`, Proof.hs:1067).  `$-$` is "above" — the child is rendered
            // at the SAME indent column as the parent step.  In our output
            // model the caller writes the indent before calling pp_proof, so
            // we reproduce that here: write the same `depth`-level indent
            // before recursing into the child.
            out.push_str(&"  ".repeat(depth));
            pp_proof(child, out, depth);
        }
        (_, multi) => {
            let doc = pp_step_doc(&node.method, base, "");
            out.push_str(&pf::step_line_with_unann(doc, base, annotated, ""));
            for (i, (name, child)) in multi.iter().enumerate() {
                if i > 0 {
                    // HS Proof.hs:1070 (non-diff `prettyProofWith`): `intersperse (prettyCase ps kwNext)`
                    // — `next` is a sibling of `solve`/`qed`, so it sits at
                    // the parent's indent (`depth*2`), not column 0.
                    out.push('\n');
                    out.push_str(&"  ".repeat(depth));
                    out.push_str("next");
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

/// Build the proof-step method as a `pretty_hpj::Doc`, mirroring
/// `pp_step_at` but yielding a Doc (so it can be combined with the
/// `/* unannotated */` comment via `sep`, per HS
/// `prettyIncrementalProof.ppStep`, ProofSkeleton.hs:80-84).
///
/// `prefix` is the leaf-step keyword (`"by "` for childless steps, `""`
/// otherwise); it is laid out BESIDE the method as line content (NOT
/// folded into the indent) so HughesPJ counts its columns toward the
/// ribbon, identical to `solve_line_render`/`pp_proof`'s string path.
///
/// `base_indent` is the column where the step's first char lands; used
/// by the SolveGoal goal builders so wrapped continuation lines indent
/// to the column after `solve( ` (= base_indent + len(prefix) + 7).
fn pp_step_doc(
    m: &crate::constraint::solver::proof_method::ProofMethod,
    base_indent: usize,
    prefix: &str,
) -> crate::pretty_hpj::Doc {
    use crate::constraint::constraints::Goal;
    use crate::constraint::solver::proof_method::ProofMethod as PM;
    use crate::pretty_hpj::Doc;
    // `solve( <goal> )` builds its own goal Doc; everything else is a
    // flat string with no internal wrapping, so `Doc::text` of the
    // string form is faithful.
    let body = match m {
        PM::SolveGoal(g) => {
            let inner = match g {
                Goal::Disj(d) if !d.0.is_empty() => pf::disj_goal_to_doc(&d.0),
                _ => solve_goal_to_doc(g),
            };
            Doc::text("solve(")
                .beside_sp(inner)
                .beside_sp(Doc::text(")"))
        }
        // A `RawSolve` is the display-only method kept for an unannotated
        // (replayed) subtree (replay.rs `parsed_to_unannotated`).  HS's
        // `noSystemPrf` (Proof.hs:469 `mapProofInfo (\i -> (Just i,
        // Nothing))`) keeps the STRUCTURED `ProofMethod` (`SolveGoal goal`)
        // unchanged and re-renders it via `prettyProofMethod`
        // (ProofMethod.hs:1174) → `prettyGoal` (Constraints.hs:273-287),
        // which RE-WRAPS the goal at the current `lineLength`/`ribbon`.  The
        // earlier RS path kept the goal's VERBATIM text from the input
        // `.spthy` file, so any wrapping the stored file carried (e.g. an
        // `∃ #j.\n  (body)` break, or a fact arg-list broken before `)`)
        // leaked into the output where HS reflows it inline.  We mirror HS by
        // re-parsing the goal text into a structured Doc and laying it out
        // through the same engine the live `SolveGoal` path uses.
        PM::RawSolve(raw) => raw_solve_to_doc(raw),
        // For non-SolveGoal methods the goal indent argument is unused;
        // reuse `pp_step_at`'s string form.  `by `-prefixed leaf steps
        // (e.g. `by sorry`) render the method at the post-prefix column.
        _ => Doc::text(pp_step_at(m, base_indent + prefix.chars().count())),
    };
    if prefix.is_empty() {
        body
    } else {
        Doc::text(prefix).beside(body)
    }
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
            use crate::constraint::constraints::Goal;
            // HS `prettyProofMethod` (ProofMethod.hs:1174; SolveGoal case 1182):
            //   SolveGoal goal ->
            //     keyword_ "solve(" <-> prettyGoal goal <-> keyword_ ")"
            // For a non-empty `DisjG`, `prettyGoal` is
            //   `fsep $ punctuate "  ∥" (map (nest 1 . parens . prettyGuarded) gfs)`
            // (Constraints.hs:281-283) — a multi-disjunct guarded formula
            // that HS wraps across lines inside the global proof-tree Doc.
            // Route this whole `solve( ... )` line through the HS-faithful
            // Doc engine so the `fsep`/`sep`/`nest` wrap decisions and the
            // continuation-line indents (col `indent + 7`, after `solve( `)
            // are byte-identical to HS.
            if let Goal::Disj(d) = g {
                if !d.0.is_empty() {
                    return pf::solve_disj_goal_line(&d.0, indent);
                }
            }
            // ActionG/ChainG/PremiseG/SplitG/SubtermG: route the whole
            // `solve( <goal> )` line through the same HS-faithful Doc engine
            // as DisjG (4a6b6d5a) so `prettyLNFact`'s `nestShort'` wrapping
            // (Fact.hs:539-544) and the `<+>` beside column-shift indent the
            // goal's continuation lines to the column after `solve( `
            // (= indent+7), byte-identical to HS.  HS `prettyGoal`
            // (Constraints.hs:273-287).
            let goal_doc = solve_goal_to_doc(g);
            pf::solve_goal_line_from_doc(goal_doc, indent)
        }
        PM::Invalidated => {
            // HS `prettyProofMethod` (ProofMethod.hs):
            //   Invalidated -> lineComment_
            //     "proof may have been invalidated by editing a reuse lemma above. You should "
            // Note the trailing space inside the string literal — HS
            // `lineComment_` renders the verbatim text after `// `.
            "// proof may have been invalidated by editing a reuse lemma above. You should ".to_string()
        }
        PM::RawSolve(inner) => {
            // Display-only: skeleton raw text preserved for unannotated
            // subtrees (replay.rs `parsed_to_unannotated`).  Mirrors
            // HS `noSystemPrf` (Proof.hs:469) which keeps the original
            // ProofMethod value verbatim.  Output: `solve( <inner> )`.
            // Trim the inner text: the parser's `read_balanced_paren`
            // returns the content between `( ... )` which may carry a
            // trailing space → `solve(  ...  )` if we don't trim.
            format!("solve( {} )", inner.trim())
        }
    }
}

/// Render a `Goal` for the oracle/tactic ranking path.  This is HS's
/// `render $ prettyGoal g` from `ProofMethod.hs:607,702` (oracle stdin)
/// and `Tactics.hs` `pg = concat . lines . render $ prettyGoal agoal`
/// (tactic regex string).  All consumers (goals.rs oracle stdin /
/// `apply_ranking_fn` / `tactic_pg`) immediately apply `concat . lines`
/// to drop the newlines, so the byte-for-byte requirement is on each
/// line's internal text (leading indent spaces survive the `concat`).
///
/// Width: the oracle/tactic path uses plain `render = P.render`
/// (`Theory.Text.Pretty` re-exports `Text.PrettyPrint.Class.render`,
/// which is `P.render` from HughesPJ — Class.hs:77-78).  `P.render`
/// uses HughesPJ's DEFAULT `style`: `lineLength = 100`,
/// `ribbonsPerLine = 1.5` → `ribbon = round(100/1.5) = 67`.  This is
/// DISTINCT from the `--prove` display path, which uses
/// `renderStyle (defaultStyle { lineLength = 110 })` (Console.hs:392),
/// i.e. width 110 / ribbon 73 (`pretty_hpj::LINE_LENGTH`/`RIBBON`).
/// We build the goal via the same `solve_goal_to_doc` builder the
/// display path uses, then render it at the oracle width.
pub(crate) fn render_goal_for_oracle(g: &crate::constraint::constraints::Goal) -> String {
    // HS oracle stdin line = `show i ++": "++ (concat . lines . render $
    // prettyGoal g)` (ProofMethod.hs:607).  HS `render` is HughesPJ's plain
    // `render` (= `fullRender`/`display` from line column 0), which APPLIES a
    // top-level `nest` to the FIRST line — so e.g. `prettyGoal (DisjG ..)` =
    // `fsep (map (nest 1 . parens . prettyGuarded) gfs)` renders with a LEADING
    // SPACE (`" (#a < #b)  ∥ .."`).  Use `render_with` (HughesPJ `lay`, indent
    // 0) here, NOT `render_at` (`lay2`, continuation mode) — `lay2` discards a
    // leading `Nest`, dropping that space and feeding the oracle a DIFFERENT
    // goal string than HS, which can change the oracle's ranking decisions.
    // (The `--prove` display path renders the disjunction AFTER a `solve( `
    // prefix, so the nest is never at the doc start there and both lay/lay2
    // agree — this divergence is oracle-stdin-specific.)
    solve_goal_to_doc(g).render_with(ORACLE_LINE_LENGTH, ORACLE_RIBBON)
}

/// Build the `solve( <goal> )` Doc for an unannotated (replayed) step from
/// its raw goal text, re-rendering through the HS-faithful Doc engine.
///
/// HS `noSystemPrf` (Proof.hs:469) keeps the parsed `SolveGoal goal`
/// structured, so `prettyProofMethod`/`prettyGoal` re-wraps it fresh.  We
/// recover the structure from the raw `solve(...)` inner text and route it
/// through the SAME builders the live-goal path uses
/// (`pf::fact_doc`/`pf::term_doc`/`pf::disj_goal_to_doc`), so the wrapping
/// is byte-identical to HS regardless of how the stored `.spthy` was laid
/// out.  Goal shapes we cannot structurally recover (chain / `Raw`) fall
/// back to the verbatim text — those goals are short and never wrap, so HS
/// renders them on one line too.
fn raw_solve_to_doc(raw: &str) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::Doc;
    let goal_doc = raw_goal_to_doc(raw);
    Doc::text("solve(")
        .beside_sp(goal_doc)
        .beside_sp(Doc::text(")"))
}

/// Re-render the goal text inside a `solve( ... )` (the part between the
/// parens) as a Doc.  Mirrors HS `prettyGoal` (Constraints.hs:273-287) by
/// reconstructing each goal kind from `parse_goal_spec`
/// (proof_tree.rs:278) and laying it out with the live-goal builders.
fn raw_goal_to_doc(raw: &str) -> crate::pretty_hpj::Doc {
    use crate::pretty_hpj::Doc;
    use tamarin_parser::ast::GoalSpec;
    use tamarin_parser::proof_tree::parse_goal_spec;
    use tamarin_parser::parser::{parse_formula_str, parse_term_str};
    use crate::guarded::formula_to_guarded;

    let trimmed = raw.trim();
    match parse_goal_spec(trimmed) {
        // `prettyGoal (ActionG i fa) = prettyFact fa <-> "@" <-> show i`.
        // `show i` (HS `Show LVar`) keeps the timepoint idx: `#vk.6`, not
        // `#vk`.  Reconstruct the node LVar and render via `render_lvar`
        // (the same renderer the live-goal path uses, render_node_id) so
        // the head is byte-identical to HS's re-render.
        GoalSpec::Action { fact, time_var, time_idx } => {
            reparse_fact_doc(&fact)
                .beside_sp(Doc::text("@"))
                .beside_sp(Doc::text(render_node_id_str(&time_var, time_idx)))
        }
        // `prettyGoal (PremiseG (i, PremIdx v) fa) =
        //    prettyLNFact fa <-> "▶"<>subscript v <-> prettyNodeId i`.
        GoalSpec::Premise { fact, prem_idx, time_var, time_idx } => {
            reparse_fact_doc(&fact)
                .beside_sp(Doc::text(format!("\u{25B6}{}", goal_subscript(prem_idx))))
                .beside_sp(Doc::text(render_node_id_str(&time_var, time_idx)))
        }
        // `prettyGoal (DisjG (Disj gfs)) =
        //    fsep $ punctuate "  ∥" (map (nest 1 . parens . prettyGuarded) gfs)`.
        // Re-parse each disjunct's text into a Guarded and route through the
        // same `disj_goal_to_doc` the live path uses.  If ANY disjunct fails
        // to re-parse, fall back to verbatim (no structural loss vs the prior
        // behaviour for the rare unparseable case).
        GoalSpec::Disj { .. } => {
            match parse_disjuncts_to_guarded(trimmed) {
                Some(gfs) => pf::disj_goal_to_doc(&gfs),
                None => Doc::text(trimmed),
            }
        }
        // `prettyGoal (SubtermG (l,r)) = prettyLNTerm l <-> "⊏" <-> prettyLNTerm r`.
        GoalSpec::Subterm { small_raw, big_raw } => {
            match (parse_term_str(small_raw.trim()), parse_term_str(big_raw.trim())) {
                (Ok(l), Ok(r)) => pf::term_doc(&l)
                    .beside_sp(Doc::text("\u{228F}"))
                    .beside_sp(pf::term_doc(&r)),
                _ => Doc::text(trimmed),
            }
        }
        // `splitEqs(N)` and `(#i,n) ~~> (#j,m)` never wrap; keep verbatim.
        GoalSpec::Split { .. } | GoalSpec::Chain { .. } => Doc::text(trimmed),
        // Unrecognised goal shapes: a lone guarded formula goal (e.g. a
        // single quantified alt) parses here.  Try formula→guarded so it
        // re-wraps like HS's `prettyGuarded`; else keep verbatim.
        GoalSpec::Raw(_) => {
            match parse_formula_str(trimmed).ok().and_then(|f| formula_to_guarded(&f).ok()) {
                Some(g) => pf::disj_goal_to_doc(std::slice::from_ref(&g)),
                None => Doc::text(trimmed),
            }
        }
    }
}

/// Render an Action/Premise goal's `Fact` to a Doc, RE-PARSING each
/// argument's term text into a structured term first.
///
/// `parse_goal_spec`'s Action/Premise parser (`build_fact`,
/// proof_tree.rs:670) is a goal-MATCHING shim — it does NOT parse the
/// argument terms, instead stuffing each top-level-comma-split arg's RAW
/// TEXT (incl. any stored newlines / wrapping) into a `Term::Var` name.
/// Rendering that via `pf::fact_doc` directly would echo the stored layout
/// verbatim (the dnp3 `senc(<…>)` tuple wrapped exactly as the input file
/// had it).  Here we re-parse each arg's text with `parse_term_str` so the
/// fact's terms get their real structure and re-wrap through the Doc engine
/// like HS's `prettyLNFact`.  If any arg fails to re-parse we keep that
/// arg's raw text (it still renders, just not re-flowed) — a strictly
/// no-worse fallback.
fn reparse_fact_doc(fact: &tamarin_parser::ast::Fact) -> crate::pretty_hpj::Doc {
    use tamarin_parser::ast::{Fact, Term};
    use tamarin_parser::parser::parse_term_str;
    let args: Vec<Term> = fact.args.iter().map(|a| match a {
        // `build_fact` stored the raw arg text as a `Var` name; re-parse it.
        Term::Var(v) => parse_term_str(v.name.trim()).unwrap_or_else(|_| a.clone()),
        other => other.clone(),
    }).collect();
    let reparsed = Fact {
        persistent: fact.persistent,
        name: fact.name.clone(),
        args,
        annotations: fact.annotations.clone(),
    };
    pf::fact_doc(&reparsed)
}

/// Split the `solve(...)` disjunction text at top-level `∥`, re-parsing
/// each disjunct as a guarded formula (HS `disjSplitGoal` parses each
/// disjunct as a full `Guarded`, Theory/Text/Parser/Proof.hs:61).  Returns
/// `None` if any disjunct fails to parse (caller falls back to verbatim).
fn parse_disjuncts_to_guarded(text: &str) -> Option<Vec<crate::guarded::Guarded>> {
    use tamarin_parser::parser::parse_formula_str;
    use crate::guarded::formula_to_guarded;
    let parts = split_top_level_disj_par(text);
    let mut out = Vec::with_capacity(parts.len());
    for p in &parts {
        let inner = strip_one_outer_paren(p.trim());
        let f = parse_formula_str(inner).ok()?;
        let g = formula_to_guarded(&f).ok()?;
        out.push(g);
    }
    Some(out)
}

/// Split `s` at top-level `∥` (U+2225), ignoring separators inside
/// `()/[]/{}` brackets.  Mirrors the parser's `split_top_level_disj`
/// (proof_tree.rs:348) so the disjunct boundaries match `parse_goal_spec`'s.
fn split_top_level_disj_par(s: &str) -> Vec<String> {
    const SEP: char = '\u{2225}';
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut depth: i32 = 0;
    for c in s.chars() {
        match c {
            '(' | '[' | '{' => { depth += 1; cur.push(c); }
            ')' | ']' | '}' => { depth -= 1; cur.push(c); }
            _ if c == SEP && depth == 0 => out.push(std::mem::take(&mut cur)),
            _ => cur.push(c),
        }
    }
    out.push(cur);
    out
}

/// Strip ONE balanced outer `(...)` layer if the whole string is wrapped
/// in it; otherwise return the string unchanged.  Each disjunct in a
/// `solve( (g1) ∥ (g2) )` carries its own `opParens` wrap (HS `map opParens`
/// in `prettyGuarded`'s GDisj, Guarded.hs:836), which `parse_formula_str`
/// would otherwise re-wrap — strip it so the re-parsed guarded matches the
/// live-goal `Guarded` (which has no outer-paren node).
fn strip_one_outer_paren(s: &str) -> &str {
    let s = s.trim();
    let bytes = s.as_bytes();
    if bytes.len() < 2 || bytes[0] != b'(' || bytes[bytes.len() - 1] != b')' {
        return s;
    }
    let mut depth: i32 = 0;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                // A depth-0 close before the final char means the leading
                // `(` does NOT match the trailing `)` — don't strip.
                if depth == 0 && i != s.len() - 1 {
                    return s;
                }
            }
            _ => {}
        }
    }
    &s[1..s.len() - 1]
}

/// Build a `pretty_hpj::Doc` for a non-DisjG `Goal`, mirroring HS
/// `prettyGoal` (Constraints.hs:273-287).  `<->` = `<+>` (beside-with-
/// space).  Facts go through `prettyLNFact`'s `nestShort'` wrapping (via
/// `pf::fact_doc`); terms through `prettyLNTerm` (via `pf::term_doc`);
/// node-ids / node-conc / node-prem are atomic strings (HS `prettyNodeId`
/// is `text . show`).  The DisjG case is handled by `solve_disj_goal_line`
/// upstream and never reaches here.
fn solve_goal_to_doc(
    g: &crate::constraint::constraints::Goal,
) -> crate::pretty_hpj::Doc {
    use crate::constraint::constraints::Goal;
    use crate::rule::PremIdx;
    use crate::pretty_hpj::Doc;
    match g {
        // `prettyGoal (ActionG i fa) = prettyNAtom (Action (varTerm i) fa)`
        // = `prettyFact fa <-> opAction <-> text (show i)` (Atom.hs:216-217),
        // `opAction = "@"` (Pretty.hs:170).
        Goal::Action(i, fa) => {
            let nid = render_node_id(i);
            pf::fact_doc(&lnfact_to_parser(fa))
                .beside_sp(Doc::text("@"))
                .beside_sp(Doc::text(nid))
        }
        // `prettyGoal (ChainG c p) =
        //    prettyNodeConc c <-> operator_ "~~>" <-> prettyNodePrem p`.
        Goal::Chain(c, p) => {
            Doc::text(render_node_conc(c))
                .beside_sp(Doc::text("~~>"))
                .beside_sp(Doc::text(render_node_prem(p)))
        }
        // `prettyGoal (PremiseG (i, PremIdx v) fa) =
        //    prettyLNFact fa <-> text ("▶" ++ subscript (show v)) <-> prettyNodeId i`.
        Goal::Premise((i, PremIdx(v)), fa) => {
            let sub = goal_subscript(*v);
            let nid = render_node_id(i);
            pf::fact_doc(&lnfact_to_parser(fa))
                .beside_sp(Doc::text(format!("\u{25B6}{}", sub)))
                .beside_sp(Doc::text(nid))
        }
        // `prettyGoal (SplitG x) = text "splitEqs" <> parens (text (show ...))`
        // `<>` = no space → `splitEqs(N)`.
        Goal::Split(id) => Doc::text(format!("splitEqs({})", id.0)),
        // `prettyGoal (DisjG (Disj [])) = text "Disj" <-> operator_ "(⊥)"`.
        Goal::Disj(d) if d.0.is_empty() => {
            Doc::text("Disj").beside_sp(Doc::text("(\u{22A5})"))
        }
        // Non-empty DisjG is routed via `solve_disj_goal_line` upstream;
        // fall back to the Doc form for safety.
        Goal::Disj(d) => pf::disj_goal_to_doc(&d.0),
        // `prettyGoal (SubtermG (l,r)) =
        //    prettyLNTerm l <-> operator_ "⊏" <-> prettyLNTerm r`.
        Goal::Subterm((l, r)) => {
            pf::term_doc(&lnterm_to_parser(l))
                .beside_sp(Doc::text("\u{228F}"))
                .beside_sp(pf::term_doc(&lnterm_to_parser(r)))
        }
    }
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

#[cfg(test)]
mod oracle_goal_tests {
    use super::*;
    use crate::constraint::constraints::Goal;
    use crate::fact::{Fact, FactTag, LNFact, Multiplicity};
    use crate::rule::PremIdx;
    use tamarin_term::lterm::{LSort, LVar, LNTerm};
    use tamarin_term::vterm::Lit;
    use tamarin_term::term::Term;

    fn fresh(name: &str) -> LNTerm {
        Term::Lit(Lit::Var(LVar::new(name, LSort::Fresh, 0)))
    }

    /// The oracle/tactic ranking string is HS's `concat . lines . render`,
    /// where `render = P.render` uses HughesPJ's default `style`
    /// (lineLength = 100, ribbon = 67) — NOT the `--prove` DISPLAY width
    /// (110 / 73, used by `renderStyle (defaultStyle { lineLength = 110 })`
    /// in Console.hs:392).
    ///
    /// Authentic ground truth (captured from the v1.13.0 HS prover with an
    /// oracle that echoes stdin, on a crafted theory whose premise goal is
    /// 69 columns wide):
    ///
    /// ```text
    /// 0: !KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb) ▶₀ #l
    /// ```
    ///
    /// Note the absence of a space before the closing `)`: at ribbon 67 the
    /// fact's `nestShort'` (Fact.hs:539-544) wraps, pushing `)` onto its own
    /// line at column 0, and `concat . lines` then joins it directly to the
    /// preceding `~msgbbbbbbbbbbbbbbbbbbbb`.  At the DISPLAY ribbon 73 the same
    /// goal stays inline (`... ~msgbbbbbbbbbbbbbbbbbbbb )`, with the space).
    /// This distinguishes the two widths and pins the behavioural fix.
    #[test]
    fn premise_goal_wraps_at_oracle_ribbon_67() {
        // !KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb ) ▶₀ #l
        let fa: LNFact = Fact::new(
            FactTag::Proto(Multiplicity::Persistent, "KeyStore0".into(), 2),
            vec![fresh("keyaaaaaaaaaaaaaaaaaaaa"), fresh("msgbbbbbbbbbbbbbbbbbbbb")],
        );
        let node = LVar::new("l", LSort::Node, 0);
        let goal = Goal::Premise((node, PremIdx(0)), fa);

        // HS: `concat . lines . render $ prettyGoal g`.
        let rendered = render_goal_for_oracle(&goal);
        let collapsed: String = rendered.lines().collect::<Vec<_>>().concat();

        assert_eq!(
            collapsed,
            "!KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb) \u{25B6}\u{2080} #l",
            "oracle goal string must match HS `render` at default ribbon 67 \
             (wrapped fact: no space before `)`)",
        );

        // The SAME goal at the DISPLAY width (110 / 73) stays inline, keeping
        // the space before `)`.  This guards against silently swapping the
        // oracle width back to the display width.
        let display: String = solve_goal_to_doc(&goal)
            .render_at(crate::pretty_hpj::LINE_LENGTH, crate::pretty_hpj::RIBBON, 0)
            .lines()
            .collect::<Vec<_>>()
            .concat();
        assert_eq!(
            display,
            "!KeyStore0( ~keyaaaaaaaaaaaaaaaaaaaa, ~msgbbbbbbbbbbbbbbbbbbbb ) \u{25B6}\u{2080} #l",
            "display width must keep the fact inline (space before `)`)",
        );
        assert_ne!(collapsed, display, "oracle and display widths must differ here");
    }

    /// Regression: a disjunction goal sent to the oracle MUST carry the
    /// leading space HS produces.  HS `prettyGoal (DisjG (Disj gfs))` =
    /// `fsep (map (nest 1 . parens . prettyGuarded) gfs)` (Constraints.hs:
    /// 276-277), and HS `render` (HughesPJ `lay`, from column 0) APPLIES the
    /// top-level `nest 1` to the FIRST line — so the oracle stdin line is
    /// `" (#a < #b)  ∥ (#b < #a)"` (leading space).  `render_goal_for_oracle`
    /// must use `render_with`/`lay`, NOT `render_at`/`lay2` (which drops a
    /// leading `Nest`); the latter fed the oracle a string differing from HS
    /// by one space, perturbing oracle ranking decisions on oracle-driven
    /// proofs (e.g. csf19-wrapping gcm).  Ground truth captured from the
    /// v1.13.0 HS prover with an echoing oracle.
    #[test]
    fn disj_goal_for_oracle_has_leading_space() {
        use crate::constraint::constraints::{Disj, Goal};
        use crate::guarded::Guarded;
        use crate::guarded_types::{BVar, GAtom, GTerm};
        use tamarin_parser::ast::{SortHint, VarSpec};

        let tp = |n: &str| GTerm::Var(BVar::Free(VarSpec {
            name: n.to_string(),
            idx: 0,
            sort: SortHint::Node,
            typ: None,
        }));
        // `#a < #b` ∥ `#b < #a`
        let d1 = Guarded::Atom(GAtom::Less(tp("a"), tp("b")));
        let d2 = Guarded::Atom(GAtom::Less(tp("b"), tp("a")));
        let goal = Goal::Disj(Disj::new(vec![d1, d2]));

        let rendered = render_goal_for_oracle(&goal);
        let collapsed: String = rendered.lines().collect::<Vec<_>>().concat();
        // HS `nest 1` leading space + `"  ∥"` separator (two spaces + ∥).
        assert_eq!(
            collapsed,
            " (#a < #b)  \u{2225} (#b < #a)",
            "oracle disjunction goal must keep HS's leading `nest 1` space",
        );
        assert!(
            collapsed.starts_with(' '),
            "regression: oracle disj goal lost its leading space (render_at/lay2 bug)",
        );
    }
}
