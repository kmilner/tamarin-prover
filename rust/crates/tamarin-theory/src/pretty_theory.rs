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
            // Tactic ranking: collect up to '}'
            // HS InternalTacticRanking → '{' ++ name ++ '}'
            let start = i;
            i += 1;
            while i < chars.len() && chars[i] != '}' {
                i += 1;
            }
            if i < chars.len() {
                i += 1; // consume '}'
            }
            // Re-emit as-is (includes braces)
            let tok: String = chars[start..i].iter().collect();
            result.push(tok);
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
    let rendered: Vec<Option<String>> = parsed.items.par_iter()
        .map(|item| render_parsed_item(item, 0, parsed, elaborated, proved, in_file))
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
        let items: Vec<String> = builtins.iter().map(|s| s.to_string()).collect();
        out.push_str(&wrap_with_lead("builtins:", &items));
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
fn render_equations(sig: &tamarin_term::maude_sig::MaudeSig) -> Vec<(String, String)> {
    let mut items: Vec<(String, String)> = Vec::new();
    for r in &sig.st_rules {
        let lhs = render_lnterm(&r.lhs);
        let rhs = render_lnterm(&r.rhs.term);
        items.push((lhs, rhs));
    }
    // Sort by `lhs = rhs` string for stable HS-like ordering.
    items.sort_by(|a, b| {
        format!("{} = {}", a.0, a.1).cmp(&format!("{} = {}", b.0, b.1))
    });
    items
}

/// HS `ppNonEmptyList' name pp xs = (keyword_ name <->) . fsep $
/// punctuate comma (map pp xs)` (Term/Maude/Signature.hs:229-231).
/// `<->` is HughesPJ `<+>` (beside-with-space), and `fsep` is the
/// fill-paragraph combinator, so the wrap decisions must come from the
/// ported HughesPJ Doc engine (LINE_LENGTH=110, RIBBON=73) — not a
/// hand-rolled greedy fill at a guessed width.  Route through `pretty_hpj`.
fn wrap_with_lead(lead: &str, items: &[String]) -> String {
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
fn sep_block_with_lead(lead: &str, items: &[(String, String)]) -> String {
    use crate::pretty_hpj::{self as hpj, Doc};
    if items.is_empty() { return String::new(); }
    let n = items.len();
    let mut docs: Vec<Doc> = Vec::with_capacity(n + 1);
    docs.push(Doc::text(lead));
    for (i, (lhs, rhs)) in items.iter().enumerate() {
        // prettyCtxtStRule: sep [ nest 2 lhs, "=" <-> rhs ]
        let lhs_doc = Doc::text(lhs).nest(2);
        let eq_doc = Doc::text("=").beside_sp(Doc::text(rhs));
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

fn render_parsed_item(
    item: &p::TheoryItem,
    _idx: usize,
    parsed: &p::Theory,
    elab: &Theory,
    proved: &[ProvedLemma],
    in_file: &str,
) -> Option<String> {
    use p::TheoryItem::*;
    // Collect macros from the parsed theory so restriction/lemma renderers
    // can apply them to get the expanded formula (mirrors HS
    // `applyMacroInRestriction` + `parseLemmaWithMacros` which store the
    // expanded formula separately from the original).
    let macros: Vec<p::Macro> = parsed.items.iter()
        .filter_map(|i| if let p::TheoryItem::Macros(ms) = i { Some(ms.as_slice()) } else { None })
        .flatten()
        .cloned()
        .collect();
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
                Some(render_rule(r, elab, &macros))
            } else {
                None
            }
        }
        IntrRule(_) => None,
        Lemma(l) => Some(render_parsed_lemma(l, &macros, proved, in_file)),
        Restriction(r) => Some(render_parsed_restriction(r, &macros)),
        Predicates(_) => {
            // TODO: render predicates (port HS prettyPredicate).
            None
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
                .filter_map(|it| render_parsed_item(it, 0, parsed, elab, proved, in_file))
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
    elab.signature
        .maude_sig()
        .no_eq_fun_syms()
        .iter()
        .filter(|s| s.arity == 1)
        .map(|s| String::from_utf8_lossy(&s.name).to_string())
        .collect()
}

/// Re-fold surplus arguments of arity-1 function applications into a single
/// right-associative pair, mirroring HS `naryOpApp` for `k == 1`
/// (Theory/Text/Parser/Term.hs:84-87):
///   `ts <- parens $ if k == 1 then return <$> tupleterm ... else commaSep ...`
/// where `tupleterm = chainr1 (...) (fAppPair <$ comma)`.  So for an arity-1
/// symbol `f`, the surface `f(a, b, c)` parses to `f(<a, b, c>)` — a single
/// argument which is the right-associative pair `<a, b, c>`.  RS's term
/// parser is arity-unaware and keeps `App("f", [a, b, c])`, so the stored
/// rule-body AST carries surplus args.  Re-fold them before rendering so the
/// theory printout matches HS's `prettyTerm`, which prints the symbol's
/// actual argument list verbatim (`ppFun f ts`, Term/Term.hs:295-296 — it
/// does NOT itself flatten a tuple arg into a comma list).
fn rewrite_arity1_term(
    t: &p::Term,
    arity1: &std::collections::HashSet<String>,
) -> p::Term {
    use p::Term::*;
    match t {
        App(name, args) => {
            let new_args: Vec<p::Term> =
                args.iter().map(|a| rewrite_arity1_term(a, arity1)).collect();
            if arity1.contains(name) && new_args.len() > 1 {
                App(name.clone(), vec![Pair(new_args)])
            } else {
                App(name.clone(), new_args)
            }
        }
        Pair(items) => Pair(items.iter().map(|i| rewrite_arity1_term(i, arity1)).collect()),
        AlgApp(name, l, r) => AlgApp(
            name.clone(),
            Box::new(rewrite_arity1_term(l, arity1)),
            Box::new(rewrite_arity1_term(r, arity1)),
        ),
        Diff(l, r) => Diff(
            Box::new(rewrite_arity1_term(l, arity1)),
            Box::new(rewrite_arity1_term(r, arity1)),
        ),
        BinOp(op, l, r) => BinOp(
            *op,
            Box::new(rewrite_arity1_term(l, arity1)),
            Box::new(rewrite_arity1_term(r, arity1)),
        ),
        PatMatch(inner) => PatMatch(Box::new(rewrite_arity1_term(inner, arity1))),
        other => other.clone(),
    }
}

fn rewrite_arity1_fact(
    fa: &p::Fact,
    arity1: &std::collections::HashSet<String>,
) -> p::Fact {
    p::Fact {
        persistent: fa.persistent,
        name: fa.name.clone(),
        args: fa.args.iter().map(|a| rewrite_arity1_term(a, arity1)).collect(),
        annotations: fa.annotations.clone(),
    }
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

fn render_rule(parsed_rule: &p::Rule, elab: &Theory, macros: &[p::Macro]) -> String {
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
    // HS-faithful: an arity-1 function applied with a comma list, `f(a,b,c)`,
    // is folded by `naryOpApp`'s `k == 1` branch into `f(<a,b,c>)`
    // (Theory/Text/Parser/Term.hs:84-87).  RS's term parser keeps the surplus
    // args, so re-fold here before rendering.  See `rewrite_arity1_term`.
    let arity1 = arity1_noeq_names(elab);
    let premises: Vec<p::Fact> =
        desugared.premises.iter().map(|f| rewrite_arity1_fact(f, &arity1)).collect();
    let actions: Vec<p::Fact> =
        desugared.actions.iter().map(|f| rewrite_arity1_fact(f, &arity1)).collect();
    let conclusions: Vec<p::Fact> =
        desugared.conclusions.iter().map(|f| rewrite_arity1_fact(f, &arity1)).collect();
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
            let ac_body_matches = match &r.abstracted_rule {
                None => {
                    // Trivial unless macros fired on this rule's display body.
                    // Apply macros to the display facts; if unchanged, the
                    // rule has no macro calls → display == elaborated → trivial.
                    let macro_prems: Vec<p::Fact> = premises.iter()
                        .map(|f| crate::macro_expand::apply_macros_fact(macros, f))
                        .collect();
                    let macro_acts: Vec<p::Fact> = actions.iter()
                        .map(|f| crate::macro_expand::apply_macros_fact(macros, f))
                        .collect();
                    let macro_concs: Vec<p::Fact> = conclusions.iter()
                        .map(|f| crate::macro_expand::apply_macros_fact(macros, f))
                        .collect();
                    // Same iff no macro call in this rule's terms changed anything.
                    macro_prems == premises
                        && macro_acts == actions
                        && macro_concs == conclusions
                }
                Some(ac) => same_rule_body(&r.rule, ac),
            };
            no_residual_substs && ac_body_matches
        })
        .unwrap_or(true);

    // HS `prettyClosedProtoRule` (ClosedTheory.hs:337-339, 352-354) emits
    // `prettyLoopBreakers` at `nest 2` BEFORE the trailing
    // `multiComment_` (trivial) or `multiComment (prettyProtoRuleAC ...)`
    // (non-trivial) block.  We emit the same `  // loop breaker: [<n>]`
    // / `  // loop breakers: [<n>,<m>]` line here when non-empty.
    let outer_loop_breaker = elab_rule
        .map(|r| render_loop_breakers_line(&r.loop_breakers, 2))
        .unwrap_or_default();
    if trivial {
        out.push_str("\n\n");
        out.push_str(&outer_loop_breaker);
        out.push_str("  /* has exactly the trivial AC variant */");
    } else if let Some(r) = elab_rule {
        out.push_str("\n\n");
        out.push_str(&outer_loop_breaker);
        out.push_str(&render_ac_variants_block(name, r));
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
///
/// HS `prettyProtoRuleACInfo` (Rule.hs:1284-1290) emits the variants
/// sub-block via `ppVariants`, which returns `emptyDoc` when the
/// disjunction is exactly `[emptySubstVFresh]`.  So when RS's
/// `variant_substs` is empty (== HS's `[empty]`) or every subst is
/// itself empty, we emit only the rule body — no `variants (modulo AC)`
/// header — matching HS byte-for-byte for the AddPublicKey-style case
/// where the AC body differs from the E body but no residual variant
/// disjunction remains.
fn render_ac_variants_block(name: &str, rule: &crate::theory::OpenProtoRule) -> String {
    let mut s = String::new();
    s.push_str("  /*\n");
    s.push_str(&format!("  rule (modulo AC) {}:\n", name));
    // Body of the abstracted rule.  Use the abstracted version when
    // available; fall back to the original facts.
    // Use the abstracted rule's facts when available; when `abstracted_rule`
    // is `None` (no reducible-headed sub-terms), fall back to the ELABORATED
    // rule's facts (`rule.rule`).  This is the macro case: the elaborated
    // facts have macro calls expanded (e.g. `aenc(~k, pkS)` instead of
    // `encrypt(~k, pkS)`) — exactly what HS's `cprRuleAC` holds after
    // `variantsProtoRule (applyMacroInRule macros ruE)`.  Previously we
    // fell back to empty vecs, producing an empty AC body.
    let ac_rule = rule.abstracted_rule.as_ref().unwrap_or(&rule.rule);
    let prems = lnfacts_to_parser(&ac_rule.premises);
    let acts = lnfacts_to_parser(&ac_rule.actions);
    let concs = lnfacts_to_parser(&ac_rule.conclusions);
    // Each line of the rule body needs an extra leading 2-space indent
    // (we're inside the comment block, which already has 2 spaces).
    let body = render_rule_body(&prems, &acts, &concs);
    for line in body.split('\n') {
        s.push_str("  ");
        s.push_str(line);
        s.push('\n');
    }
    // HS `ppVariants (Disj [subst]) | subst == emptySubstVFresh = emptyDoc`
    // (Rule.hs:1289): skip the variants sub-block when there's no
    // residual disjunction beyond the identity.
    let has_residual_variants = rule.variant_substs.iter().any(|sub| !sub.is_empty());
    if has_residual_variants {
        s.push_str("    variants (modulo AC)\n");
        // HS `numbered'` (PrettyPrint/Class.hs:252-259) right-pads each
        // variant number to the width of the largest number so the dots
        // line up: e.g. with 21 variants, variant 1 is rendered as
        // ` 1.` (leading space) to align with `21.`.
        let total = rule.variant_substs.len();
        let n_width = total.to_string().len();
        for (i, subst) in rule.variant_substs.iter().enumerate() {
            if i > 0 { s.push_str("    \n"); }
            s.push_str(&render_variant_subst(i + 1, subst, n_width));
        }
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

/// Render one entry of `prettyDisjLNSubstsVFresh`
/// (SubstVFresh.hs:223-229): the variant's number, then each domain var
/// followed by `= <range>`.  HS aligns the `=` at column 6 from the
/// entry's local origin when the var name is short, otherwise wraps to
/// a new line.
///
/// `n_width` is the width of the largest variant number (HS's
/// `numbered`'s `nWidth = length (show n)` at PrettyPrint/Class.hs:258);
/// each variant's number is right-flushed in that width so dots line up.
fn render_variant_subst(
    n: usize,
    subst: &tamarin_term::subst_vfresh::LNSubstVFresh,
    n_width: usize,
) -> String {
    use crate::pretty_hpj::Doc;
    let mut s = String::new();
    let bindings = subst.to_list();
    // Continuation prefix's width depends on `n_width` so subsequent lines
    // line up under the first variable column.
    let label = format!("{:>width$}. ", n, width = n_width);
    let cont_indent = " ".repeat(label.chars().count());
    for (i, (v, t)) in bindings.iter().enumerate() {
        let var_str = render_lvar(v);
        let prefix = if i == 0 {
            format!("    {}", label)
        } else {
            format!("    {}", cont_indent)
        };
        // HS `prettyEq (a,b) = prettyNTerm (Var a) $$ nest 6 (text "="
        // <-> prettyNTerm b)` (SubstVFresh.hs:228-229).  `$$` overlaps the
        // (single-line) var onto the same line as the nest-6 `= <term>`,
        // giving `z     = term` with `=` at col 6; the term itself wraps
        // via `prettyTerm`'s fcat/fsep, with continuation aligned under the
        // first argument.  Build it as one Doc so the engine reproduces the
        // term wrap and continuation indent byte-identically.  `<->` is
        // `<+>` (beside-with-space).
        let term_doc = pf::term_to_doc(&lnterm_to_parser(t), &[]);
        let rhs = Doc::text("=").beside_sp(term_doc).nest(6);
        let entry = Doc::text(var_str).above(rhs);
        // Place the entry at its absolute column = prefix width.  Nest by
        // that amount, render, then strip the leading prefix-width spaces
        // from the first line (we emit `prefix` explicitly so the label /
        // continuation-indent is right).
        let col = prefix.chars().count();
        let rendered = entry.nest(col as isize).render();
        let strip = rendered.chars().take(col).take_while(|c| *c == ' ').count();
        s.push_str(&prefix);
        s.push_str(&rendered[strip..]);
        s.push('\n');
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

/// HS page width — the hard cap on total line length.  Mirrors
/// `lineWidth = 110` (Main/Console.hs:236).  HughesPJ uses
/// `min(line_start + ribbon, page_width)` as the inline-fit threshold,
/// so deeply-nested lines can never exceed `PAGE_WIDTH` regardless of
/// how generous the ribbon would be.
const PAGE_WIDTH: usize = 110;

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
    render_fact_brackets_at(facts, 3, 3)
}

/// `line_start`: column where the OUTPUT line on which this bracket
/// list begins started.  Equal to `indent` when the `[` is at the start
/// of a fresh line; less than `indent` when the bracket list is being
/// laid out mid-line (e.g. inside a `Fact( ... )` whose body fsep-packs
/// it).  Used for HS-faithful ribbon checks `cur_col - line_start <=
/// RIBBON`.
fn render_fact_brackets_at(facts: &[p::Fact], indent: usize, line_start: usize) -> String {
    if facts.is_empty() {
        return "[ ]".to_string();
    }
    // Try inline first.
    let inline = render_fact_brackets_inline(facts);
    let inline_max_col = std::cmp::min(line_start + RIBBON, PAGE_WIDTH);
    if !inline.contains('\n') && indent + inline.chars().count() < inline_max_col {
        return inline;
    }
    // HS `ppFactsList list = fsep [text "[", ppFacts' list, text "]"]`
    // (Rule.hs:1268). The three-doc fsep tries:
    //   (1) `[ body ]` inline  (checked above)
    //   (2) `[ body\n]`         — body inline after `[`, closer on
    //                             its own line
    //   (3) `[\n body \n]`      — full break around the body
    //
    // For (2)/(3) the body is itself `fsep . punctuate comma` so it
    // packs across lines comma-by-comma.
    let inline_body = facts.iter()
        .map(render_fact)
        .collect::<Vec<_>>()
        .join(", ");
    let opener_inline_body = format!("[ {}", inline_body);
    let opener_fits = !opener_inline_body.contains('\n')
        && indent + opener_inline_body.chars().count() <= inline_max_col;
    let pad = " ".repeat(indent);
    if opener_fits {
        // Layout (2): `[ body\n<pad>]`
        return format!("{}\n{}]", opener_inline_body, pad);
    }
    // Layout (3): each fact at column `indent`, packed greedily.
    let items: Vec<String> = facts.iter()
        .map(|f| render_fact_at(f, indent, indent))
        .collect();
    let body = fsep_pack(&items, indent, ", ", indent);
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
    render_fact_at(fa, 3, 3)
}

/// `line_start`: see `render_fact_brackets_at`.
fn render_fact_at(fa: &p::Fact, indent: usize, line_start: usize) -> String {
    render_fact_at_with_trailing(fa, indent, line_start, 0)
}

/// Like `render_fact_at` but the inline-fit check reserves
/// `trailing_chars` cols at the end of the line for caller-emitted
/// trailing text (e.g. ` ▶₁ #i )` after a Premise goal's fact).  This
/// mirrors HS's `fits` walking PAST the fact's nestShort' sep Union
/// into the OUTER doc's remaining text — HS sees the trailing chars
/// when deciding inline-vs-vertical at the fact's sep.
fn render_fact_at_with_trailing(fa: &p::Fact, indent: usize, line_start: usize, trailing_chars: usize) -> String {
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
    let inline_max_col = std::cmp::min(line_start + RIBBON, PAGE_WIDTH);
    if indent + inline.chars().count() + trailing_chars < inline_max_col && !inline.contains('\n') {
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
    // HS `nestShort'` (Class.hs:218-223): `sep [lead $$ nest n body, finish]`.
    // The `$$` puts `body`'s first line on the SAME line as `lead`
    // (overlap), so the first arg lands at `cont_indent` on the
    // current line — `line_start` propagates THROUGH from the fact's
    // line.  Continuation lines (if any arg wraps) land at col
    // `cont_indent` on fresh lines (their line_start = cont_indent).
    //
    // We pre-render each arg at the FACT'S `line_start` (matches the
    // overlap-line budget for arg 1).  When fsep_pack later forces a
    // break, the broken arg's continuation lines will be slightly
    // more wrapped than HS would do at `line_start = cont_indent` —
    // but never less.  HS-faithful in the common case (single-arg
    // facts like `!KU( aead(...) )`).
    let item_strs: Vec<String> = fa.args.iter()
        .map(|t| render_term_at(t, cont_indent, line_start))
        .collect();
    let body = fsep_pack(&item_strs, cont_indent, ", ", line_start);
    let pad = " ".repeat(indent);
    format!("{} {}\n{})", head, body, pad)
}

/// Render a parser-AST term with wrap-awareness.  The output's first
/// char will land at column `indent`; continuation lines (when the
/// term wraps internally) start at column `indent` too.
///
/// `line_start`: column where the OUTPUT line on which this term begins
/// started.  Equal to `indent` when the term is at the start of a fresh
/// line; less than `indent` when it's mid-line.  Used for HS-faithful
/// ribbon check `indent + inline_len - line_start <= RIBBON`, mirroring
/// HughesPJ's `lineLength - ribbonsPerLine` semantics.
fn render_term_at(t: &p::Term, indent: usize, line_start: usize) -> String {
    // Try inline first — HS-faithful ribbon + pageWidth check.
    // HughesPJ's effective inline budget is
    // `min(line_start + RIBBON, PAGE_WIDTH)`.
    let inline = pf::pretty_term(t);
    let max_col = std::cmp::min(line_start + RIBBON, PAGE_WIDTH);
    if indent + inline.chars().count() <= max_col && !inline.contains('\n') {
        return inline;
    }
    // Decompose at the top-level constructor.
    match t {
        p::Term::Pair(items) => render_pair_at(items, indent, line_start),
        p::Term::App(name, args) if !args.is_empty() => {
            render_app_at(name, args, indent, line_start)
        }
        p::Term::AlgApp(name, l, r) => {
            // HS-faithful: `aenc{m}pk` surface form, but prettyTerm emits
            // it as `Name(m, pk)` — match `pretty_term`.
            render_app_at(name, &[(**l).clone(), (**r).clone()], indent, line_start)
        }
        p::Term::Diff(l, r) => {
            render_app_at("diff", &[(**l).clone(), (**r).clone()], indent, line_start)
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
///
/// `line_start`: column where the OUTPUT line on which this pair's `<`
/// lands started.  Equal to `indent` when `<` is at start of a fresh
/// line; less when mid-line.  See `render_term_at`.
fn render_pair_at(items: &[p::Term], indent: usize, line_start: usize) -> String {
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
    let inline_max_col = std::cmp::min(line_start + RIBBON, PAGE_WIDTH);
    if indent + inline.chars().count() < inline_max_col && !inline.contains('\n') {
        return inline;
    }
    let cont_indent = indent + 1;
    // Pre-render at `line_start = cont_indent` (the laxest budget,
    // matching the eventual fresh-wrap-line case).  See `render_app_at`.
    let item_strs: Vec<String> = items.iter()
        .map(|t| render_term_at(t, cont_indent, cont_indent))
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
    // would force the line past `line_start + RIBBON`, so HS breaks at `<`
    // and starts the item on its own fresh line at cont_indent (where
    // its continuation lines align).
    let first_is_too_wide = item_strs.first().map(|s| {
        let first_line_len = match s.find('\n') {
            Some(j) => s[..j].chars().count(),
            None => s.chars().count(),
        };
        let max_col = std::cmp::min(line_start + RIBBON, PAGE_WIDTH);
        cont_indent + first_line_len > max_col
    }).unwrap_or(false);
    let first_is_multiline = item_strs.first().map(|s| s.contains('\n')).unwrap_or(false)
        || first_is_too_wide;
    let last_is_multiline = item_strs.last().map(|s| s.contains('\n')).unwrap_or(false);
    // For the inner-pair body fsep, line_start is the column where
    // the outer `<` was opened — that's the OUTER `line_start` (the
    // render_pair_at caller's line_start), since `<` is on that
    // same line.  When `first_is_multiline`, we emit `<\n...` so the
    // body's first item is on a fresh line at col `cont_indent`; in
    // that case we pass `cont_indent` as line_start to fsep_pack.
    let body_line_start = if first_is_multiline { cont_indent } else { line_start };
    let body = fsep_pack_pair(&item_strs, cont_indent, body_line_start);
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
    //
    // `close_fits` uses absolute-col ribbon check: compute the col
    // where `>` would land, compare against the ribbon for the line it
    // would sit on.
    let body_is_multi = body.contains('\n');
    let body_last_line_len = match body.rfind('\n') {
        Some(j) => body[j + 1..].chars().count(),
        None => body.chars().count(),
    };
    // Col where `>` would land if attached after body's last char.
    // For single-line body: `<` at indent, body at indent+1..indent+body_len,
    // `>` at indent+1+body_len.
    // For multi-line body: body's last line starts at col 0 (after `\n`),
    // already padded by fsep_pack to `cont_indent` leading spaces;
    // `>` lands at col body_last_line_len.
    let (gt_col, gt_line_start) = if body_is_multi {
        (body_last_line_len, cont_indent)
    } else {
        let pair_starts_fresh = first_is_multiline;
        let body_line_start = if pair_starts_fresh { cont_indent } else { line_start };
        (indent + 1 + body_last_line_len, body_line_start)
    };
    let close_max = std::cmp::min(gt_line_start + RIBBON, PAGE_WIDTH);
    let close_fits = !last_is_multiline && gt_col + 1 <= close_max;
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
///
/// `line_start`: see `render_term_at`.
fn render_app_at(name: &str, args: &[p::Term], indent: usize, line_start: usize) -> String {
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
    let inline_max_col = std::cmp::min(line_start + RIBBON, PAGE_WIDTH);
    if indent + inline.chars().count() < inline_max_col && !inline.contains('\n') {
        return inline;
    }
    // HS `ppFun` uses `text (f ++ "(") <> fsep (...)  <> text ")"` (no
    // `nestShort'`).  The `fsep` starts right after `Name(` and lays
    // out items.  When wrapping, items continue at col-of-`(` + 1.
    // Close `)` attaches to last line (since the `<>` glues it on).
    let cont_indent = indent + head.chars().count();
    // Items land on the SAME line as `Name(` (which started at the
    // outer `line_start`).  Pre-render against that OUTER line_start
    // so internal inline-fit decisions match the first-line ribbon
    // budget.  fsep_pack then handles per-item break decisions for
    // subsequent items — when an item breaks to a fresh line at col
    // `cont_indent`, its already-rendered form may be slightly more
    // wrapped than necessary, but never less.  HS-faithful in the
    // common case (single-arg apps like `h(pair)` where the only arg
    // stays on the first line).
    let item_strs: Vec<String> = args.iter()
        .map(|t| render_term_at(t, cont_indent, line_start))
        .collect();
    // line_start passes THROUGH: the `Name(` lands at `indent` on a
    // line that started at `line_start`, so fsep_pack's first-line
    // ribbon-fit check is against `line_start + RIBBON`.
    let body = fsep_pack(&item_strs, cont_indent, ", ", line_start);
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
        // HS-faithful ribbon + pageWidth constraint: line content past
        // `cur_line_start` cannot exceed RIBBON, AND total col cannot
        // exceed PAGE_WIDTH.  HughesPJ uses
        // `min(line_start + ribbon, page_width)` as the inline-fit
        // threshold (Text.PrettyPrint.HughesPJ source).
        let max_col = std::cmp::min(cur_line_start + RIBBON, PAGE_WIDTH);
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
            //
            // Note: HS's `fsep`/`fill` (HughesPJ.hs:780-805) uses
            // `fillNBE`/`fits` to decide at each item-boundary whether
            // to inline.  `fits` walks the flat alt's RESOLVED doc tree
            // and returns True as soon as it hits a `NilAbove` or
            // `Empty`.  In practice this means "first line of flat
            // alt fits".  When a later item internally breaks (its
            // `nestShort'` Union picks multi-line), `fits` short-circuits
            // True at that internal NilAbove — so the OUTER item's
            // boundary Union can still pick "inline", even when the
            // total flat doesn't fit.  Greedy `col + sep + first_line`
            // check approximates this within RS's non-Doc-tree packer.
            // HS-faithful lookahead: when the NEXT item is multi-line
            // (forcing a break AFTER us), the `break_sep` (typically ",")
            // is appended at the END of our line before the newline.  HS's
            // `fits` walks past the boundary into the next fillNBE Union
            // and sees the trailing `,` from `punctuate`'s `arg_i <> ","`.
            // We reserve 1 extra col for that trailing break_sep so the
            // inline-fit decision accounts for it (matching HS's `fits`
            // walking arg_(i-1)<>"," + " " + arg_i<>"," up to the next
            // NilAbove from the multi-line break).
            let break_sep_reserve = if i + 1 < items.len() && items[i + 1].contains('\n') {
                // break_sep is sep with trailing space trimmed (when
                // trim_break_space=true) → 1 char less than sep_chars.
                // Concretely sep ", " → break_sep "," → 1 char.
                if trim_break_space { sep_chars - 1 } else { 0 }
            } else {
                0
            };
            let inline_fits = !force_break
                && col + sep_chars + first_line_len + break_sep_reserve <= max_col
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

fn render_parsed_lemma(lem: &p::Lemma, macros: &[p::Macro], proved: &[ProvedLemma], in_file: &str) -> String {
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
    // HS sorts AC arguments at parse time when building `LNTerm` via `fAppAC`
    // (Term/Term/Raw.hs:118-122); our parser keeps `BinOp` trees in written
    // order, so re-establish the canonical AC operand order on the formula
    // before rendering the header (matches the guarded-block path which
    // already canonicalises via guarded.rs:684).
    let canon_formula = crate::elaborate::canonicalize_ac_in_formula(&lem.formula);
    out.push_str(&pf::lemma_header_line(quant, &canon_formula));
    out.push('\n');

    // /* guarded formula characterizing ... */
    out.push_str(&render_guarded_block(lem, macros));

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

// Legacy string-join form (kept for any direct callers).
#[allow(dead_code)]
fn render_lemma_attrs(attrs: &[p::LemmaAttr], in_file: &str) -> String {
    lemma_attr_docs(attrs, in_file).iter()
        .map(|d| d.clone().render())
        .collect::<Vec<_>>()
        .join(", ")
}

fn quantifier_keyword(q: &p::TraceQuantifier) -> &'static str {
    match q {
        p::TraceQuantifier::AllTraces => "all-traces",
        p::TraceQuantifier::ExistsTrace => "exists-trace",
    }
}

fn render_guarded_block(lem: &p::Lemma, macros: &[p::Macro]) -> String {
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
                .map(|f| crate::pretty_formula::pretty_formula(f))
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

fn render_parsed_restriction(r: &p::Restriction, macros: &[p::Macro]) -> String {
    // HS `prettyRestriction` (TheoryObject.hs:846-857):
    //   The `Restriction` carries two formulas after `applyMacroInRestriction`:
    //   - `_rstrFormula`         = macro-EXPANDED formula  (displayed in expanded block)
    //   - `_rstrOriginalFormula` = original macro-form     (displayed on top)
    //   HS always has `ogFormula = Just _` (applyMacroInRestriction sets it
    //   even when there are no macros: `Just $ maybe f id ofm`).
    //
    // RS's `r.formula` is the parser-form (macro calls present).  Apply
    // the theory's macros to get the expanded formula used in the block.
    let expanded = if macros.is_empty() {
        r.formula.clone()
    } else {
        crate::macro_expand::apply_macros_formula(macros, &r.formula)
    };
    let mut out = String::new();
    out.push_str("restriction ");
    out.push_str(&r.name);
    out.push_str(":\n");
    // Top-level display: original formula (macro form) — `fromMaybe expandedFormula ogFormula`.
    // Since ogFormula = Just original, this always shows `r.formula` (macro form).
    out.push_str(&pf::formula_doublequoted_nested(&r.formula, 2));
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
    let unann = if node.annotated { "" } else { " /* unannotated */" };
    let step = pp_step_at(&node.method, depth * 2);
    let cases: Vec<(&String, &crate::constraint::solver::search::ProofNode)> =
        node.children.iter().collect();

    match (&node.method, cases.as_slice()) {
        (ProofMethod::Finished(MR::Solved), []) => {
            out.push_str(&step);
            out.push_str(unann);
        }
        (_, []) => {
            // No children: `by <step>` form.  HS `ppCases ps [] =
            // prettyCase ps (kwBy <> text " ") <> prettyStep ps` (Proof.hs:
            // 1085-1086) — `<>` is beside, so the `prettyStep` Doc is laid
            // out BESIDE `by ` and HughesPJ's beside column-shift indents
            // the step's wrapped continuation lines by the width of `by `
            // (3 chars).  Render the step at col `depth*2 + 3` so wrapped
            // `solve(...)` continuation lines align under the post-`by `
            // column, not the bare proof-tree indent.
            out.push_str("by ");
            let step = pp_step_at(&node.method, depth * 2 + 3);
            out.push_str(&step);
            out.push_str(unann);
        }
        (_, [(label, child)]) if label.is_empty() => {
            out.push_str(&step);
            out.push_str(unann);
            out.push('\n');
            // HS `ppCases ps [("", prf)] = prettyStep ps $-$ ppPrf prf`
            // (Proof.hs:1086).  `$-$` is "above" — the child is rendered
            // at the SAME indent column as the parent step.  In our output
            // model the caller writes the indent before calling pp_proof, so
            // we reproduce that here: write the same `depth`-level indent
            // before recursing into the child.
            out.push_str(&"  ".repeat(depth));
            pp_proof(child, out, depth);
        }
        (_, multi) => {
            out.push_str(&step);
            out.push_str(unann);
            for (i, (name, child)) in multi.iter().enumerate() {
                if i > 0 {
                    // HS Proof.hs:1089: `intersperse (prettyCase ps kwNext)`
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
            use crate::constraint::constraints::Goal;
            // HS `prettyProofMethod` (ProofMethod.hs:1494):
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

/// Render a `Goal` for `solve(...)` output.  Mirrors HS `prettyGoal`
/// (Constraints.hs:267-282).
/// Also used as oracle stdin goal text (ProofMethod.hs:828).
pub(crate) fn render_goal_for_oracle(g: &crate::constraint::constraints::Goal) -> String {
    render_goal_at(g, 0, 0)
}

#[allow(dead_code)]
fn render_goal(g: &crate::constraint::constraints::Goal) -> String {
    render_goal_at(g, 0, 0)
}

/// Wrap-aware goal renderer.  `indent` is the column where the goal's
/// first character will land — used so internal facts/terms can decide
/// to wrap when their inline form overflows the ribbon.  `line_start`
/// is the column where the OUTPUT line that contains the goal started;
/// it's used as the ribbon base for HS-faithful inline-fit decisions
/// when the goal is placed mid-line (e.g. inside `solve( <goal> )`
/// where the goal lands at col `line_start + 7`).
/// `trailing_chars`: chars the CALLER will append after this goal on
/// the same line (e.g. ` )` for `solve(...)`).  Threaded into the
/// fact's nestShort' inline-fit check so HS-faithful break decisions
/// account for what comes after.
fn render_goal_at(g: &crate::constraint::constraints::Goal, indent: usize, line_start: usize) -> String {
    render_goal_at_trailing(g, indent, line_start, 0)
}

fn render_goal_at_trailing(g: &crate::constraint::constraints::Goal, indent: usize, line_start: usize, trailing_chars: usize) -> String {
    use crate::constraint::constraints::Goal;
    use crate::rule::PremIdx;
    match g {
        // `prettyGoal (ActionG i fa) = prettyNAtom (Action (varTerm i) fa)`
        // which expands (Atom.hs:214-215) to `prettyFact ppT fa <-> opAction <-> text (show v)`.
        // `<->` is hsep-with-space → `<fact> @ <node-id>`.
        // Trailing for the fact = ` @ <node-id>` + caller's trailing.
        Goal::Action(i, fa) => {
            let nid = render_node_id(i);
            let fact_trailing = 1 + 1 + 1 + nid.chars().count() + trailing_chars;
            format!("{} @ {}", render_lnfact_at_with_trailing(fa, indent, line_start, fact_trailing), nid)
        }
        // `prettyGoal (ChainG c p) = prettyNodeConc c <-> operator_ "~~>" <-> prettyNodePrem p`
        Goal::Chain(c, p) =>
            format!("{} ~~> {}", render_node_conc(c), render_node_prem(p)),
        // `prettyGoal (PremiseG (i, PremIdx v) fa) =
        //    prettyLNFact fa <-> text ("▶" ++ subscript (show v)) <-> prettyNodeId i`
        // Trailing for the fact = ` ▶<subscript> <nid>` + caller's trailing.
        Goal::Premise((i, PremIdx(v)), fa) => {
            let sub = goal_subscript(*v);
            let nid = render_node_id(i);
            let fact_trailing = 1 + 1 + sub.chars().count() + 1 + nid.chars().count() + trailing_chars;
            format!("{} \u{25B6}{} {}",
                render_lnfact_at_with_trailing(fa, indent, line_start, fact_trailing), sub, nid)
        }
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
    render_lnfact_at(fa, 0, 0)
}

/// Wrap-aware variant.  When the inline form exceeds the ribbon from
/// `indent`, lays out the args with HS-faithful `nestShort'` semantics
/// (see `render_fact_at` for the parser-AST equivalent).
fn render_lnfact_at(fa: &crate::fact::LNFact, indent: usize, line_start: usize) -> String {
    render_lnfact_at_with_trailing(fa, indent, line_start, 0)
}

fn render_lnfact_at_with_trailing(fa: &crate::fact::LNFact, indent: usize, line_start: usize, trailing_chars: usize) -> String {
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
    let pfa = lnfact_to_parser(fa);
    render_fact_at_with_trailing(&pfa, indent, line_start, trailing_chars)
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
