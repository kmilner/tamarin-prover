//! Elaboration: parser AST → typed `Theory`.
//!
//! This pass takes a `tamarin_parser::ast::Theory` (the surface syntax
//! tree) and produces a `crate::theory::Theory` (typed). The full
//! Haskell `processOpenTheory` does many things — macro expansion,
//! sort inference, predicate expansion, `_restrict` lifting, derivation
//! checks. This first cut handles:
//!
//! - Theory header (`name`, `in_file`, `is_diff`)
//! - `builtins:` → `MaudeSig` (we record the names; full sig
//!   composition is handled by `signature::SignaturePure::empty`)
//! - `functions:` → `st_fun_syms` extension
//! - `equations:` → recorded as `CtxtStRule`s when convertible
//! - Rules — `parser::Rule` → `OpenProtoRule(ProtoRuleE, [])`
//! - Lemmas — passthrough; the formula is kept as parser AST until
//!   we port `formulaToGuarded`
//! - Restrictions — passthrough as `OpenRestriction`
//! - Predicates, macros, formal comments — copied verbatim
//!
//! Returned errors describe the surface offence (e.g. "duplicate rule
//! `R`"), with no internal panics.

use std::collections::BTreeSet;
use std::cell::RefCell;

use tamarin_parser::ast as p;
use tamarin_term::function_symbols::{
    Constructability, NoEqSym, Privacy,
};
use tamarin_term::lterm::LVar;
use tamarin_term::lterm::LSort;

thread_local! {
    /// User-declared arity-1 function names for the theory currently
    /// being elaborated.  Set by `elaborate()` from the theory's
    /// `functions:` declarations, read by `term_to_lnterm`'s arity-1
    /// auto-tuple branch.  In Tamarin's surface syntax, `f(a, b, c)`
    /// for a function declared `f/1` is sugar for `f(<a, b, c>)`; our
    /// hard-coded list previously only covered built-in arity-1 names
    /// (h, fst, snd, inv, pk).  Without this, `PRF(pms, nc, ns)` for
    /// `functions: PRF/1` would reach Maude as a 3-arg call, which
    /// Maude silently rejects, and our `reduce` loop spins forever.
    static USER_UNARY_FUNS: RefCell<BTreeSet<String>>
        = RefCell::new(BTreeSet::new());

    /// Names of nullary (0-arity) function symbols available in the
    /// theory currently being elaborated.  Set by `elaborate()` from
    /// both user `functions: f/0` declarations and the builtins that
    /// introduce 0-arity constants (`signing`/`dest-signing`/
    /// `revealing-signing` add `true`; `xor` adds `zero`; etc.).
    /// Read by `term_to_lnterm`'s `Var` branch so a bare `true` (which
    /// the lexer-level surface parser renders as `Var("true",Untagged)`
    /// for lack of a signature lookup) is converted into a 0-arity
    /// `f_app_no_eq` constant instead of a free variable.  Without
    /// this, `Eq(verify(...), true)` in a rule's actions becomes an
    /// `Eq` over `verify(...)` and a Msg-sort variable, which the
    /// `Eq_check_succeed` restriction trivially satisfies via the
    /// eq-store — undermining the signing builtin's semantics and
    /// causing TLS_Handshake-class lemmas to be wrong-falsified.
    static USER_NULLARY_FUNS: RefCell<BTreeSet<String>>
        = RefCell::new(BTreeSet::new());

    /// Names of user-declared function symbols marked `private`.
    /// Populated from `FunctionDecl.private` across all arities.  Read
    /// by `term_to_lnterm` when synthesizing `NoEqSym` for user-defined
    /// function applications so `Privacy::Private` propagates through
    /// to Maude.  Without this, `KU(f)` for a private nullary `f` is
    /// filtered by `is_nullary_public_function` (because we say
    /// Public), causing `is_finished` to incorrectly report Solved.
    static USER_PRIVATE_FUNS: RefCell<BTreeSet<String>>
        = RefCell::new(BTreeSet::new());
}
use tamarin_term::term::{f_app_no_eq, Term};
use tamarin_term::lterm::{Name, NameTag};
use tamarin_term::vterm::Lit;
use tamarin_term::maude_sig::{
    asym_enc_dest_maude_sig, asym_enc_maude_sig, bp_maude_sig, dh_maude_sig,
    enable_diff_maude_sig, hash_maude_sig, location_report_maude_sig,
    mset_maude_sig, nat_maude_sig, pair_maude_sig,
    reveal_signature_maude_sig, signature_dest_maude_sig, signature_maude_sig,
    sym_enc_dest_maude_sig, sym_enc_maude_sig, xor_maude_sig, MaudeSig,
};

use crate::rule::{
    ConcIdx, PremIdx, ProtoRuleE, ProtoRuleEInfo, ProtoRuleName,
    Rule, RuleAttributes,
};
use crate::signature::SignaturePure;
use crate::guarded::formula_to_guarded;
use crate::theory::{
    AccLemma, CaseTest, LNMacro, Lemma, LemmaAttr, OpenProtoRule,
    OpenRestriction, ProofSkeleton, Theory, TheoryItem,
    TraceQuantifier, TranslationElement,
};

#[derive(Debug, Clone)]
pub struct ElabError {
    pub message: String,
}

impl std::fmt::Display for ElabError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "elaboration error: {}", self.message)
    }
}
impl std::error::Error for ElabError {}

/// One diagnostic from `elaborate_with_diagnostics`, mirroring a
/// wellformedness "Formula guardedness" warning.
#[derive(Debug, Clone)]
pub struct GuardDiagnostic {
    pub topic: String,
    pub item: String,
    pub message: String,
}

/// Run elaboration and additionally check that every lemma /
/// restriction formula converts to a guarded formula. Returns the
/// elaborated theory along with any guardedness diagnostics. Mirrors
/// Haskell's `formulaReports.checkGuarded`.
pub fn elaborate_with_diagnostics(
    parser_thy: &p::Theory,
) -> Result<(Theory, Vec<GuardDiagnostic>), ElabError> {
    let thy = elaborate(parser_thy)?;
    let mut diags = Vec::new();
    for l in thy.lemmas() {
        if let Err(e) = formula_to_guarded(&l.formula) {
            diags.push(GuardDiagnostic {
                topic: "Formula guardedness".into(),
                item: format!("Lemma `{}'", l.name),
                message: format!("cannot be converted to a guarded formula: {}", e.message),
            });
        }
    }
    for r in thy.restrictions() {
        if let Err(e) = formula_to_guarded(&r.formula) {
            diags.push(GuardDiagnostic {
                topic: "Formula guardedness".into(),
                item: format!("Restriction `{}'", r.name),
                message: format!("cannot be converted to a guarded formula: {}", e.message),
            });
        }
    }
    Ok((thy, diags))
}

/// Elaborate a parser theory into a typed `Theory`. The signature
/// is initialised from the union of `builtins:` declarations. Before
/// the structural conversion runs, predicate atoms are expanded
/// in-place against any `predicates:` declarations.
pub fn elaborate(parser_thy: &p::Theory) -> Result<Theory, ElabError> {
    let mut thy_clone = parser_thy.clone();
    // Apply macros at parser-AST level BEFORE predicate expansion.
    // Mirrors HS's parse-time application: lemmas are expanded by
    // `parseLemmaWithMacros` (Theory/Text/Parser.hs:97-105); rules by
    // `closeProtoRule` (lib/theory/src/Rule.hs:96-98) before
    // variantsProtoRule runs; restrictions by `applyMacroInRestriction`
    // (Theory/Model/Restriction.hs:163-165).  We apply at the parser-AST
    // level so a single pass handles every term-bearing item before any
    // typed conversion (`term_to_lnterm` / `formula_to_guarded`) sees a
    // macro call.  Predicate-expand may itself substitute the inlined
    // predicate body into use sites, and the body could contain macro
    // calls — so expand macros first.
    crate::macro_expand::expand_theory_macros(&mut thy_clone);
    if let Err(e) = crate::predicate_expand::expand_theory_formulas(&mut thy_clone) {
        return Err(ElabError {
            message: format!("predicate expansion failed: {}", e.message),
        });
    }
    // Collect user-declared arity-1 function names so `term_to_lnterm`'s
    // auto-tuple branch fires for them as well as the built-in unary
    // names (h, fst, snd, ...).  Scoped via a guard so concurrent
    // elaborations on the same thread can't see stale state if one
    // panics — see `UserUnaryFunsGuard`.
    let unary_funs: BTreeSet<String> = thy_clone.items.iter().flat_map(|it| {
        if let p::TheoryItem::Functions(decls) = it {
            decls.iter().filter(|d| d.arg_types.len() == 1)
                .map(|d| d.name.clone()).collect::<Vec<_>>()
        } else { Vec::new() }
    }).collect();
    let _guard = UserUnaryFunsGuard::set(unary_funs);
    // Collect 0-arity function names introduced by user `functions:` and
    // by any enabled builtin (mirroring Haskell's parser-state-driven
    // `nullaryApp` lookup).
    let mut nullary_funs: BTreeSet<String> = thy_clone.items.iter().flat_map(|it| {
        if let p::TheoryItem::Functions(decls) = it {
            decls.iter().filter(|d| d.arg_types.is_empty())
                .map(|d| d.name.clone()).collect::<Vec<_>>()
        } else { Vec::new() }
    }).collect();
    for it in &thy_clone.items {
        if let p::TheoryItem::Builtins(names) = it {
            for n in names {
                for c in builtin_nullary_constants(n) {
                    nullary_funs.insert(c.to_string());
                }
            }
        }
    }
    let _nullary_guard = UserNullaryFunsGuard::set(nullary_funs);
    // Collect names of user-declared private function symbols (any
    // arity).  Used by term_to_lnterm to thread Privacy::Private through
    // synthesized NoEqSyms — without this, `KU(f)` for private nullary
    // `f` is incorrectly filtered as a known public function.
    let private_funs: BTreeSet<String> = thy_clone.items.iter().flat_map(|it| {
        if let p::TheoryItem::Functions(decls) = it {
            decls.iter().filter(|d| d.private).map(|d| d.name.clone()).collect::<Vec<_>>()
        } else { Vec::new() }
    }).collect();
    let _private_guard = UserPrivateFunsGuard::set(private_funs);
    elaborate_already_expanded(&thy_clone)
}

/// Extracts the 0-arity NoEq function-symbol names from a `MaudeSig`.
/// Mirrors HS `nullaryApp` (Theory/Text/Parser/Term.hs:139-143):
///
/// ```haskell
/// nullaryApp = do
///   maudeSig <- sig <$> getState
///   asum [ try (symbol (BC.unpack sym)) $> fApp fs []
///        | fs@(NoEq (sym,(0,_,_))) <- S.toList $ funSyms maudeSig ]
/// ```
///
/// HS's parser consults `funSyms maudeSig` when disambiguating a bare
/// identifier from a free variable.  Our parser is too lexer-driven to
/// thread the MaudeSig through the parser-state, so we populate the
/// `USER_NULLARY_FUNS` thread-local with the same names instead.  By
/// asking the MaudeSig directly here (rather than maintaining a parallel
/// hand-curated table) we guarantee the set we recognise matches HS's
/// `funSyms`, e.g. `oneSymString = "one"` and
/// `dhNeutralSymString = "DH_neutral"` for `dhFunSig`
/// (lib/term/src/Term/Term/FunctionSymbols.hs:134,137,153,163,192).
fn builtin_nullary_names_from_msig(msig: &MaudeSig) -> Vec<String> {
    msig.fun_syms.iter().filter_map(|fs| match fs {
        tamarin_term::function_symbols::FunSym::NoEq(s) if s.arity == 0 =>
            String::from_utf8(s.name.clone()).ok(),
        _ => None,
    }).collect()
}

/// Returns the 0-arity function symbol names introduced by a given
/// `builtins:` declaration name.  Resolves the name to its MaudeSig via
/// `builtin_sig` and then extracts the 0-arity NoEq names via
/// [`builtin_nullary_names_from_msig`].  This mirrors HS exactly: a
/// `builtins: foo` declaration triggers `enableBuiltin foo` which
/// installs the corresponding `*FunSig` into the parser-state MaudeSig,
/// and `nullaryApp` then consults that signature.
///
/// Returns an empty vector for unknown builtin names (HS would never
/// reach this point: `enableBuiltin` is exhaustive over the parsed
/// keywords; unknowns fail at the parser).
pub fn builtin_nullary_constants(name: &str) -> Vec<String> {
    match builtin_sig(name) {
        Some(msig) => builtin_nullary_names_from_msig(&msig),
        None => Vec::new(),
    }
}

/// RAII guard that swaps in a fresh `USER_UNARY_FUNS` set for the
/// duration of an `elaborate()` call and restores the previous value
/// on drop.  Ensures nested or sequential elaborations don't bleed
/// each other's arity-1 function sets.
struct UserUnaryFunsGuard {
    previous: BTreeSet<String>,
}

impl UserUnaryFunsGuard {
    fn set(new: BTreeSet<String>) -> Self {
        let previous = USER_UNARY_FUNS.with(|c| {
            let mut b = c.borrow_mut();
            let prev = std::mem::replace(&mut *b, new);
            prev
        });
        UserUnaryFunsGuard { previous }
    }
}

impl Drop for UserUnaryFunsGuard {
    fn drop(&mut self) {
        USER_UNARY_FUNS.with(|c| {
            *c.borrow_mut() = std::mem::take(&mut self.previous);
        });
    }
}

/// True if `name` is registered as a user-declared arity-1 function for
/// the current elaboration.  Read from the `USER_UNARY_FUNS` thread-local.
fn is_user_unary_fun(name: &str) -> bool {
    USER_UNARY_FUNS.with(|c| c.borrow().contains(name))
}

/// Same as `UserUnaryFunsGuard` but for the `USER_NULLARY_FUNS` set.
struct UserNullaryFunsGuard {
    previous: BTreeSet<String>,
}

impl UserNullaryFunsGuard {
    fn set(new: BTreeSet<String>) -> Self {
        let previous = USER_NULLARY_FUNS.with(|c| {
            let mut b = c.borrow_mut();
            std::mem::replace(&mut *b, new)
        });
        UserNullaryFunsGuard { previous }
    }
}

impl Drop for UserNullaryFunsGuard {
    fn drop(&mut self) {
        USER_NULLARY_FUNS.with(|c| {
            *c.borrow_mut() = std::mem::take(&mut self.previous);
        });
    }
}

/// True if `name` is registered as a 0-arity function for the current
/// elaboration.  See `USER_NULLARY_FUNS` for the populating logic.
fn is_user_nullary_fun(name: &str) -> bool {
    USER_NULLARY_FUNS.with(|c| c.borrow().contains(name))
}

/// RAII guard for the USER_PRIVATE_FUNS thread-local.
struct UserPrivateFunsGuard {
    previous: BTreeSet<String>,
}

impl UserPrivateFunsGuard {
    fn set(new: BTreeSet<String>) -> Self {
        let previous = USER_PRIVATE_FUNS.with(|c| {
            let mut b = c.borrow_mut();
            std::mem::replace(&mut *b, new)
        });
        UserPrivateFunsGuard { previous }
    }
}

impl Drop for UserPrivateFunsGuard {
    fn drop(&mut self) {
        USER_PRIVATE_FUNS.with(|c| {
            *c.borrow_mut() = std::mem::take(&mut self.previous);
        });
    }
}

/// Returns `Privacy::Private` if `name` is a user-declared private
/// function symbol; otherwise `Privacy::Public`.  Mirrors Haskell's
/// `signature` lookup against the per-theory funSig.
fn user_fun_privacy(name: &str) -> Privacy {
    USER_PRIVATE_FUNS.with(|c| {
        if c.borrow().contains(name) { Privacy::Private } else { Privacy::Public }
    })
}

/// Bundles RAII guards for all the user-declared function thread-locals,
/// scoped to the lifetime of an outer call (typically `prove_lemma`).
pub struct UserFunsForTheoryGuard {
    _unary: UserUnaryFunsGuard,
    _nullary: UserNullaryFunsGuard,
    _private: UserPrivateFunsGuard,
}

/// RAII guard that swaps in the 0-arity NoEq function-symbol names from
/// a `MaudeSig` for the duration of a parse, then restores the previous
/// `USER_NULLARY_FUNS` on drop.  Use this around any call that builds
/// LNTerms via [`term_to_lnterm`] from a string the user/HS wrote
/// against a specific MaudeSig (e.g. the cached intruder-variant files
/// in `data/`).
///
/// HS analogue: the parser-state MaudeSig consulted by `nullaryApp`
/// (Theory/Text/Parser/Term.hs:139-143).  HS sets it via
/// `setState (mkStateSig msig)` at the top of `parseIntruderRules`
/// (Theory/Text/Parser/Rule.hs:200-204).
pub struct MaudeSigNullaryGuard {
    _nullary: UserNullaryFunsGuard,
}

impl MaudeSigNullaryGuard {
    /// Push the 0-arity NoEq names from `msig` into `USER_NULLARY_FUNS`.
    pub fn set(msig: &MaudeSig) -> Self {
        let nullary_funs: BTreeSet<String> =
            builtin_nullary_names_from_msig(msig).into_iter().collect();
        MaudeSigNullaryGuard {
            _nullary: UserNullaryFunsGuard::set(nullary_funs),
        }
    }
}

/// Re-collects the user-declared unary / nullary / private function
/// names from `parser_theory` and pushes them into the thread-locals
/// read by `term_to_lnterm`.  Returns an RAII guard whose drop
/// restores the previous values.  Use from `prove_lemma` so search-
/// time term conversions see the right per-theory signature info.
pub fn set_user_funs_for_theory(parser_theory: &p::Theory) -> UserFunsForTheoryGuard {
    let unary_funs: BTreeSet<String> = parser_theory.items.iter().flat_map(|it| {
        if let p::TheoryItem::Functions(decls) = it {
            decls.iter().filter(|d| d.arg_types.len() == 1)
                .map(|d| d.name.clone()).collect::<Vec<_>>()
        } else { Vec::new() }
    }).collect();
    let mut nullary_funs: BTreeSet<String> = parser_theory.items.iter().flat_map(|it| {
        if let p::TheoryItem::Functions(decls) = it {
            decls.iter().filter(|d| d.arg_types.is_empty())
                .map(|d| d.name.clone()).collect::<Vec<_>>()
        } else { Vec::new() }
    }).collect();
    for it in &parser_theory.items {
        if let p::TheoryItem::Builtins(names) = it {
            for n in names {
                for c in builtin_nullary_constants(n) {
                    nullary_funs.insert(c.to_string());
                }
            }
        }
    }
    let private_funs: BTreeSet<String> = parser_theory.items.iter().flat_map(|it| {
        if let p::TheoryItem::Functions(decls) = it {
            decls.iter().filter(|d| d.private).map(|d| d.name.clone()).collect::<Vec<_>>()
        } else { Vec::new() }
    }).collect();
    UserFunsForTheoryGuard {
        _unary: UserUnaryFunsGuard::set(unary_funs),
        _nullary: UserNullaryFunsGuard::set(nullary_funs),
        _private: UserPrivateFunsGuard::set(private_funs),
    }
}

fn elaborate_already_expanded(parser_thy: &p::Theory) -> Result<Theory, ElabError> {
    let mut sig = SignaturePure::empty(parser_thy.is_diff);
    if parser_thy.is_diff {
        sig.maude_sig = sig.maude_sig.merge(enable_diff_maude_sig());
    }

    let mut thy: Theory = Theory::new(parser_thy.name.clone(), sig);
    thy.in_file = String::new();
    thy.is_sapic = parser_thy.items.iter().any(|i|
        matches!(i, p::TheoryItem::ProcessDef(_)
            | p::TheoryItem::TopLevelProcess(_)
            | p::TheoryItem::EquivLemma(_, _)
            | p::TheoryItem::DiffEquivLemma(_)));

    if let Some(cfg) = &parser_thy.configuration {
        thy.items.push(TheoryItem::ConfigBlock(cfg.clone()));
    }

    elaborate_items(&parser_thy.items, &mut thy)?;
    Ok(thy)
}

fn elaborate_items(
    items: &[p::TheoryItem],
    out: &mut Theory,
) -> Result<(), ElabError> {
    for item in items {
        match item {
            p::TheoryItem::Builtins(names) => {
                let mut s = out.signature.maude_sig.clone();
                for name in names {
                    if let Some(sig) = builtin_sig(name) {
                        s = s.merge(sig);
                    }
                    if name == "diff" || name == "diffie-hellman" {
                        // ensure dh on
                        s.enable_dh = true;
                        s = s.refresh();
                    }
                    out.items.push(TheoryItem::Translation(
                        TranslationElement::SignatureBuiltin(name.clone())));
                }
                out.signature.maude_sig = s;
            }
            p::TheoryItem::Functions(decls) => {
                for d in decls {
                    let arity = d.arg_types.len();
                    let priv_ = if d.private { Privacy::Private } else { Privacy::Public };
                    let constr = if d.destructor { Constructability::Destructor } else { Constructability::Constructor };
                    let sym = NoEqSym::new(d.name.as_bytes().to_vec(), arity, priv_, constr);
                    out.signature.maude_sig =
                        out.signature.maude_sig.clone().add_fun_sym(sym);
                }
            }
            p::TheoryItem::Equations { eqs, convergent } => {
                // Port of Haskell `addEquationsM` (Theory.hs).
                // Convert each LHS=RHS pair to a CtxtStRule via
                // `rrule_to_ctxt_st_rule` and install it on the MaudeSig
                // so Maude sees the rewrite rule in its `fmod MSG ...`
                // module.  Convergent flag is stored as informational.
                out.signature.maude_sig.eq_convergent = *convergent;
                let mut s = out.signature.maude_sig.clone();
                for eq in eqs {
                    let (Some(l), Some(r)) =
                        (term_to_lnterm(&eq.lhs), term_to_lnterm(&eq.rhs)) else { continue };
                    let rrule = tamarin_term::rewriting::RRule::new(l, r);
                    if let Some(ctxt) = tamarin_term::subterm_rule::rrule_to_ctxt_st_rule(&rrule) {
                        s = s.add_ctxt_st_rule(ctxt);
                    }
                }
                out.signature.maude_sig = s.refresh();
            }
            p::TheoryItem::Macros(macros) => {
                let mut ms = Vec::new();
                for m in macros {
                    let args: Vec<LVar> = m.args.iter()
                        .map(|v| LVar::new(v.name.clone(), sort_of(&v.sort), v.idx))
                        .collect();
                    let body = match term_to_lnterm(&m.body) {
                        Some(t) => t,
                        None => continue, // best-effort, skip on failure
                    };
                    // Register macro fun-sym in MaudeSig — mirrors HS
                    // `addMacroSym (op,(k,Private,Destructor))`
                    // (Theory/Text/Parser/Macro.hs:48) and
                    // `macroToFunSym` (Term/Macro.hs:30).  After parser-
                    // AST macro expansion (run in `elaborate()` above)
                    // call sites no longer reference the macro name, but
                    // the fun-sym must still be present in MaudeSig so
                    // Maude / source precomputation / round-trip parsers
                    // see the same signature as HS.
                    let sym = NoEqSym::new(
                        m.name.as_bytes().to_vec(),
                        args.len(),
                        Privacy::Private,
                        Constructability::Destructor,
                    );
                    out.signature.maude_sig =
                        out.signature.maude_sig.clone().add_macro_sym(sym);
                    ms.push(LNMacro { name: m.name.clone(), args, body });
                }
                if !ms.is_empty() { out.items.push(TheoryItem::Macros(ms)); }
            }
            p::TheoryItem::Predicates(_predicates) => {
                // Predicate elaboration needs a typed Fact + LNFormula.
                // Skip for now; the parser-AST predicate is preserved
                // by the wf checker through different means.
            }
            p::TheoryItem::Options(opts) => {
                let mut o = out.options.clone();
                for n in opts {
                    match n.as_str() {
                        "translation-progress" => o.trans_progress = true,
                        "translation-allow-pattern-lookups" => o.trans_allow_pattern_matching_in_lookup = true,
                        "translation-state-optimisation" => o.state_channel_opt = true,
                        "translation-asynchronous-channels" => o.asynchronous_channels = true,
                        "translation-compress-events" => o.compress_events = true,
                        _ => {}
                    }
                }
                out.options = o;
            }
            p::TheoryItem::Heuristic(h) => {
                out.heuristic.push(h.clone());
            }
            p::TheoryItem::Tactic(t) => {
                out.tactic.push(t.raw.clone());
            }
            p::TheoryItem::Restriction(r) => {
                let or = OpenRestriction::new(r.name.clone(), r.formula.clone());
                out.items.push(TheoryItem::Restriction(or));
            }
            p::TheoryItem::LegacyAxiom(r) => {
                let or = OpenRestriction::new(r.name.clone(), r.formula.clone());
                out.items.push(TheoryItem::Restriction(or));
            }
            p::TheoryItem::Rule(r) | p::TheoryItem::IntrRule(r) => {
                let elab = rule_to_proto_rule_e(r)?;
                out.items.push(TheoryItem::Rule(OpenProtoRule::new(elab)));
            }
            p::TheoryItem::Lemma(l) => {
                let lem: Lemma = Lemma {
                    name: l.name.clone(),
                    modulo: l.modulo.clone(),
                    attributes: l.attributes.iter().map(elaborate_lemma_attr).collect(),
                    trace_quantifier: match l.trace_quantifier {
                        p::TraceQuantifier::AllTraces => TraceQuantifier::AllTraces,
                        p::TraceQuantifier::ExistsTrace => TraceQuantifier::ExistsTrace,
                    },
                    formula: l.formula.clone(),
                    proof: ProofSkeleton {
                        raw: l.proof.as_ref().map(|p| p.raw.clone()).unwrap_or_default(),
                        tree: l.proof.as_ref().and_then(|p| p.tree.clone()),
                    },
                };
                out.items.push(TheoryItem::Lemma(lem));
            }
            p::TheoryItem::DiffLemma(_dl) => {
                // DiffLemma lives in DiffTheory only. In a non-diff
                // theory we'd reject; for now silently drop.
            }
            p::TheoryItem::AccLemma(a) => {
                let acc = AccLemma {
                    name: a.name.clone(),
                    attributes: a.attributes.iter().map(elaborate_lemma_attr).collect(),
                    formula: a.formula.clone(),
                    case_test_idents: a.case_test_idents.clone(),
                };
                out.items.push(TheoryItem::Translation(TranslationElement::AccLemma(acc)));
            }
            p::TheoryItem::CaseTest(c) => {
                let ct = CaseTest { name: c.name.clone(), formula: c.formula.clone() };
                out.items.push(TheoryItem::Translation(TranslationElement::CaseTest(ct)));
            }
            p::TheoryItem::ProcessDef(_) | p::TheoryItem::TopLevelProcess(_)
            | p::TheoryItem::EquivLemma(_, _) | p::TheoryItem::DiffEquivLemma(_) => {
                // Process elaboration is a separate, large pass — left
                // for the SAPIC port. We keep the items in the source
                // representation by skipping for now.
            }
            p::TheoryItem::Export { tag, body } => {
                out.items.push(TheoryItem::Translation(
                    TranslationElement::ExportInfo {
                        tag: tag.clone(), body: body.clone() }));
            }
            p::TheoryItem::FormalComment { header, body } => {
                out.items.push(TheoryItem::Text((header.clone(), body.clone())));
            }
            p::TheoryItem::IfDef { then_items, else_items, .. } => {
                // The parser already expanded #ifdef branches based on
                // the flags; both `then_items` and `else_items` are
                // populated only for the live branch.
                elaborate_items(then_items, out)?;
                if let Some(else_b) = else_items { elaborate_items(else_b, out)?; }
            }
            p::TheoryItem::Define(_) | p::TheoryItem::Include(_) => {
                // Already handled by the parser preprocessor.
            }
        }
    }
    Ok(())
}

fn elaborate_lemma_attr(a: &p::LemmaAttr) -> LemmaAttr {
    match a {
        p::LemmaAttr::Sources => LemmaAttr::Sources,
        p::LemmaAttr::Reuse => LemmaAttr::Reuse,
        p::LemmaAttr::DiffReuse => LemmaAttr::DiffReuse,
        p::LemmaAttr::UseInduction => LemmaAttr::UseInduction,
        p::LemmaAttr::HideLemma(s) => LemmaAttr::HideLemma(s.clone()),
        p::LemmaAttr::Heuristic(s) => LemmaAttr::Heuristic(s.clone()),
        p::LemmaAttr::Output(v) => LemmaAttr::Output(v.clone()),
        p::LemmaAttr::Left => LemmaAttr::Left,
        p::LemmaAttr::Right => LemmaAttr::Right,
        p::LemmaAttr::Hint(s) => LemmaAttr::Hint(s.clone()),
    }
}

// =============================================================================
// Rule elaboration
// =============================================================================

fn rule_to_proto_rule_e(r: &p::Rule) -> Result<ProtoRuleE, ElabError> {
    let info = ProtoRuleEInfo {
        name: ProtoRuleName::Stand(r.name.clone()),
        attributes: RuleAttributes::empty(),
        restrictions: Vec::new(),
    };
    // Desugar let-bindings before fact conversion: each `let x = t in ...`
    // binding substitutes `x` with `t` in the rule body.
    let r_owned: p::Rule;
    let r_eff = if r.let_block.is_empty() { r } else {
        r_owned = apply_let_block(r);
        &r_owned
    };
    let prems = r_eff.premises.iter().map(fact_to_lnfact)
        .collect::<Result<Vec<_>, _>>()?;
    let acts  = r_eff.actions.iter().map(fact_to_lnfact)
        .collect::<Result<Vec<_>, _>>()?;
    let concs = r_eff.conclusions.iter().map(fact_to_lnfact)
        .collect::<Result<Vec<_>, _>>()?;
    let new_vars = compute_new_vars(&prems, &concs, &acts);
    let _ = (std::marker::PhantomData::<PremIdx>, std::marker::PhantomData::<ConcIdx>);

    Ok(Rule::new(info, prems, concs, acts).with_new_vars(new_vars))
}

/// Desugar a rule's `let x_1 = t_1 ... x_n = t_n in body` block by
/// substituting each binding's RHS for occurrences of the LHS in the
/// body (premises, actions, conclusions, embedded restrictions).
/// Bindings are sequential — later bindings see earlier substitutions
/// applied. Mirrors Haskell tamarin's rule-let desugaring.
pub fn apply_let_block(r: &p::Rule) -> p::Rule {
    let mut out = r.clone();
    let bindings = std::mem::take(&mut out.let_block);

    // Apply each binding in order, accumulating later RHS rewrites with
    // earlier substitutions already baked in.
    let mut applied: Vec<(p::Term, p::Term)> = Vec::new();
    for b in bindings {
        let mut value = b.value;
        for (k, v) in &applied {
            value = subst_term(&value, k, v);
        }
        applied.push((b.var, value));
    }
    for (k, v) in &applied {
        for f in &mut out.premises    { subst_fact_in_place(f, k, v); }
        for f in &mut out.actions     { subst_fact_in_place(f, k, v); }
        for f in &mut out.conclusions { subst_fact_in_place(f, k, v); }
        for phi in &mut out.embedded_restrictions {
            subst_formula_in_place(phi, k, v);
        }
    }
    out
}

fn subst_term(t: &p::Term, key: &p::Term, val: &p::Term) -> p::Term {
    if t == key { return val.clone(); }
    match t {
        p::Term::App(name, args) => p::Term::App(
            name.clone(),
            args.iter().map(|a| subst_term(a, key, val)).collect(),
        ),
        p::Term::AlgApp(name, a, b) => p::Term::AlgApp(
            name.clone(),
            Box::new(subst_term(a, key, val)),
            Box::new(subst_term(b, key, val)),
        ),
        p::Term::Pair(args) => p::Term::Pair(
            args.iter().map(|a| subst_term(a, key, val)).collect(),
        ),
        p::Term::Diff(a, b) => p::Term::Diff(
            Box::new(subst_term(a, key, val)),
            Box::new(subst_term(b, key, val)),
        ),
        p::Term::BinOp(op, a, b) => p::Term::BinOp(
            *op,
            Box::new(subst_term(a, key, val)),
            Box::new(subst_term(b, key, val)),
        ),
        p::Term::PatMatch(a) => p::Term::PatMatch(
            Box::new(subst_term(a, key, val)),
        ),
        // Atoms and literals: no recursion.
        p::Term::Var(_) | p::Term::PubLit(_) | p::Term::FreshLit(_)
        | p::Term::NatLit(_) | p::Term::Number(_) | p::Term::NumberOne
        | p::Term::NatOne | p::Term::DhNeutral => t.clone(),
    }
}

fn subst_fact_in_place(f: &mut p::Fact, key: &p::Term, val: &p::Term) {
    for a in &mut f.args { *a = subst_term(a, key, val); }
}

fn subst_formula_in_place(phi: &mut p::Formula, key: &p::Term, val: &p::Term) {
    use p::Formula::*;
    match phi {
        False | True => {}
        Atom(a) => subst_atom_in_place(a, key, val),
        Not(p) => subst_formula_in_place(p, key, val),
        And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b) => {
            subst_formula_in_place(a, key, val);
            subst_formula_in_place(b, key, val);
        }
        Forall(_, body) | Exists(_, body) => {
            subst_formula_in_place(body, key, val);
        }
    }
}

fn subst_atom_in_place(a: &mut p::Atom, key: &p::Term, val: &p::Term) {
    use p::Atom::*;
    match a {
        Eq(x, y) | Less(x, y) | LessMset(x, y) | Subterm(x, y) => {
            *x = subst_term(x, key, val);
            *y = subst_term(y, key, val);
        }
        Action(f, t) => {
            subst_fact_in_place(f, key, val);
            *t = subst_term(t, key, val);
        }
        Last(t) => { *t = subst_term(t, key, val); }
        Pred(f) => subst_fact_in_place(f, key, val),
    }
}

pub fn fact_to_lnfact(f: &p::Fact) -> Result<crate::fact::LNFact, ElabError> {
    use crate::fact::{Fact, FactTag, Multiplicity};
    // Tag mapping mirrors Haskell's parser in
    // `Theory.Text.Parser.Fact.mkProtoFact`:
    //   "OUT" → outFact (Out)
    //   "IN"  → inFact  (In)
    //   "KU"  → kuFact  (KUFact)
    //   "KD"  → kdFact  (KDFact)
    //   "DED" → dedLogFact (DedFact)
    //   "FR"  → freshFact (Fresh)
    //   else  → protoFact (ProtoFact tag with name)
    //
    // Critically, `K` is *not* in this list — Haskell's parser falls
    // through to the protoFact case for "K", giving `ProtoFact Linear "K"`.
    // That matches ISend's action `kLogFact = protoFact Linear "K"`,
    // so user lemma `K(t) @ j` correctly matches ISend instances.
    // We previously aliased "K" → FactTag::Ku, which broke witness
    // construction for any lemma using K(_) atoms (they couldn't
    // satisfy via ISend; only Coerce/etc. routes were available).
    let tag = match f.name.as_str() {
        "Fr" => FactTag::Fresh,
        "In" => FactTag::In,
        "Out" => FactTag::Out,
        "KU" => FactTag::Ku,
        "KD" => FactTag::Kd,
        "Ded" => FactTag::Ded,
        _ => FactTag::Proto(
            if f.persistent { Multiplicity::Persistent } else { Multiplicity::Linear },
            f.name.clone(),
            f.args.len(),
        ),
    };
    let terms: Result<Vec<_>, _> = f.args.iter()
        .map(|t| term_to_lnterm(t).ok_or_else(||
            ElabError { message: format!("could not elaborate term in fact `{}`", f.name) }))
        .collect();
    let mut fact = Fact::new(tag, terms?);
    let mut anns: BTreeSet<crate::fact::FactAnnotation> = BTreeSet::new();
    for ann in &f.annotations {
        anns.insert(match ann {
            p::FactAnnotation::SolveFirst => crate::fact::FactAnnotation::SolveFirst,
            p::FactAnnotation::SolveLast => crate::fact::FactAnnotation::SolveLast,
            p::FactAnnotation::NoSources => crate::fact::FactAnnotation::NoSources,
        });
    }
    fact = fact.with_annotations(anns);
    Ok(fact)
}

fn compute_new_vars(
    prems: &[crate::fact::LNFact],
    concs: &[crate::fact::LNFact],
    acts: &[crate::fact::LNFact],
) -> Vec<tamarin_term::lterm::LNTerm> {
    let mut prem_vars: BTreeSet<LVar> = BTreeSet::new();
    for f in prems {
        for t in &f.terms { collect_vars(t, &mut prem_vars); }
    }
    let mut new_set: BTreeSet<LVar> = BTreeSet::new();
    for f in concs.iter().chain(acts) {
        for t in &f.terms {
            let mut here = BTreeSet::new();
            collect_vars(t, &mut here);
            for v in here {
                if !prem_vars.contains(&v) { new_set.insert(v); }
            }
        }
    }
    new_set.into_iter().map(|v| Term::Lit(Lit::Var(v))).collect()
}

fn collect_vars(t: &tamarin_term::lterm::LNTerm, out: &mut BTreeSet<LVar>) {
    match t {
        Term::Lit(Lit::Var(v)) => { out.insert(v.clone()); }
        Term::Lit(_) => {}
        Term::App(_, args) => for a in args.iter() { collect_vars(a, out); }
    }
}

// =============================================================================
// Term conversion: parser::Term → LNTerm
// =============================================================================

fn sort_of(s: &p::SortHint) -> LSort {
    match s {
        p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) => LSort::Fresh,
        p::SortHint::Pub   | p::SortHint::Suffix(p::SuffixSort::Pub) => LSort::Pub,
        p::SortHint::Node  | p::SortHint::Suffix(p::SuffixSort::Node) => LSort::Node,
        p::SortHint::Nat   | p::SortHint::Suffix(p::SuffixSort::Nat) => LSort::Nat,
        p::SortHint::Msg   | p::SortHint::Suffix(p::SuffixSort::Msg)
        | p::SortHint::Untagged => LSort::Msg,
    }
}

/// Best-effort conversion of a parser term to an `LNTerm`. Returns
/// Convert an `LNTerm` back to a parser-AST term. Used when we
/// need to translate Maude-produced substitutions back into the
/// parser-AST world (e.g. for `insert_implied_formulas`).
pub fn lnterm_to_term(t: &tamarin_term::lterm::LNTerm) -> p::Term {
    use tamarin_term::function_symbols::FunSym;
    use tamarin_term::vterm::Lit;
    use tamarin_term::lterm::LSort;
    match t {
        tamarin_term::term::Term::Lit(Lit::Var(v)) => {
            let sort = match v.sort {
                LSort::Msg => p::SortHint::Msg,
                LSort::Pub => p::SortHint::Pub,
                LSort::Fresh => p::SortHint::Fresh,
                LSort::Node => p::SortHint::Node,
                LSort::Nat => p::SortHint::Nat,
            };
            p::Term::Var(p::VarSpec {
                name: v.name.clone(),
                idx: v.idx,
                sort,
                typ: None,
            })
        }
        tamarin_term::term::Term::Lit(Lit::Con(name)) => {
            // Encode as the right literal kind based on the sort hint
            // attached to the name's tag.
            match name.tag {
                tamarin_term::lterm::NameTag::Pub => p::Term::PubLit(name.id.0.clone()),
                tamarin_term::lterm::NameTag::Fresh => p::Term::FreshLit(name.id.0.clone()),
                tamarin_term::lterm::NameTag::Nat => p::Term::NatLit(name.id.0.clone()),
                tamarin_term::lterm::NameTag::Node => p::Term::PubLit(name.id.0.clone()),
            }
        }
        tamarin_term::term::Term::App(funsym, args) => {
            let parser_args: Vec<p::Term> = args.iter().map(lnterm_to_term).collect();
            match funsym {
                FunSym::NoEq(s) => {
                    let name = String::from_utf8(s.name.clone())
                        .unwrap_or_default();
                    if name == "pair" && parser_args.len() == 2 {
                        // Re-pair into a flat Pair term where possible.
                        // Right-assoc: pair(a, pair(b, c)) → Pair([a, b, c]).
                        let mut flat = vec![parser_args[0].clone()];
                        match &parser_args[1] {
                            p::Term::Pair(rest) => flat.extend(rest.clone()),
                            other => flat.push(other.clone()),
                        }
                        p::Term::Pair(flat)
                    } else {
                        p::Term::App(name, parser_args)
                    }
                }
                FunSym::Ac(ac) => {
                    // Round-trip AC heads back to parser BinOp so that a
                    // later `term_to_lnterm` call rebuilds them as the
                    // proper `FunSym::Ac` head (not as `NoEqSym("?")`).
                    // Without this, `insert_implied_formulas_pass`'s
                    // Maude-backed matcher (`match_atom_via_maude`) sees
                    // a NoEq-headed pattern against an Ac-headed
                    // subject, and AC matching fails — observed on
                    // MTI_C0::Secrecy_..._Initiator where the lemma's
                    // `AcceptedR(... exp(g, ~tid*~x.5) ...)` universal
                    // pattern arrives at the matcher as
                    // `exp(g, NoEq("?", 2, ekI, x))` and never matches
                    // the system's `exp(g, Mult(x, ekI))`.
                    // Mirrors HS's `viewTerm` round-trip via `FApp (AC m)`
                    // (Term/Term.hs: viewTerm).
                    use tamarin_term::function_symbols::AcSym;
                    // AC terms are flattened by `f_app_ac` to 2+ args.
                    // Round-trip via parser BinOp (left-fold), which
                    // term_to_lnterm later rebuilds as a flat AC App.
                    // Previously this only fired on EXACTLY 2 args — any
                    // flat 3+-arg AC term (common with multiset: `a + b + c`)
                    // fell through to the `?Union` placeholder branch and
                    // a downstream `term_to_lnterm` re-parse rebuilt it as
                    // `App(NoEq("?Union"), [a,b,c])`, an opaque non-AC
                    // 3-ary functor.  That broke Maude unification on
                    // multiset equations (e.g. `('1'++x++z) = x` returned
                    // No-unifier in the Eq branch but the LNTerm we
                    // actually fed Maude was `Union(1,x,z) =? x` vs a
                    // BROKEN return-form leaking into impl_formulas matches
                    // and breaking the `1+x+z` → false simplification
                    // chain for `counters_linear_order`.
                    if parser_args.len() >= 2 {
                        let op = match ac {
                            AcSym::Mult => p::BinOp::Mult,
                            AcSym::Union => p::BinOp::Union,
                            AcSym::Xor => p::BinOp::Xor,
                            AcSym::NatPlus => p::BinOp::NatPlus,
                        };
                        // Left-fold: a parser BinOp is strictly arity-2,
                        // so fold left-to-right when more than 2 args.
                        let mut iter = parser_args.into_iter();
                        let first = iter.next().unwrap();
                        let second = iter.next().unwrap();
                        let mut acc = p::Term::BinOp(op, Box::new(first), Box::new(second));
                        for next in iter {
                            acc = p::Term::BinOp(op, Box::new(acc), Box::new(next));
                        }
                        acc
                    } else {
                        // Defensive: 0- or 1-arg AC term shouldn't occur
                        // (AC operators are arity-2), but emit a
                        // recognisable placeholder if it does.
                        let name = match ac {
                            AcSym::Mult => "?Mult",
                            AcSym::Union => "?Union",
                            AcSym::Xor => "?Xor",
                            AcSym::NatPlus => "?NatPlus",
                        };
                        p::Term::App(name.to_string(), parser_args)
                    }
                }
                FunSym::C(_) | FunSym::List => {
                    let name = "?".to_string();
                    p::Term::App(name, parser_args)
                }
            }
        }
    }
}

/// `None` on constructs we can't yet round-trip (e.g. `PatMatch`,
/// algebraic-app `f{a}b` without enough context for proper sigil
/// inference).
pub fn term_to_lnterm(t: &p::Term) -> Option<tamarin_term::lterm::LNTerm> {
    use tamarin_term::function_symbols::AcSym;
    use tamarin_term::term::f_app_ac;

    match t {
        p::Term::Var(v) => {
            // A bare identifier in surface syntax may denote a 0-arity
            // function symbol (e.g. `true` when `builtins: signing` is
            // enabled).  Haskell's `term` parser disambiguates this
            // via `nullaryApp` against the maudeSig in parser state;
            // our parser doesn't, so the lexer leaves it as
            // `Var{name, sort: Untagged}`.  We recover the constant
            // here.  Only fires for `Untagged` sort + idx 0 — a user
            // can still bind a Msg-sort var named `true` if they
            // explicitly annotate it (e.g. `true:msg`), and the parser
            // would emit `Untagged` only for the bare form anyway.
            if matches!(v.sort, p::SortHint::Untagged) && v.idx == 0
                && is_user_nullary_fun(&v.name) {
                let sym = NoEqSym::new(v.name.as_bytes().to_vec(), 0,
                    user_fun_privacy(&v.name), Constructability::Constructor);
                return Some(f_app_no_eq(sym, vec![]));
            }
            let lv = LVar::new(v.name.clone(), sort_of(&v.sort), v.idx);
            Some(Term::Lit(Lit::Var(lv)))
        }
        p::Term::PubLit(s) => {
            let n = Name::new(NameTag::Pub, s.clone());
            Some(Term::Lit(Lit::Con(n)))
        }
        p::Term::FreshLit(s) => {
            let n = Name::new(NameTag::Fresh, s.clone());
            Some(Term::Lit(Lit::Con(n)))
        }
        p::Term::NatLit(s) => {
            let n = Name::new(NameTag::Nat, s.clone());
            Some(Term::Lit(Lit::Con(n)))
        }
        p::Term::NumberOne => {
            // HS `fAppOne = fAppNoEq oneSym []` (Term/Term.hs:127); the
            // `"1"` keyword in the term parser dispatches to this
            // (Theory/Text/Parser/Term.hs:130).  Mirror exactly — emit
            // a 0-arity NoEq application of `oneSym`, NOT a public
            // constant.  Treating it as `Lit::Con(Pub,"1")` causes
            // source-case enumeration to mismatch HS's `c_one` rule.
            Some(f_app_no_eq(
                tamarin_term::function_symbols::one_sym(),
                vec![],
            ))
        }
        p::Term::DhNeutral => {
            // HS `fAppDHNeutral = fAppNoEq dhNeutralSym []` (Term/Term.hs:130);
            // dispatched by `symbol "DH_neutral" *> pure fAppDHNeutral`
            // (Theory/Text/Parser/Term.hs:127).
            Some(f_app_no_eq(
                tamarin_term::function_symbols::dh_neutral_sym(),
                vec![],
            ))
        }
        p::Term::NatOne => {
            // HS `fAppNatOne = fAppNoEq natOneSym []` (Term/Term.hs); the
            // `1:nat` / `%1` keywords dispatch to this
            // (Theory/Text/Parser/Term.hs:128-129).
            Some(f_app_no_eq(
                tamarin_term::function_symbols::nat_one_sym(),
                vec![],
            ))
        }
        p::Term::Number(_) => {
            // Generic numeric literal — surface form `1`, `2`, …  We
            // don't yet model these as LNTerm constants in a
            // type-correct way; fall back to a public constant
            // placeholder.  TODO: model as proper nat / public name.
            let n = Name::new(NameTag::Pub, "n".to_string());
            Some(Term::Lit(Lit::Con(n)))
        }
        p::Term::App(name, args) => {
            // Multi-arg unary builtins: `h(a, b, c)` is parsed as
            // `App("h", [a, b, c])` but Haskell Tamarin folds the
            // surplus args into a right-associative pair so the
            // function stays arity-1: `h(<a, b, c>)`.  Without this,
            // KU source-cases (precomputed using the canonical
            // arity-1 signature) never match the runtime arity-3
            // term, leaving e.g. `c_h` out of the case list.
            // Currently only `h` (from `builtins: hashing`) is
            // unary; other multi-arg builtins (senc/aenc/sign/...)
            // are genuinely multi-arg.
            let unary_builtin = matches!(name.as_str(), "h" | "fst" | "snd" | "inv" | "pk")
                || is_user_unary_fun(name.as_str());
            let new_args: Option<Vec<_>> = args.iter().map(term_to_lnterm).collect();
            let mut new_args = new_args?;
            if unary_builtin && new_args.len() > 1 {
                // Wrap args into a right-associative pair to make
                // the call arity-1.
                let mut iter = new_args.into_iter().rev();
                let last = iter.next()?;
                let mut acc = last;
                for prev in iter {
                    let pair_sym = NoEqSym::new(b"pair".to_vec(), 2,
                        Privacy::Public, Constructability::Constructor);
                    acc = f_app_no_eq(pair_sym, vec![prev, acc]);
                }
                new_args = vec![acc];
            }
            let sym = NoEqSym::new(name.as_bytes().to_vec(), new_args.len(),
                user_fun_privacy(name), Constructability::Constructor);
            Some(f_app_no_eq(sym, new_args))
        }
        p::Term::Pair(items) => {
            let new_items: Option<Vec<_>> = items.iter().map(term_to_lnterm).collect();
            let new_items = new_items?;
            // Right-associative pair: <a, b, c> = pair(a, pair(b, c))
            let mut iter = new_items.into_iter().rev();
            let last = iter.next()?;
            let mut acc = last;
            for prev in iter {
                let sym = NoEqSym::new(b"pair".to_vec(), 2,
                    Privacy::Public, Constructability::Constructor);
                acc = f_app_no_eq(sym, vec![prev, acc]);
            }
            Some(acc)
        }
        p::Term::AlgApp(name, a, b) => {
            // `f{a}b` desugars to `f(a, b)` semantically; users typically
            // use this for senc/aenc/sign/mac.
            let aa = term_to_lnterm(a)?;
            let bb = term_to_lnterm(b)?;
            let sym = NoEqSym::new(name.as_bytes().to_vec(), 2,
                Privacy::Public, Constructability::Constructor);
            Some(f_app_no_eq(sym, vec![aa, bb]))
        }
        p::Term::Diff(a, b) => {
            let aa = term_to_lnterm(a)?;
            let bb = term_to_lnterm(b)?;
            let sym = NoEqSym::new(b"diff".to_vec(), 2,
                Privacy::Public, Constructability::Constructor);
            Some(f_app_no_eq(sym, vec![aa, bb]))
        }
        p::Term::BinOp(op, a, b) => {
            let aa = term_to_lnterm(a)?;
            let bb = term_to_lnterm(b)?;
            match op {
                p::BinOp::Mult => Some(f_app_ac(AcSym::Mult, vec![aa, bb])),
                p::BinOp::Union => Some(f_app_ac(AcSym::Union, vec![aa, bb])),
                p::BinOp::Xor => Some(f_app_ac(AcSym::Xor, vec![aa, bb])),
                p::BinOp::NatPlus => Some(f_app_ac(AcSym::NatPlus, vec![aa, bb])),
                p::BinOp::Exp => {
                    let sym = NoEqSym::new(b"exp".to_vec(), 2,
                        Privacy::Public, Constructability::Constructor);
                    Some(f_app_no_eq(sym, vec![aa, bb]))
                }
            }
        }
        p::Term::PatMatch(_) => None,
    }
}

// =============================================================================
// Builtin → MaudeSig
// =============================================================================

fn builtin_sig(name: &str) -> Option<MaudeSig> {
    match name {
        "diffie-hellman" => Some(dh_maude_sig()),
        "bilinear-pairing" => Some(bp_maude_sig()),
        "multiset" => Some(mset_maude_sig()),
        "natural-numbers" => Some(nat_maude_sig()),
        "xor" => Some(xor_maude_sig()),
        "symmetric-encryption" => Some(sym_enc_maude_sig()),
        "asymmetric-encryption" => Some(asym_enc_maude_sig()),
        "signing" => Some(signature_maude_sig()),
        "revealing-signing" => Some(reveal_signature_maude_sig()),
        "hashing" => Some(hash_maude_sig()),
        "locations-report" => Some(location_report_maude_sig()),
        "dest-symmetric-encryption" => Some(sym_enc_dest_maude_sig()),
        "dest-asymmetric-encryption" => Some(asym_enc_dest_maude_sig()),
        "dest-signing" => Some(signature_dest_maude_sig()),
        "dest-pairing" => Some(pair_maude_sig()), // pair-with-destructors
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_parser::parse_theory;

    #[test]
    fn elaborate_empty_theory() {
        let p = parse_theory("theory T begin end", &[]).unwrap();
        let t = elaborate(&p).unwrap();
        assert_eq!(t.name, "T");
    }

    #[test]
    fn elaborate_builtins() {
        let p = parse_theory("theory T begin builtins: hashing, signing end", &[]).unwrap();
        let t = elaborate(&p).unwrap();
        // hashing adds h/1, signing adds sign/2 etc.
        let funs: Vec<String> = t.signature.maude_sig.st_fun_syms.iter()
            .map(|s| String::from_utf8_lossy(&s.name).to_string())
            .collect();
        assert!(funs.iter().any(|n| n == "h"), "expected h: {:?}", funs);
        assert!(funs.iter().any(|n| n == "sign"), "expected sign: {:?}", funs);
    }

    #[test]
    fn elaborate_simple_rule() {
        let src = r#"theory T begin
            rule R: [Fr(~k)] --[Foo(~k)]-> [Out(~k)]
        end"#;
        let p = parse_theory(src, &[]).unwrap();
        let t = elaborate(&p).unwrap();
        let rules: Vec<_> = t.rules().collect();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].name(), "R");
    }

    #[test]
    fn elaborate_lemma_passthrough() {
        let src = r#"theory T begin
            rule R: [Fr(~k)] --[Foo(~k)]-> [Out(~k)]
            lemma secret: "All k #i. Foo(k) @ i ==> F"
        end"#;
        let p = parse_theory(src, &[]).unwrap();
        let t = elaborate(&p).unwrap();
        assert_eq!(t.lemmas().count(), 1);
        let l = t.lemmas().next().unwrap();
        assert_eq!(l.name, "secret");
        assert_eq!(l.trace_quantifier, TraceQuantifier::AllTraces);
    }

    // =========================================================================
    // lnterm_to_term round-tripping correctness
    // =========================================================================

    fn parser_var(name: &str, idx: u64, sort: p::SortHint) -> p::Term {
        p::Term::Var(p::VarSpec { name: name.into(), idx, sort, typ: None })
    }

    #[test]
    fn lnterm_to_term_round_trip_var_msg() {
        let v = parser_var("x", 7, p::SortHint::Msg);
        let lt = term_to_lnterm(&v).unwrap();
        let back = lnterm_to_term(&lt);
        assert_eq!(back, v);
    }

    #[test]
    fn lnterm_to_term_round_trip_var_fresh() {
        let v = parser_var("k", 3, p::SortHint::Fresh);
        let lt = term_to_lnterm(&v).unwrap();
        assert_eq!(lnterm_to_term(&lt), v);
    }

    #[test]
    fn lnterm_to_term_round_trip_var_node() {
        let v = parser_var("i", 0, p::SortHint::Node);
        let lt = term_to_lnterm(&v).unwrap();
        assert_eq!(lnterm_to_term(&lt), v);
    }

    #[test]
    fn lnterm_to_term_round_trip_pub_lit() {
        let pl = p::Term::PubLit("Alice".into());
        let lt = term_to_lnterm(&pl).unwrap();
        assert_eq!(lnterm_to_term(&lt), pl);
    }

    #[test]
    fn lnterm_to_term_round_trip_fresh_lit() {
        let fl = p::Term::FreshLit("n42".into());
        let lt = term_to_lnterm(&fl).unwrap();
        assert_eq!(lnterm_to_term(&lt), fl);
    }

    #[test]
    fn lnterm_to_term_round_trip_pair() {
        // <a, b> → pair(a, b) → back to Pair([a, b]).
        let pair = p::Term::Pair(vec![
            parser_var("a", 0, p::SortHint::Msg),
            parser_var("b", 0, p::SortHint::Msg),
        ]);
        let lt = term_to_lnterm(&pair).unwrap();
        let back = lnterm_to_term(&lt);
        assert_eq!(back, pair);
    }

    #[test]
    fn lnterm_to_term_round_trip_triple() {
        // <a, b, c> → pair(a, pair(b, c)) → back to Pair([a, b, c]).
        let triple = p::Term::Pair(vec![
            parser_var("a", 0, p::SortHint::Msg),
            parser_var("b", 0, p::SortHint::Msg),
            parser_var("c", 0, p::SortHint::Msg),
        ]);
        let lt = term_to_lnterm(&triple).unwrap();
        let back = lnterm_to_term(&lt);
        assert_eq!(back, triple);
    }

    #[test]
    fn lnterm_to_term_round_trip_nested_app() {
        // f(g(x), y) → ... → f(g(x), y).
        let inner = p::Term::App("g".into(), vec![parser_var("x", 0, p::SortHint::Msg)]);
        let outer = p::Term::App("f".into(), vec![
            inner.clone(),
            parser_var("y", 0, p::SortHint::Msg),
        ]);
        let lt = term_to_lnterm(&outer).unwrap();
        let back = lnterm_to_term(&lt);
        assert_eq!(back, outer);
    }

    // =========================================================================
    // Rule let-block desugaring
    // =========================================================================
    //
    // Haskell tamarin desugars `rule R: let x = t in body` by substituting
    // `t` for occurrences of `x` in the body before any further analysis.
    // These tests pin our `apply_let_block` to the same semantics.

    #[test]
    fn let_block_substitutes_in_premises() {
        // rule R: let r = ~k in [In(r)] --[]-> []
        // After desugaring: [In(~k)] --[]-> []
        let src = r#"theory T begin
            rule R: let r = ~k in [In(r), Fr(~k)] --[]-> []
        end"#;
        let p = parse_theory(src, &[]).unwrap();
        let r = match &p.items[0] {
            p::TheoryItem::Rule(r) => r, _ => unreachable!(),
        };
        let desugared = apply_let_block(r);
        assert!(desugared.let_block.is_empty());
        // Premise In should now hold ~k (Var with sort Fresh), not local `r`.
        let in_fact = &desugared.premises[0];
        assert_eq!(in_fact.name, "In");
        match &in_fact.args[0] {
            p::Term::Var(vs) if vs.name == "k" && vs.sort == p::SortHint::Fresh => {}
            other => panic!("expected ~k after subst, got {:?}", other),
        }
    }

    #[test]
    fn let_block_sequential_bindings() {
        // let a = ~k; b = h(a) in [In(b)] --[]-> []
        // After desugaring: [In(h(~k))]
        let src = r#"theory T begin
            rule R: let a = ~k b = h(a) in [In(b), Fr(~k)] --[]-> []
        end"#;
        let p = parse_theory(src, &[]).unwrap();
        let r = match &p.items[0] {
            p::TheoryItem::Rule(r) => r, _ => unreachable!(),
        };
        let desugared = apply_let_block(r);
        let in_fact = &desugared.premises[0];
        match &in_fact.args[0] {
            p::Term::App(name, args) if name == "h" => match &args[0] {
                p::Term::Var(vs) if vs.name == "k" && vs.sort == p::SortHint::Fresh => {}
                other => panic!("expected h(~k), got h({:?})", other),
            },
            other => panic!("expected h(~k), got {:?}", other),
        }
    }

    #[test]
    fn let_block_substitutes_in_actions_and_conclusions() {
        let src = r#"theory T begin
            rule R: let r = ~k in [Fr(~k)] --[Use(r)]-> [Out(r)]
        end"#;
        let p = parse_theory(src, &[]).unwrap();
        let r = match &p.items[0] {
            p::TheoryItem::Rule(r) => r, _ => unreachable!(),
        };
        let desugared = apply_let_block(r);
        let use_act = &desugared.actions[0];
        match &use_act.args[0] {
            p::Term::Var(vs) if vs.name == "k" && vs.sort == p::SortHint::Fresh => {}
            other => panic!("expected Use(~k), got Use({:?})", other),
        }
        let out_conc = &desugared.conclusions[0];
        match &out_conc.args[0] {
            p::Term::Var(vs) if vs.name == "k" && vs.sort == p::SortHint::Fresh => {}
            other => panic!("expected Out(~k), got Out({:?})", other),
        }
    }

    #[test]
    fn let_block_end_to_end_elaborates() {
        // The desugared rule should elaborate cleanly through `elaborate`.
        let src = r#"theory T begin
            rule R: let r = ~k in [Fr(~k)] --[Use(r)]-> [Out(r)]
            lemma trivial: "All k #i. Use(k) @ i ==> Use(k) @ i"
        end"#;
        let p = parse_theory(src, &[]).unwrap();
        let t = elaborate(&p).unwrap();
        let rules: Vec<_> = t.rules().collect();
        assert_eq!(rules.len(), 1);
    }
}

