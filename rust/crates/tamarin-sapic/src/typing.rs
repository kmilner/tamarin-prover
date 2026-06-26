//! Port of `Sapic.Typing` (`lib/sapic/src/Sapic/Typing.hs`) — the
//! uniqueness-renaming pass (`renameUnique`) and the lightweight type
//! inference (`typeProcess` / `typeWith`) over SAPIC processes.
//!
//! HS pipeline (`typeTheoryEnv`, Typing.hs:201-223):
//!   for each top-level process:  `renameUnique` then `typeProcess`.
//! We mirror that in [`type_and_rename_process`], driven by [`type_theory`].

use std::collections::BTreeMap;

use tamarin_term::function_symbols::{FunSym, NoEqSym};
use tamarin_term::lterm::{LSort, LVar, Name};
use tamarin_term::term::{f_app_ac, f_app_c, f_app_list, f_app_no_eq};
use tamarin_term::vterm::{Lit, VTerm};
use tamarin_utils::fresh::PreciseFreshState;

use tamarin_theory::sapic::{
    Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm, SapicType,
};
use tamarin_theory::sapic::PlainProcess;

use crate::bindings::{bindings_act, bindings_comb};

// =============================================================================
// renameUnique (Typing.hs:232-269)
// =============================================================================

/// `varsProc`: every SAPIC variable that occurs anywhere in `p` (HS
/// `varsProc = foldMap Data.Set.singleton`, Process.hs:361 — a Set, so sorted
/// + deduplicated).  We return the underlying `LVar`s used to seed the
/// avoidance state for `renameUnique`.
fn proc_lvars(p: &PlainProcess) -> Vec<LVar> {
    let mut set = std::collections::BTreeSet::new();
    collect_proc_vars(p, &mut set);
    // `avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar)` — strip types.
    set.into_iter().map(|sv| sv.var).collect()
}

fn collect_proc_vars(p: &PlainProcess, out: &mut std::collections::BTreeSet<SapicLVar>) {
    match p {
        Process::Null(_) => {}
        Process::Action(a, _, body) => {
            collect_action_vars(a, out);
            collect_proc_vars(body, out);
        }
        Process::Comb(c, _, l, r) => {
            collect_comb_vars(c, out);
            collect_proc_vars(l, out);
            collect_proc_vars(r, out);
        }
    }
}

fn collect_term_vars(t: &SapicTerm, out: &mut std::collections::BTreeSet<SapicLVar>) {
    for v in tamarin_term::vterm::vars_vterm(t) {
        out.insert(v);
    }
}

fn collect_fact_vars(
    f: &tamarin_theory::sapic::SapicLNFact,
    out: &mut std::collections::BTreeSet<SapicLVar>,
) {
    for t in &f.terms {
        collect_term_vars(t, out);
    }
}

fn collect_action_vars(a: &SapicAction<SapicLVar>, out: &mut std::collections::BTreeSet<SapicLVar>) {
    match a {
        SapicAction::New(v) => {
            out.insert(v.clone());
        }
        SapicAction::Event(f) => collect_fact_vars(f, out),
        SapicAction::ChOut { chan, msg } => {
            if let Some(c) = chan {
                collect_term_vars(c, out);
            }
            collect_term_vars(msg, out);
        }
        SapicAction::ChIn { chan, msg, match_vars } => {
            if let Some(c) = chan {
                collect_term_vars(c, out);
            }
            collect_term_vars(msg, out);
            for v in match_vars {
                out.insert(v.clone());
            }
        }
        SapicAction::Insert(a, b) => {
            collect_term_vars(a, out);
            collect_term_vars(b, out);
        }
        SapicAction::Delete(t) | SapicAction::Lock(t) | SapicAction::Unlock(t) => {
            collect_term_vars(t, out)
        }
        SapicAction::ProcessCall(_, ts) => {
            for t in ts {
                collect_term_vars(t, out);
            }
        }
        SapicAction::Msr { prems, acts, concs, .. } => {
            for f in prems.iter().chain(acts).chain(concs) {
                collect_fact_vars(f, out);
            }
        }
        SapicAction::Rep => {}
    }
}

fn collect_comb_vars(c: &ProcessCombinator<SapicLVar>, out: &mut std::collections::BTreeSet<SapicLVar>) {
    match c {
        ProcessCombinator::Lookup(t, v) => {
            collect_term_vars(t, out);
            out.insert(v.clone());
        }
        ProcessCombinator::Let { left, right, match_vars } => {
            collect_term_vars(left, out);
            collect_term_vars(right, out);
            for v in match_vars {
                out.insert(v.clone());
            }
        }
        ProcessCombinator::CondEq(a, b) => {
            collect_term_vars(a, out);
            collect_term_vars(b, out);
        }
        // HS `varsProc = foldMap singleton` over the derived `Foldable (Process)`
        // folds the `v` occurrences inside `Cond (SapicNFormula v)` too — i.e.
        // the formula's FREE variables (bound `BVar` quantifier vars are not
        // `v`).  Collect them so they seed the `renameUnique` avoidance set.
        ProcessCombinator::Cond(f) => {
            for lv in cond_formula_free_lvars(f) {
                out.insert(SapicLVar::untyped(lv));
            }
        }
        ProcessCombinator::Parallel | ProcessCombinator::Ndc => {}
    }
}

/// Parser `SortHint` → `LSort` (mirrors elaborate.rs `sort_of`).
fn sort_of_hint(s: &tamarin_parser::ast::SortHint) -> LSort {
    use tamarin_parser::ast as p;
    match s {
        p::SortHint::Fresh | p::SortHint::Suffix(p::SuffixSort::Fresh) => LSort::Fresh,
        p::SortHint::Pub | p::SortHint::Suffix(p::SuffixSort::Pub) => LSort::Pub,
        p::SortHint::Node | p::SortHint::Suffix(p::SuffixSort::Node) => LSort::Node,
        p::SortHint::Nat | p::SortHint::Suffix(p::SuffixSort::Nat) => LSort::Nat,
        p::SortHint::Msg | p::SortHint::Suffix(p::SuffixSort::Msg) | p::SortHint::Untagged => {
            LSort::Msg
        }
    }
}

/// Free `LVar`s of a `Cond` parser-AST formula (vars not bound by an enclosing
/// quantifier).  Used to seed the `renameUnique` avoidance set and as the
/// rename domain.
fn cond_formula_free_lvars(f: &tamarin_parser::ast::Formula) -> Vec<LVar> {
    use tamarin_parser::ast as p;
    fn collect_term(t: &p::Term, bound: &[String], out: &mut Vec<LVar>) {
        match t {
            p::Term::Var(v) => {
                if !bound.iter().any(|n| n == &v.name) {
                    out.push(LVar::new(v.name.clone(), sort_of_hint(&v.sort), v.idx));
                }
            }
            p::Term::App(_, args) | p::Term::Pair(args) => {
                for a in args {
                    collect_term(a, bound, out);
                }
            }
            p::Term::AlgApp(_, a, b) | p::Term::Diff(a, b) | p::Term::BinOp(_, a, b) => {
                collect_term(a, bound, out);
                collect_term(b, bound, out);
            }
            p::Term::PatMatch(inner) => collect_term(inner, bound, out),
            _ => {}
        }
    }
    fn collect_atom(a: &p::Atom, bound: &[String], out: &mut Vec<LVar>) {
        use p::Atom::*;
        match a {
            Eq(l, r) | Less(l, r) | LessMset(l, r) | Subterm(l, r) => {
                collect_term(l, bound, out);
                collect_term(r, bound, out);
            }
            Action(fa, t) => {
                for arg in &fa.args {
                    collect_term(arg, bound, out);
                }
                collect_term(t, bound, out);
            }
            Last(t) => collect_term(t, bound, out),
            Pred(fa) => {
                for arg in &fa.args {
                    collect_term(arg, bound, out);
                }
            }
        }
    }
    fn collect(f: &p::Formula, bound: &mut Vec<String>, out: &mut Vec<LVar>) {
        use p::Formula::*;
        match f {
            True | False => {}
            Atom(a) => collect_atom(a, bound, out),
            Not(g) => collect(g, bound, out),
            And(a, b) | Or(a, b) | Implies(a, b) | Iff(a, b) => {
                collect(a, bound, out);
                collect(b, bound, out);
            }
            Forall(vs, body) | Exists(vs, body) => {
                let saved = bound.len();
                for v in vs {
                    bound.push(v.name.clone());
                }
                collect(body, bound, out);
                bound.truncate(saved);
            }
        }
    }
    let mut out = Vec::new();
    let mut bound = Vec::new();
    collect(f, &mut bound, &mut out);
    out
}

/// Rename the FREE variables of a `Cond` parser-AST formula according to `subst`
/// (`LVar → LVar`), mirroring HS `mapTermsComb (apply subst) ... (Cond fa) =
/// Cond (apply subst fa)` (Process.hs:165).  Quantifier-bound vars are left
/// untouched (they are not in the subst domain — process renaming only renames
/// process-bound variables).
fn rename_cond_formula(
    subst: &BTreeMap<LVar, LVar>,
    f: &tamarin_parser::ast::Formula,
) -> tamarin_parser::ast::Formula {
    use tamarin_parser::ast as p;
    fn rt(subst: &BTreeMap<LVar, LVar>, bound: &[String], t: &p::Term) -> p::Term {
        match t {
            p::Term::Var(v) => {
                if bound.iter().any(|n| n == &v.name) {
                    return t.clone();
                }
                let key = LVar::new(v.name.clone(), sort_of_hint(&v.sort), v.idx);
                match subst.get(&key) {
                    Some(nv) => p::Term::Var(p::VarSpec {
                        name: nv.name.to_string(),
                        idx: nv.idx,
                        sort: v.sort,
                        typ: v.typ.clone(),
                    }),
                    None => t.clone(),
                }
            }
            p::Term::App(n, args) => {
                p::Term::App(n.clone(), args.iter().map(|a| rt(subst, bound, a)).collect())
            }
            p::Term::Pair(items) => {
                p::Term::Pair(items.iter().map(|a| rt(subst, bound, a)).collect())
            }
            p::Term::AlgApp(n, a, b) => p::Term::AlgApp(
                n.clone(),
                Box::new(rt(subst, bound, a)),
                Box::new(rt(subst, bound, b)),
            ),
            p::Term::Diff(a, b) => {
                p::Term::Diff(Box::new(rt(subst, bound, a)), Box::new(rt(subst, bound, b)))
            }
            p::Term::BinOp(op, a, b) => {
                p::Term::BinOp(*op, Box::new(rt(subst, bound, a)), Box::new(rt(subst, bound, b)))
            }
            p::Term::PatMatch(inner) => p::Term::PatMatch(Box::new(rt(subst, bound, inner))),
            other => other.clone(),
        }
    }
    fn ra(subst: &BTreeMap<LVar, LVar>, bound: &[String], a: &p::Atom) -> p::Atom {
        use p::Atom::*;
        match a {
            Eq(l, r) => Eq(rt(subst, bound, l), rt(subst, bound, r)),
            Less(l, r) => Less(rt(subst, bound, l), rt(subst, bound, r)),
            LessMset(l, r) => LessMset(rt(subst, bound, l), rt(subst, bound, r)),
            Subterm(l, r) => Subterm(rt(subst, bound, l), rt(subst, bound, r)),
            Action(fa, t) => Action(
                p::Fact {
                    persistent: fa.persistent,
                    name: fa.name.clone(),
                    args: fa.args.iter().map(|x| rt(subst, bound, x)).collect(),
                    annotations: fa.annotations.clone(),
                },
                rt(subst, bound, t),
            ),
            Last(t) => Last(rt(subst, bound, t)),
            Pred(fa) => Pred(p::Fact {
                persistent: fa.persistent,
                name: fa.name.clone(),
                args: fa.args.iter().map(|x| rt(subst, bound, x)).collect(),
                annotations: fa.annotations.clone(),
            }),
        }
    }
    fn rf(subst: &BTreeMap<LVar, LVar>, bound: &mut Vec<String>, f: &p::Formula) -> p::Formula {
        use p::Formula::*;
        match f {
            True => True,
            False => False,
            Atom(a) => Atom(ra(subst, bound, a)),
            Not(g) => Not(Box::new(rf(subst, bound, g))),
            And(a, b) => And(Box::new(rf(subst, bound, a)), Box::new(rf(subst, bound, b))),
            Or(a, b) => Or(Box::new(rf(subst, bound, a)), Box::new(rf(subst, bound, b))),
            Implies(a, b) => {
                Implies(Box::new(rf(subst, bound, a)), Box::new(rf(subst, bound, b)))
            }
            Iff(a, b) => Iff(Box::new(rf(subst, bound, a)), Box::new(rf(subst, bound, b))),
            Forall(vs, body) => {
                let saved = bound.len();
                for v in vs {
                    bound.push(v.name.clone());
                }
                let r = Forall(vs.clone(), Box::new(rf(subst, bound, body)));
                bound.truncate(saved);
                r
            }
            Exists(vs, body) => {
                let saved = bound.len();
                for v in vs {
                    bound.push(v.name.clone());
                }
                let r = Exists(vs.clone(), Box::new(rf(subst, bound, body)));
                bound.truncate(saved);
                r
            }
        }
    }
    let mut bound = Vec::new();
    rf(subst, &mut bound, f)
}

/// Rename a SAPIC term's variables according to `subst` (`LVar -> LVar`),
/// preserving each variable's SAPIC type.  HS `renameUnique'` uses
/// `apply subst`, where `subst` only ever maps to `varTerm v'` (a renaming),
/// so a structural LVar→LVar rewrite is faithful.
fn rename_term(subst: &BTreeMap<LVar, LVar>, t: &SapicTerm) -> SapicTerm {
    match t {
        VTerm::Lit(Lit::Var(sv)) => {
            let new_lv = subst.get(&sv.var).cloned().unwrap_or_else(|| sv.var.clone());
            VTerm::Lit(Lit::Var(SapicLVar::new(new_lv, sv.stype.clone())))
        }
        VTerm::Lit(Lit::Con(c)) => VTerm::Lit(Lit::Con(c.clone())),
        VTerm::App(sym, args) => {
            let new_args: Vec<SapicTerm> = args.iter().map(|a| rename_term(subst, a)).collect();
            // Rebuild through the smart constructor so AC normal form is kept.
            rebuild_app(sym, new_args)
        }
    }
}

/// Rebuild an `App` node through the AC-preserving smart constructors, mirroring
/// `apply_vterm_map_changed`'s reconstruction (subst.rs).
fn rebuild_app(sym: &FunSym, args: Vec<SapicTerm>) -> SapicTerm {
    match sym {
        FunSym::Ac(o) => f_app_ac(*o, args),
        FunSym::C(o) => f_app_c(*o, args),
        FunSym::NoEq(o) => f_app_no_eq(o.clone(), args),
        FunSym::List => f_app_list(args),
    }
}

fn rename_sv(subst: &BTreeMap<LVar, LVar>, sv: &SapicLVar) -> SapicLVar {
    let new_lv = subst.get(&sv.var).cloned().unwrap_or_else(|| sv.var.clone());
    SapicLVar::new(new_lv, sv.stype.clone())
}

fn rename_fact(
    subst: &BTreeMap<LVar, LVar>,
    f: &tamarin_theory::sapic::SapicLNFact,
) -> tamarin_theory::sapic::SapicLNFact {
    let terms = f.terms.iter().map(|t| rename_term(subst, t)).collect();
    let mut nf = tamarin_theory::fact::Fact::new(f.tag.clone(), terms);
    nf = nf.with_annotations(f.annotations.clone());
    nf
}

fn rename_action(subst: &BTreeMap<LVar, LVar>, a: &SapicAction<SapicLVar>) -> SapicAction<SapicLVar> {
    match a {
        SapicAction::New(v) => SapicAction::New(rename_sv(subst, v)),
        SapicAction::Event(f) => SapicAction::Event(rename_fact(subst, f)),
        SapicAction::ChOut { chan, msg } => SapicAction::ChOut {
            chan: chan.as_ref().map(|t| rename_term(subst, t)),
            msg: rename_term(subst, msg),
        },
        SapicAction::ChIn { chan, msg, match_vars } => SapicAction::ChIn {
            chan: chan.as_ref().map(|t| rename_term(subst, t)),
            msg: rename_term(subst, msg),
            match_vars: match_vars.iter().map(|v| rename_sv(subst, v)).collect(),
        },
        SapicAction::Insert(a, b) => {
            SapicAction::Insert(rename_term(subst, a), rename_term(subst, b))
        }
        SapicAction::Delete(t) => SapicAction::Delete(rename_term(subst, t)),
        SapicAction::Lock(t) => SapicAction::Lock(rename_term(subst, t)),
        SapicAction::Unlock(t) => SapicAction::Unlock(rename_term(subst, t)),
        SapicAction::ProcessCall(n, ts) => {
            SapicAction::ProcessCall(n.clone(), ts.iter().map(|t| rename_term(subst, t)).collect())
        }
        SapicAction::Msr { prems, acts, concs, rest, match_vars } => SapicAction::Msr {
            prems: prems.iter().map(|f| rename_fact(subst, f)).collect(),
            acts: acts.iter().map(|f| rename_fact(subst, f)).collect(),
            concs: concs.iter().map(|f| rename_fact(subst, f)).collect(),
            rest: rest.clone(),
            match_vars: match_vars.iter().map(|v| rename_sv(subst, v)).collect(),
        },
        SapicAction::Rep => SapicAction::Rep,
    }
}

fn rename_comb(
    subst: &BTreeMap<LVar, LVar>,
    c: &ProcessCombinator<SapicLVar>,
) -> ProcessCombinator<SapicLVar> {
    match c {
        ProcessCombinator::Lookup(t, v) => {
            ProcessCombinator::Lookup(rename_term(subst, t), rename_sv(subst, v))
        }
        ProcessCombinator::Let { left, right, match_vars } => ProcessCombinator::Let {
            left: rename_term(subst, left),
            right: rename_term(subst, right),
            match_vars: match_vars.iter().map(|v| rename_sv(subst, v)).collect(),
        },
        ProcessCombinator::CondEq(a, b) => {
            ProcessCombinator::CondEq(rename_term(subst, a), rename_term(subst, b))
        }
        // HS `mapTermsComb (apply subst) ... (Cond fa) = Cond (apply subst fa)`
        // (Process.hs:165): rename the formula's free variables.
        ProcessCombinator::Cond(f) => ProcessCombinator::Cond(rename_cond_formula(subst, f)),
        other => other.clone(),
    }
}

/// `renameUnique'` (Typing.hs:239-261).  `subst` is the *outstanding* renaming
/// applied at this node (`apply initSubst p`); `fresh` mints fresh indices.
/// For each binder we (1) mint a fresh copy of every bound variable, (2) record
/// the inverse renaming in the node's `back_substitution` annotation, and
/// (3) descend with the extended substitution.
fn rename_unique_go(
    fresh: &mut PreciseFreshState,
    subst: &BTreeMap<LVar, LVar>,
    p: &PlainProcess,
) -> PlainProcess {
    // `let p' = apply initSubst p` — apply the outstanding renaming to the
    // WHOLE subtree (HS Typing.hs:243); the children inherit the rename, then
    // are descended into with only the NEW fresh subst for this node's binders.
    let p_prime = rename_process_full(subst, p);
    match p_prime {
        Process::Null(ann) => Process::Null(ann),
        Process::Action(ac, ann, body) => {
            let bvars = bindings_act(&ac);
            let (new_subst, inv) = mk_subst(fresh, &bvars);
            let mut ann2 = ann;
            ann2.back_substitution = ann2.back_substitution.compose(&inv);
            let ac1 = rename_action(&new_subst, &ac);
            let body1 = rename_unique_go(fresh, &new_subst, &body);
            Process::Action(ac1, ann2, Box::new(body1))
        }
        Process::Comb(c, ann, l, r) => {
            let bvars = bindings_comb(&c);
            let (new_subst, inv) = mk_subst(fresh, &bvars);
            let mut ann2 = ann;
            ann2.back_substitution = ann2.back_substitution.compose(&inv);
            let c1 = rename_comb(&new_subst, &c);
            let l1 = rename_unique_go(fresh, &new_subst, &l);
            let r1 = rename_unique_go(fresh, &new_subst, &r);
            Process::Comb(c1, ann2, Box::new(l1), Box::new(r1))
        }
    }
}

/// `apply subst p` over an entire process subtree (terms + bound vars), used to
/// mirror HS's `apply initSubst p` (Typing.hs:243).  Annotations are untouched
/// here — `renameUnique_go` updates `back_substitution` per node afterwards.
fn rename_process_full(subst: &BTreeMap<LVar, LVar>, p: &PlainProcess) -> PlainProcess {
    match p {
        Process::Null(ann) => Process::Null(ann.clone()),
        Process::Action(ac, ann, body) => Process::Action(
            rename_action(subst, ac),
            ann.clone(),
            Box::new(rename_process_full(subst, body)),
        ),
        Process::Comb(c, ann, l, r) => Process::Comb(
            rename_comb(subst, c),
            ann.clone(),
            Box::new(rename_process_full(subst, l)),
            Box::new(rename_process_full(subst, r)),
        ),
    }
}

/// `mkSubst` (Typing.hs:267-269): for each bound variable mint a fresh LVar
/// copy (`freshLVar name sort`), returning the forward renaming `(v -> v')`
/// and the inverse `(v' -> v)` as a `Subst Name LVar` for back-substitution.
fn mk_subst(
    fresh: &mut PreciseFreshState,
    bvars: &[SapicLVar],
) -> (BTreeMap<LVar, LVar>, tamarin_term::subst::Subst<Name, LVar>) {
    let mut fwd: BTreeMap<LVar, LVar> = BTreeMap::new();
    let mut inv_pairs: Vec<(LVar, VTerm<Name, LVar>)> = Vec::new();
    for sv in bvars {
        let lv = &sv.var;
        let v_new = tamarin_term::lterm::fresh_lvar(fresh, &lv.name, lv.sort);
        fwd.insert(lv.clone(), v_new.clone());
        inv_pairs.push((v_new, VTerm::Lit(Lit::Var(lv.clone()))));
    }
    let inv = tamarin_term::subst::Subst::from_list(inv_pairs);
    (fwd, inv)
}

/// `renameUnique` (Typing.hs:232-237): seed the fresh-var supply so it avoids
/// every variable already present, then run `renameUnique'` from the identity
/// substitution.
pub fn rename_unique(p: &PlainProcess) -> PlainProcess {
    let avoid: Vec<(String, u64)> =
        proc_lvars(p).into_iter().map(|lv| (lv.name.to_string(), lv.idx)).collect();
    let mut fresh = PreciseFreshState::avoid_precise(avoid);
    let empty: BTreeMap<LVar, LVar> = BTreeMap::new();
    rename_unique_go(&mut fresh, &empty, p)
}

// =============================================================================
// Type inference (typeProcess / typeWith, Typing.hs:73-200)
// =============================================================================

/// `TypingEnvironment` (Typing.hs:56-60).  We only need `vars` and `funs`.
pub struct TypingEnvironment {
    pub vars: BTreeMap<LVar, SapicType>,
    pub funs: BTreeMap<NoEqSym, (Vec<SapicType>, SapicType)>,
}

/// `smallerType` (Typing.hs:32-35).
fn smaller_type(t1: &SapicType, t2: &SapicType) -> bool {
    match (t1, t2) {
        (_, None) => true,
        (Some(a), Some(b)) => a == b,
        (None, Some(_)) => false,
    }
}

/// `sqcap` (Typing.hs:46-51): more specific of two types, error if they clash.
fn sqcap(t1: &SapicType, t2: &SapicType) -> Result<SapicType, String> {
    if smaller_type(t1, t2) {
        Ok(t1.clone())
    } else if smaller_type(t2, t1) {
        Ok(t2.clone())
    } else {
        Err(format!("Cannot merge types {t1:?} and {t2:?}."))
    }
}

/// `defaultFunctionType n = (replicate n Nothing, Nothing)` (Typing.hs:53).
fn default_function_type(n: usize) -> (Vec<SapicType>, SapicType) {
    (vec![None; n], None)
}

/// True iff `fs` is a `viewTerm2`-SPECIAL NoEq symbol (Term/Raw.hs:183-196):
/// `pair`, `exp`, `pmult`, `diff`, `inv`, `one`, `natOne`, `dhNeutral`.  HS's
/// `viewTerm2` renders these as dedicated constructors (`FPair`/`FExp`/…) rather
/// than `FAppNoEq`, so `typeWith` treats them via the polymorphic `viewTerm`
/// branch (no function-type learning / no argument back-propagation).
fn is_special_viewterm2_sym(fs: &NoEqSym) -> bool {
    use tamarin_term::function_symbols::{
        DH_NEUTRAL_SYM_STRING, DIFF_SYM_STRING, EXP_SYM_STRING, INV_SYM_STRING, NAT_ONE_SYM_STRING,
        ONE_SYM_STRING, PMULT_SYM_STRING,
    };
    let n = &fs.name[..];
    (n == b"pair" && fs.arity == 2)
        || (n == EXP_SYM_STRING && fs.arity == 2)
        || (n == PMULT_SYM_STRING && fs.arity == 2)
        || (n == DIFF_SYM_STRING && fs.arity == 2)
        || (n == INV_SYM_STRING && fs.arity == 1)
        || (n == ONE_SYM_STRING && fs.arity == 0)
        || (n == NAT_ONE_SYM_STRING && fs.arity == 0)
        || (n == DH_NEUTRAL_SYM_STRING && fs.arity == 0)
}

/// `typeWith` (Typing.hs:73-114).  Types term `t` against target `tt`,
/// returning the typed term and its inferred type, updating `env`.
fn type_with(
    env: &mut TypingEnvironment,
    t: &SapicTerm,
    tt: &SapicType,
) -> Result<(SapicTerm, SapicType), String> {
    match t {
        VTerm::Lit(Lit::Var(v)) => {
            let lvar = &v.var;
            // CASE: variable.
            let stype = if lvar.sort == LSort::Pub {
                None
            } else {
                match env.vars.get(lvar) {
                    None => return Err(format!("unbound variable {lvar:?}")),
                    Some(ty) => ty.clone(),
                }
            };
            let merged = sqcap(&stype, tt)?;
            env.vars.insert(lvar.clone(), merged.clone());
            Ok((
                VTerm::Lit(Lit::Var(SapicLVar::new(lvar.clone(), merged.clone()))),
                merged,
            ))
        }
        VTerm::App(sym, args) => {
            use tamarin_term::function_symbols::FunSym;
            match sym {
                // HS `typeWith` dispatches on `viewTerm2 t`: a NoEq application
                // whose head is one of the SPECIAL symbols (`pair`, `exp`, `inv`,
                // `pmult`, `diff`, `one`, `natOne`, `dhNeutral`) does NOT view as
                // `FAppNoEq` (Term/Raw.hs:183-196) — it views as its own
                // constructor (`FPair`, `FExp`, …).  None of those match the
                // `FAppNoEq fs ts` case (Typing.hs:83), so they fall through to
                // the polymorphic `FApp fs ts <- viewTerm t` branch (Typing.hs:102)
                // which types arguments with `Nothing` and learns NO function
                // type.  Crucially this means pairs (`<a,b>`) do NOT back-propagate
                // an argument type onto `a`/`b` — matching HS, which keeps
                // tuple-component variables untyped.
                FunSym::NoEq(fs) if !is_special_viewterm2_sym(fs) => {
                    let n = fs.arity;
                    // First pass: refine output type from target.
                    let (intypes1, outtype1) = get_fun(env, n, fs);
                    let mintype1 = sqcap(&outtype1, tt)?;
                    insert_fun(env, fs, (intypes1.clone(), mintype1))?;
                    // Type args (discard results, just to learn input types).
                    let ts: Vec<SapicTerm> = args.to_vec();
                    let mut ptypes: Vec<SapicType> = Vec::with_capacity(ts.len());
                    for (a, want) in ts.iter().zip(intypes1.iter()) {
                        let (_, ty) = type_with(env, a, want)?;
                        ptypes.push(ty);
                    }
                    // Recompute output type, having learnt arg types.
                    let (intypes2, outtype2) = get_fun(env, n, fs);
                    let mintype2 = sqcap(&outtype2, tt)?;
                    insert_fun(env, fs, (ptypes, mintype2))?;
                    // Type args for real.
                    let mut ts_new: Vec<SapicTerm> = Vec::with_capacity(ts.len());
                    let mut ptypes2: Vec<SapicType> = Vec::with_capacity(ts.len());
                    for (a, want) in ts.iter().zip(intypes2.iter()) {
                        let (a_new, ty) = type_with(env, a, want)?;
                        ts_new.push(a_new);
                        ptypes2.push(ty);
                    }
                    insert_fun(env, fs, (ptypes2, outtype2.clone()))?;
                    Ok((
                        rebuild_app(sym, ts_new),
                        outtype2,
                    ))
                }
                // list / AC / C symbol: polymorphic, type args with Nothing.
                _ => {
                    let mut ts_new = Vec::with_capacity(args.len());
                    for a in args.iter() {
                        let (a_new, _) = type_with(env, a, &None)?;
                        ts_new.push(a_new);
                    }
                    Ok((
                        rebuild_app(sym, ts_new),
                        None,
                    ))
                }
            }
        }
        // Constant literal: never occurs as the variable/funapp cases; type Nothing.
        VTerm::Lit(Lit::Con(_)) => Ok((t.clone(), None)),
    }
}

fn get_fun(env: &TypingEnvironment, n: usize, fs: &NoEqSym) -> (Vec<SapicType>, SapicType) {
    env.funs
        .get(fs)
        .cloned()
        .unwrap_or_else(|| default_function_type(n))
}

fn insert_fun(
    env: &mut TypingEnvironment,
    fs: &NoEqSym,
    new_ty: (Vec<SapicType>, SapicType),
) -> Result<(), String> {
    match env.funs.get(fs).cloned() {
        None => {
            env.funs.insert(fs.clone(), new_ty);
            Ok(())
        }
        Some(old) => {
            let merged = merge_fun_types(&new_ty, &old)?;
            env.funs.insert(fs.clone(), merged);
            Ok(())
        }
    }
}

fn merge_fun_types(
    a: &(Vec<SapicType>, SapicType),
    b: &(Vec<SapicType>, SapicType),
) -> Result<(Vec<SapicType>, SapicType), String> {
    let mut ins = Vec::with_capacity(a.0.len());
    for (x, y) in a.0.iter().zip(b.0.iter()) {
        ins.push(sqcap(x, y)?);
    }
    let out = sqcap(&a.1, &b.1)?;
    Ok((ins, out))
}

/// `typeProcess` (Typing.hs:135-167) via `traverseProcess` (Process.hs:221-234):
///   1. `fAct`/`fComb` — insert this node's bound vars (PRE-order, on the way
///      down);
///   2. recurse into the subtree (`p''<- traverseProcess … p'`);
///   3. `gAct`/`gComb` — reconstruct THIS node's terms (`typeWith'`), POST-order,
///      i.e. AFTER the whole subtree has been typed.
///
/// The post-order step (3) is what BACK-PROPAGATES a type learned deeper in the
/// process onto an earlier term: e.g. with `f(bitstring):bitstring`, typing
/// `out(y); out(f(y))` learns `y:bitstring` from `out(f(y))` (deeper) into the
/// shared `vars` env, and the earlier `out(y)` — reconstructed afterwards — then
/// renders `out(y:bitstring)`.  A pre-order single pass would miss this.
fn type_process(env: &mut TypingEnvironment, p: &PlainProcess) -> Result<PlainProcess, String> {
    match p {
        Process::Null(ann) => Ok(Process::Null(ann.clone())),
        Process::Action(ac, ann, body) => {
            // 1. fAct: insert bound vars (with their declared types).
            for v in bindings_act(ac) {
                insert_var(env, &v)?;
            }
            // 2. recurse into the subtree FIRST (learns deeper types into `env`).
            let body1 = type_process(env, body)?;
            // 3. gAct: type the action's terms, with the now-complete `env`.
            let ac1 = type_action(env, ac)?;
            Ok(Process::Action(ac1, ann.clone(), Box::new(body1)))
        }
        Process::Comb(c, ann, l, r) => {
            // 1. fComb: insert bound vars.
            for v in bindings_comb(c) {
                insert_var(env, &v)?;
            }
            // 2. recurse into BOTH children first.
            let l1 = type_process(env, l)?;
            let r1 = type_process(env, r)?;
            // 3. gComb: type this node's terms with the completed `env`.
            let c1 = type_comb(env, c)?;
            Ok(Process::Comb(c1, ann.clone(), Box::new(l1), Box::new(r1)))
        }
    }
}

/// `insertVar` (Typing.hs:163-167).
fn insert_var(env: &mut TypingEnvironment, v: &SapicLVar) -> Result<(), String> {
    if env.vars.contains_key(&v.var) {
        return Err(format!("variable bound twice: {:?}", v.var));
    }
    env.vars.insert(v.var.clone(), v.stype.clone());
    Ok(())
}

/// `typeWithVar` (Typing.hs:159-161): a standalone bound variable is already
/// correctly typed; if untyped, give it `defaultSapicType` (= `Nothing`).
fn type_with_var(v: &SapicLVar) -> SapicLVar {
    match &v.stype {
        None => SapicLVar::new(v.var.clone(), None),
        Some(_) => v.clone(),
    }
}

/// `traverseTermsAction` (Process.hs:242-265) specialised to the typing
/// handlers `typeWith'` (terms), `typeWithVar` (standalone vars).
fn type_action(
    env: &mut TypingEnvironment,
    a: &SapicAction<SapicLVar>,
) -> Result<SapicAction<SapicLVar>, String> {
    match a {
        SapicAction::New(v) => Ok(SapicAction::New(type_with_var(v))),
        // `Event <$> traverse ft fa` (Process.hs:257): the event fact's TERMS
        // are typed via `ft = typeWith'` — NOT `typeWithFact` (which only
        // handles MSR's `rest` formulas).  This is what propagates `:lol` onto
        // the `Test( x.1 )` references.
        SapicAction::Event(f) => Ok(SapicAction::Event(type_event_fact(env, f)?)),
        SapicAction::ChOut { chan, msg } => Ok(SapicAction::ChOut {
            chan: chan.as_ref().map(|t| type_term(env, t)).transpose()?,
            msg: type_term(env, msg)?,
        }),
        SapicAction::ChIn { chan, msg, match_vars } => Ok(SapicAction::ChIn {
            chan: chan.as_ref().map(|t| type_term(env, t)).transpose()?,
            msg: type_term(env, msg)?,
            match_vars: match_vars.iter().map(type_with_var).collect(),
        }),
        SapicAction::Insert(a, b) => {
            Ok(SapicAction::Insert(type_term(env, a)?, type_term(env, b)?))
        }
        SapicAction::Delete(t) => Ok(SapicAction::Delete(type_term(env, t)?)),
        SapicAction::Lock(t) => Ok(SapicAction::Lock(type_term(env, t)?)),
        SapicAction::Unlock(t) => Ok(SapicAction::Unlock(type_term(env, t)?)),
        SapicAction::ProcessCall(n, ts) => Ok(SapicAction::ProcessCall(
            n.clone(),
            ts.iter().map(|t| type_term(env, t)).collect::<Result<_, _>>()?,
        )),
        SapicAction::Msr { prems, acts, concs, rest, match_vars } => Ok(SapicAction::Msr {
            prems: prems.iter().map(|f| type_event_fact(env, f)).collect::<Result<_, _>>()?,
            acts: acts.iter().map(|f| type_event_fact(env, f)).collect::<Result<_, _>>()?,
            concs: concs.iter().map(|f| type_event_fact(env, f)).collect::<Result<_, _>>()?,
            // `rest` formulas use `typeWithFact = return` (Typing.hs:162) — left
            // untyped, matching HS.
            rest: rest.clone(),
            match_vars: match_vars.iter().map(type_with_var).collect(),
        }),
        SapicAction::Rep => Ok(SapicAction::Rep),
    }
}

fn type_comb(
    env: &mut TypingEnvironment,
    c: &ProcessCombinator<SapicLVar>,
) -> Result<ProcessCombinator<SapicLVar>, String> {
    match c {
        ProcessCombinator::Lookup(t, v) => {
            Ok(ProcessCombinator::Lookup(type_term(env, t)?, type_with_var(v)))
        }
        ProcessCombinator::Let { left, right, match_vars } => Ok(ProcessCombinator::Let {
            left: type_term(env, left)?,
            right: type_term(env, right)?,
            match_vars: match_vars.iter().map(type_with_var).collect(),
        }),
        ProcessCombinator::CondEq(a, b) => {
            Ok(ProcessCombinator::CondEq(type_term(env, a)?, type_term(env, b)?))
        }
        other => Ok(other.clone()),
    }
}

/// `typeWith' t = fst <$> typeWith t Nothing` (Typing.hs:155).
fn type_term(env: &mut TypingEnvironment, t: &SapicTerm) -> Result<SapicTerm, String> {
    let (t1, _) = type_with(env, t, &None)?;
    Ok(t1)
}

/// Type every term of a fact via `ft = typeWith'` — this is the `traverse ft fa`
/// path used by `traverseTermsAction` for `Event` (and per-fact terms in MSR).
fn type_event_fact(
    env: &mut TypingEnvironment,
    f: &tamarin_theory::sapic::SapicLNFact,
) -> Result<tamarin_theory::sapic::SapicLNFact, String> {
    let terms: Result<Vec<_>, _> = f.terms.iter().map(|t| type_term(env, t)).collect();
    let mut nf = tamarin_theory::fact::Fact::new(f.tag.clone(), terms?);
    nf = nf.with_annotations(f.annotations.clone());
    Ok(nf)
}

// =============================================================================
// initTEFromSig + type_theory orchestration
// =============================================================================

/// A user `functions:` typing declaration — the function name, its declared
/// argument types and return type (HS `SapicFunSym = (NoEqSym, [SapicType],
/// SapicType)`, the payload of `theoryFunctionTypingInfos`).
pub type UserFunTyping = (String, Vec<SapicType>, SapicType);

/// `initTEFromSig` (Typing.hs:185-200): seed every signature function symbol
/// with its `defaultFunctionType`, THEN overlay the user-declared function
/// typings (`withUserDefinedFuns`, Typing.hs:191-192).  The user typings carry
/// the declared argument / return types (e.g. `f(bitstring):bitstring`) that
/// `typeWith` propagates onto the bound variables.
fn init_te_from_sig(
    maude_sig: &tamarin_term::maude_sig::MaudeSig,
    user_fun_typings: &[UserFunTyping],
) -> TypingEnvironment {
    let mut funs: BTreeMap<NoEqSym, (Vec<SapicType>, SapicType)> = BTreeMap::new();
    for fs in &maude_sig.st_fun_syms {
        funs.insert(fs.clone(), default_function_type(fs.arity));
    }
    // `withUserDefinedFuns`: overlay declared types onto the matching signature
    // symbol (matched by name + arity, so the BTreeMap key — the actual term
    // symbol — is preserved exactly, keeping the privacy/constructability flags
    // that the process terms carry).
    for (name, arg_types, out_type) in user_fun_typings {
        let arity = arg_types.len();
        if let Some(key) = maude_sig
            .st_fun_syms
            .iter()
            .find(|fs| &fs.name[..] == name.as_bytes() && fs.arity == arity)
        {
            funs.insert(key.clone(), (arg_types.clone(), out_type.clone()));
        }
    }
    TypingEnvironment { vars: BTreeMap::new(), funs }
}

/// `typeAndRenameProcess` (Typing.hs:209-212): renameUnique then typeProcess.
pub fn type_and_rename_process(
    maude_sig: &tamarin_term::maude_sig::MaudeSig,
    user_fun_typings: &[UserFunTyping],
    p: &PlainProcess,
) -> Result<PlainProcess, String> {
    let renamed = rename_unique(p);
    let mut env = init_te_from_sig(maude_sig, user_fun_typings);
    type_process(&mut env, &renamed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_theory::sapic::ProcessParsedAnnotation;

    fn slv(name: &str, idx: u64, ty: Option<&str>) -> SapicLVar {
        SapicLVar::new(LVar::new(name, LSort::Msg, idx), ty.map(|s| s.to_string()))
    }

    #[test]
    fn rename_unique_mints_x1_for_new_x0() {
        // new x:lol; 0  with x at index 0 → x.1
        let new = Process::Action(
            SapicAction::New(slv("x", 0, Some("lol"))),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        let r = rename_unique(&new);
        if let Process::Action(SapicAction::New(v), _, _) = r {
            assert_eq!(v.var.idx, 1);
            assert_eq!(&*v.var.name, "x");
            assert_eq!(v.stype, Some("lol".to_string()));
        } else {
            panic!("expected New action");
        }
    }
}
