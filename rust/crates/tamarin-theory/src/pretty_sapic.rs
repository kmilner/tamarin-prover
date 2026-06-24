//! Port of the SAPIC process pretty-printers from
//! `lib/theory/src/Theory/Sapic/{Term,Process}.hs` and
//! `lib/theory/src/Theory/Model/Fact.hs`, restricted to the *flat* (single
//! line) rendering used for the `process="..."` rule attribute and the
//! SAPIC-generated rule names.
//!
//! HS references:
//!   - `prettySapicTerm = prettyTerm (text . show)` (Term.hs:168-169), where
//!     `show :: SapicLVar` is `show v ++ ":" ++ t` for typed vars (Term.hs:108).
//!   - `prettySapicFact = prettyFact prettySapicTerm` (Term.hs:171-172); a
//!     fact renders as `Name( a, b )` with a leading/trailing space
//!     (`nestShort'`, Fact.hs:540-547).
//!   - `prettySapicAction'` (Process.hs:450-469).
//!   - `prettySapicTopLevel'` (Process.hs:514-524).
//!
//! Scope: the LINEAR subset (`New` / `Event` / `ChOut` / `ChIn` / `Null`).
//! Everything that typing2 cannot reach renders defensively (or is left to
//! later phases); the printers here are only used for SAPIC-generated output,
//! so they never affect non-process theories.

use tamarin_term::function_symbols::{AcSym, CSym, FunSym};
use tamarin_term::function_symbols::{diff_sym, exp_sym, nat_one_sym, pair_sym, EMAP_SYM_STRING};
use tamarin_term::vterm::{Lit, VTerm};

use crate::sapic::{
    PlainProcess, Process, ProcessCombinator, SapicAction, SapicLVar, SapicTerm,
};

/// `show :: SapicLVar` (Term.hs:108-110): `show lvar (++ ":" ++ type)`.
fn show_sapic_lvar(v: &SapicLVar) -> String {
    let mut s = String::new();
    tamarin_term::pretty::pp_lvar(&v.var, &mut s);
    if let Some(t) = &v.stype {
        s.push(':');
        s.push_str(t);
    }
    s
}

fn ac_op_symbol(op: AcSym) -> &'static str {
    match op {
        AcSym::Mult => "*",
        AcSym::Xor => "\u{2295}",
        AcSym::Union => "++",
        AcSym::NatPlus => "%+",
    }
}

/// `prettyTerm (text . show)` over a `SapicTerm` (Term.hs:268-298), flat.
pub fn pretty_sapic_term(t: &SapicTerm) -> String {
    let mut out = String::new();
    pp_sapic_term(t, &mut out);
    out
}

fn pp_sapic_term(t: &SapicTerm, out: &mut String) {
    match t {
        VTerm::Lit(Lit::Var(v)) => out.push_str(&show_sapic_lvar(v)),
        VTerm::Lit(Lit::Con(n)) => tamarin_term::pretty::pp_name(n, out),
        VTerm::App(FunSym::Ac(o), ts) => {
            out.push('(');
            for (i, c) in ts.iter().enumerate() {
                if i > 0 {
                    out.push_str(ac_op_symbol(*o));
                }
                pp_sapic_term(c, out);
            }
            out.push(')');
        }
        VTerm::App(FunSym::NoEq(sym), ts) if ts.len() == 2 && *sym == exp_sym() => {
            pp_sapic_term(&ts[0], out);
            out.push('^');
            pp_sapic_term(&ts[1], out);
        }
        VTerm::App(FunSym::NoEq(sym), ts) if ts.len() == 2 && *sym == diff_sym() => {
            out.push_str("diff(");
            pp_sapic_term(&ts[0], out);
            out.push_str(", ");
            pp_sapic_term(&ts[1], out);
            out.push(')');
        }
        VTerm::App(FunSym::NoEq(sym), ts) if ts.is_empty() && *sym == nat_one_sym() => {
            out.push_str("%1");
        }
        VTerm::App(FunSym::NoEq(sym), _) if *sym == pair_sym() => {
            let mut flat: Vec<&SapicTerm> = Vec::new();
            collect_pair_tail(t, &mut flat);
            out.push('<');
            for (i, c) in flat.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                pp_sapic_term(c, out);
            }
            out.push('>');
        }
        VTerm::App(FunSym::NoEq(sym), ts) => {
            out.push_str(&String::from_utf8_lossy(&sym.name));
            if !ts.is_empty() {
                out.push('(');
                for (i, c) in ts.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    pp_sapic_term(c, out);
                }
                out.push(')');
            }
        }
        VTerm::App(FunSym::C(CSym::EMap), ts) => {
            out.push_str(&String::from_utf8_lossy(EMAP_SYM_STRING));
            out.push('(');
            for (i, c) in ts.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                pp_sapic_term(c, out);
            }
            out.push(')');
        }
        VTerm::App(FunSym::List, ts) => {
            out.push_str("LIST(");
            for (i, c) in ts.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                pp_sapic_term(c, out);
            }
            out.push(')');
        }
    }
}

fn collect_pair_tail<'a>(t: &'a SapicTerm, out: &mut Vec<&'a SapicTerm>) {
    if let VTerm::App(FunSym::NoEq(sym), args) = t {
        if sym.name == b"pair" && args.len() == 2 {
            collect_pair_tail(&args[0], out);
            collect_pair_tail(&args[1], out);
            return;
        }
    }
    out.push(t);
}

/// `prettySapicFact = prettyFact prettySapicTerm` (Fact.hs:540-547).
/// A non-empty argument list renders as `Name( a, b )` — note the leading and
/// trailing space introduced by `nestShort'`'s `sep`.  An empty list renders
/// as `Name( )` (HS `nestShort'` always prints lead/finish; `sep [empty,")"]`
/// = `( )`).
fn pretty_sapic_fact(f: &crate::sapic::SapicLNFact) -> String {
    let name = crate::fact::show_fact_tag(&f.tag);
    let mut inner = String::new();
    for (i, t) in f.terms.iter().enumerate() {
        if i > 0 {
            inner.push_str(", ");
        }
        inner.push_str(&pretty_sapic_term(t));
    }
    // `nestShort' (n++"(") ")" body = sep [text (n++"(") $$ nest k body, ")"]`.
    // On one line that is `"<name>(" <space> <body> <space> ")"` for non-empty
    // body, and `"<name>(" <space> ")"` for empty body.
    if inner.is_empty() {
        format!("{name}( )")
    } else {
        format!("{name}( {inner} )")
    }
}

/// `prettySapicAction'` (Process.hs:450-469), linear subset.
fn pretty_sapic_action(a: &SapicAction<SapicLVar>) -> String {
    match a {
        SapicAction::New(v) => format!("new {}", show_sapic_lvar(v)),
        SapicAction::Rep => "!".to_string(),
        SapicAction::Event(fa) => format!("event {}", pretty_sapic_fact(fa)),
        SapicAction::ChOut { chan: None, msg } => {
            format!("out({})", pretty_sapic_term(msg))
        }
        SapicAction::ChOut { chan: Some(c), msg } => {
            format!("out({},{})", pretty_sapic_term(c), pretty_sapic_term(msg))
        }
        SapicAction::ChIn { chan: None, msg, .. } => {
            format!("in({})", pretty_sapic_term(msg))
        }
        SapicAction::ChIn { chan: Some(c), msg, .. } => {
            format!("in({},{})", pretty_sapic_term(c), pretty_sapic_term(msg))
        }
        SapicAction::Insert(a, b) => {
            format!("insert {},{}", pretty_sapic_term(a), pretty_sapic_term(b))
        }
        SapicAction::Delete(t) => format!("delete {}", pretty_sapic_term(t)),
        SapicAction::Lock(t) => format!("lock {}", pretty_sapic_term(t)),
        SapicAction::Unlock(t) => format!("unlock {}", pretty_sapic_term(t)),
        SapicAction::ProcessCall(s, ts) => {
            let inner: Vec<String> = ts.iter().map(pretty_sapic_term).collect();
            format!("{}({})", s, inner.join(", "))
        }
        SapicAction::Msr { .. } => {
            // MSR rendering inside a process is Phase 2+ (uses prettyRuleRestr).
            "/* msr */".to_string()
        }
    }
}

/// `prettySapicComb` (Process.hs:473-485), only the cases reachable here.
fn pretty_sapic_comb(c: &ProcessCombinator<SapicLVar>) -> String {
    match c {
        ProcessCombinator::Parallel => "|".to_string(),
        ProcessCombinator::Ndc => "+".to_string(),
        ProcessCombinator::CondEq(t, t2) => {
            format!("if {}={}", pretty_sapic_term(t), pretty_sapic_term(t2))
        }
        // Cond/Lookup/Let render their formulas/patterns; deferred to Phase 2+.
        _ => "/* comb */".to_string(),
    }
}

/// `prettySapicTopLevel'` (Process.hs:514-524): used for rule names and the
/// `process=` attribute.  Only inspects the TOP node.
pub fn pretty_sapic_top_level(p: &PlainProcess) -> String {
    match p {
        Process::Null(_) => "0".to_string(),
        Process::Comb(c, _, _, _) => pretty_sapic_comb(c),
        Process::Action(SapicAction::Rep, _, _) => pretty_sapic_action(&SapicAction::Rep),
        Process::Action(a, _, _) => format!("{};", pretty_sapic_action(a)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::function_symbols::{Constructability, NoEqSym, Privacy};
    use tamarin_term::term::f_app_no_eq;
    use crate::sapic::ProcessParsedAnnotation;

    fn sv(name: &str, idx: u64, ty: Option<&str>) -> SapicLVar {
        SapicLVar::new(LVar::new(name, LSort::Msg, idx), ty.map(String::from))
    }

    #[test]
    fn new_top_level() {
        let p = Process::Action(
            SapicAction::New(sv("x", 1, Some("lol"))),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        assert_eq!(pretty_sapic_top_level(&p), "new x.1:lol;");
    }

    #[test]
    fn out_ffx_top_level() {
        let f = NoEqSym::new(b"f".to_vec(), 1, Privacy::Public, Constructability::Constructor);
        let x = VTerm::Lit(Lit::Var(sv("x", 1, Some("lol"))));
        let ffx = f_app_no_eq(f.clone(), vec![f_app_no_eq(f, vec![x])]);
        let p = Process::Action(
            SapicAction::ChOut { chan: None, msg: ffx },
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        assert_eq!(pretty_sapic_top_level(&p), "out(f(f(x.1:lol)));");
    }

    #[test]
    fn event_top_level_has_spaces() {
        let x = VTerm::Lit(Lit::Var(sv("x", 1, Some("lol"))));
        let fact = crate::fact::Fact::new(
            crate::fact::FactTag::Proto(crate::fact::Multiplicity::Linear, "Test".into(), 1),
            vec![x],
        );
        let p = Process::Action(
            SapicAction::Event(fact),
            ProcessParsedAnnotation::empty(),
            Box::new(Process::Null(ProcessParsedAnnotation::empty())),
        );
        assert_eq!(pretty_sapic_top_level(&p), "event Test( x.1:lol );");
    }

    #[test]
    fn null_top_level() {
        let p: PlainProcess = Process::Null(ProcessParsedAnnotation::empty());
        assert_eq!(pretty_sapic_top_level(&p), "0");
    }
}
