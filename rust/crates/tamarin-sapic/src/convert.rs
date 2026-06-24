//! Parser-AST → theory-AST process converter (P0a).
//!
//! Maps `tamarin_parser::ast::Process` (the surface syntax tree) into
//! `tamarin_theory::sapic::PlainProcess` (the HS-faithful `Process<ann, v>`
//! working representation), for the CORE LINEAR subset of SAPIC needed by
//! `examples/sapic/fast/basic/typing2.spthy`:
//!
//!   - `Null`
//!   - `Action New / Event / ChOut / ChIn`
//!   - `Action Rep` (replication `!P`)
//!   - `Comb Parallel | NDC | CondEq` (`P|Q`, `P+Q`, `if t1 = t2 then P else Q`)
//!
//! `Cond`-with-a-formula (`if <formula> then`), state (insert/delete/lookup),
//! locks, secret/private channels, `let`, and process-calls are deferred to
//! later phases — they error out so we never silently mistranslate.
//!
//! There is no single HS function this mirrors: in HS the parser builds the
//! `PlainProcess` directly (`Theory.Text.Parser.Sapic.process`), whereas the
//! Rust parser produces its own `ast::Process` first.  The term/fact payloads
//! reuse the shared elaborators `term_to_sapic_term` / `fact_to_sapic_fact`
//! (elaborate.rs), so the term universe matches the protocol-rule path.

use std::collections::BTreeSet;

use tamarin_parser::ast as p;
use tamarin_theory::elaborate::{fact_to_sapic_fact, term_to_sapic_term};
use tamarin_theory::sapic::{
    PlainProcess, Process, ProcessCombinator, ProcessParsedAnnotation, SapicAction, SapicLVar,
};
use tamarin_term::lterm::{LSort, LVar};

/// Error returned for SAPIC constructs not yet ported (Phase 2+).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConvertError {
    pub message: String,
}

impl ConvertError {
    fn new(s: impl Into<String>) -> Self {
        ConvertError { message: s.into() }
    }
}

fn sort_of_hint(s: &p::SortHint) -> LSort {
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

/// `VarSpec` → `SapicLVar` (carrying the SAPIC `name:type` annotation).
fn varspec_to_sapic(v: &p::VarSpec) -> SapicLVar {
    SapicLVar::new(LVar::new(v.name.clone(), sort_of_hint(&v.sort), v.idx), v.typ.clone())
}

fn term(t: &p::Term) -> Result<tamarin_theory::sapic::SapicTerm, ConvertError> {
    term_to_sapic_term(t)
        .ok_or_else(|| ConvertError::new("could not convert SAPIC term (pattern term?)"))
}

fn fact(f: &p::Fact) -> Result<tamarin_theory::sapic::SapicLNFact, ConvertError> {
    fact_to_sapic_fact(f).map_err(|e| ConvertError::new(e.message))
}

/// Convert a parser action into a theory `SapicAction<SapicLVar>`.
fn action(a: &p::SapicAction) -> Result<SapicAction<SapicLVar>, ConvertError> {
    match a {
        p::SapicAction::New(v) => Ok(SapicAction::New(varspec_to_sapic(v))),
        p::SapicAction::Event(f) => Ok(SapicAction::Event(fact(f)?)),
        p::SapicAction::ChOut { chan, msg } => Ok(SapicAction::ChOut {
            chan: chan.as_ref().map(term).transpose()?,
            msg: term(msg)?,
        }),
        p::SapicAction::ChIn { chan, msg } => {
            // The surface `in(pat)` parser separates pattern (match) variables
            // from freshly-bound ones (`extractMatchingVariables`).  The Rust
            // parser does not yet carry that split, so for the linear subset
            // (typing2 has no `in`) we keep `match_vars` empty.  Phase 2 must
            // port `validPattern`/`extractMatchingVariables`.
            Ok(SapicAction::ChIn {
                chan: chan.as_ref().map(term).transpose()?,
                msg: term(msg)?,
                match_vars: BTreeSet::new(),
            })
        }
        other => Err(ConvertError::new(format!(
            "SAPIC action not yet ported (Phase 2+): {other:?}"
        ))),
    }
}

/// Convert a parser combinator into a theory `ProcessCombinator<SapicLVar>`.
///
/// Mirrors the SAPIC parser's combinator construction
/// (`Theory.Text.Parser.Sapic`): `Parallel`/`Ndc` are nullary; `if t1 = t2`
/// becomes `CondEq t1 t2`; `if frml` becomes `Cond frml`.  `Lookup`/`Let` are
/// deferred (Phase 3+ for state; `let`-with-destructors).
fn combinator(c: &p::ProcessComb) -> Result<ProcessCombinator<SapicLVar>, ConvertError> {
    match c {
        p::ProcessComb::Parallel => Ok(ProcessCombinator::Parallel),
        p::ProcessComb::Ndc => Ok(ProcessCombinator::Ndc),
        p::ProcessComb::Cond(p::Condition::Eq(t1, t2)) => {
            Ok(ProcessCombinator::CondEq(term(t1)?, term(t2)?))
        }
        p::ProcessComb::Cond(p::Condition::Formula(_)) => Err(ConvertError::new(
            "conditional with a formula (`if <formula> then`) not yet ported \
             (Phase 2+); only `if t1 = t2 then` is supported",
        )),
        p::ProcessComb::Lookup(_, _) => {
            Err(ConvertError::new("lookup not yet ported (Phase 3 — state)"))
        }
        p::ProcessComb::Let { .. } => {
            Err(ConvertError::new("let-binding not yet ported (Phase 2+)"))
        }
    }
}

/// Convert a parser process into a `PlainProcess`.  Each node carries an empty
/// [`ProcessParsedAnnotation`]; names/back-substitution are filled in by later
/// passes (`propagate_names`, `rename_unique`).
pub fn convert_process(proc: &p::Process) -> Result<PlainProcess, ConvertError> {
    let ann = ProcessParsedAnnotation::empty();
    match proc {
        p::Process::Null => Ok(Process::Null(ann)),
        p::Process::Action { action: act, body } => Ok(Process::Action(
            action(act)?,
            ann,
            Box::new(convert_process(body)?),
        )),
        p::Process::Comb { comb, left, right } => {
            let l = Box::new(convert_process(left)?);
            let r = Box::new(convert_process(right)?);
            let c = combinator(comb)?;
            Ok(Process::Comb(c, ann, l, r))
        }
        // `!P` parses to `ProcessAction Rep mempty P` in HS
        // (Theory.Text.Parser.Sapic, replication branch); mirror by emitting a
        // `Rep` action whose single child is the replicated body.
        p::Process::Replication(body) => Ok(Process::Action(
            SapicAction::Rep,
            ann,
            Box::new(convert_process(body)?),
        )),
        p::Process::Call { .. } => {
            Err(ConvertError::new("process calls not yet ported (Phase 2+)"))
        }
        p::Process::AtAnnotation(inner, _) => {
            // Location annotation (`@ loc`) — for the linear subset we drop the
            // location and descend; locations matter only for IEE / reliable
            // channels (Phase 2+).
            convert_process(inner)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn convert_new_event_out_chain() {
        // new x:lol; event Test(x); out(f(f(x)))
        let xspec = p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: Some("lol".into()),
        };
        let xref = p::Term::Var(p::VarSpec {
            name: "x".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: None,
        });
        let ffx = p::Term::App(
            "f".into(),
            vec![p::Term::App("f".into(), vec![xref.clone()])],
        );
        let inner = p::Process::Action {
            action: p::SapicAction::ChOut { chan: None, msg: ffx },
            body: Box::new(p::Process::Null),
        };
        let evt = p::Process::Action {
            action: p::SapicAction::Event(p::Fact {
                persistent: false,
                name: "Test".into(),
                args: vec![xref],
                annotations: vec![],
            }),
            body: Box::new(inner),
        };
        let top = p::Process::Action {
            action: p::SapicAction::New(xspec),
            body: Box::new(evt),
        };
        let conv = convert_process(&top).unwrap();
        // Outermost is New.
        assert!(matches!(conv, Process::Action(SapicAction::New(_), _, _)));
    }

    fn event(name: &str) -> p::Process {
        p::Process::Action {
            action: p::SapicAction::Event(p::Fact {
                persistent: false,
                name: name.into(),
                args: vec![],
                annotations: vec![],
            }),
            body: Box::new(p::Process::Null),
        }
    }

    #[test]
    fn convert_parallel_and_ndc() {
        let par = p::Process::Comb {
            comb: p::ProcessComb::Parallel,
            left: Box::new(event("A")),
            right: Box::new(event("B")),
        };
        assert!(matches!(
            convert_process(&par).unwrap(),
            Process::Comb(ProcessCombinator::Parallel, _, _, _)
        ));
        let ndc = p::Process::Comb {
            comb: p::ProcessComb::Ndc,
            left: Box::new(event("A")),
            right: Box::new(event("B")),
        };
        assert!(matches!(
            convert_process(&ndc).unwrap(),
            Process::Comb(ProcessCombinator::Ndc, _, _, _)
        ));
    }

    #[test]
    fn convert_replication_becomes_rep_action() {
        let rep = p::Process::Replication(Box::new(event("A")));
        assert!(matches!(
            convert_process(&rep).unwrap(),
            Process::Action(SapicAction::Rep, _, _)
        ));
    }

    #[test]
    fn convert_condeq() {
        let a = p::Term::Var(p::VarSpec {
            name: "a".into(),
            idx: 0,
            sort: p::SortHint::Untagged,
            typ: None,
        });
        let cond = p::Process::Comb {
            comb: p::ProcessComb::Cond(p::Condition::Eq(a.clone(), a)),
            left: Box::new(event("E")),
            right: Box::new(p::Process::Null),
        };
        assert!(matches!(
            convert_process(&cond).unwrap(),
            Process::Comb(ProcessCombinator::CondEq(_, _), _, _, _)
        ));
    }

    #[test]
    fn convert_cond_formula_errors_gracefully() {
        let cond = p::Process::Comb {
            comb: p::ProcessComb::Cond(p::Condition::Formula(p::Formula::True)),
            left: Box::new(event("E")),
            right: Box::new(p::Process::Null),
        };
        assert!(convert_process(&cond).is_err());
    }
}
