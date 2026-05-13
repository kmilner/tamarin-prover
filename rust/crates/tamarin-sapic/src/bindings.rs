//! Port of `Sapic.Bindings` from `lib/sapic/src/Sapic/Bindings.hs`.
//!
//! Compute the variables bound by SAPIC process actions / combinators.

use std::collections::BTreeSet;

use tamarin_theory::sapic::{
    frees_sapic_fact, frees_sapic_term, pfold_map, GoodAnnotation, Process, ProcessCombinator,
    SapicAction, SapicLVar,
};

/// `bindings`: variables bound *precisely at this point* in `p`.
pub fn bindings<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    match p {
        Process::Null(_) => Vec::new(),
        Process::Comb(c, _, _, _) => bindings_comb(c),
        Process::Action(a, _, _) => bindings_act(a),
    }
}

/// `bindingsAct`: variables bound by an action (`new x`, `in(c, t)`, etc.).
pub fn bindings_act(a: &SapicAction<SapicLVar>) -> Vec<SapicLVar> {
    match a {
        SapicAction::New(v) => vec![v.clone()],
        SapicAction::ChIn { msg, match_vars, .. } => {
            subtract_set(frees_sapic_term(msg), match_vars)
        }
        SapicAction::Msr { prems, match_vars, .. } => {
            let mut all = Vec::new();
            for f in prems { all.extend(frees_sapic_fact(f)); }
            all.sort();
            all.dedup();
            subtract_set(all, match_vars)
        }
        _ => Vec::new(),
    }
}

/// `bindingsComb`: variables bound by a process combinator (`lookup`, `let`).
pub fn bindings_comb(c: &ProcessCombinator<SapicLVar>) -> Vec<SapicLVar> {
    match c {
        ProcessCombinator::Lookup(_, v) => vec![v.clone()],
        ProcessCombinator::Let { left, match_vars, .. } => {
            subtract_set(frees_sapic_term(left), match_vars)
        }
        _ => Vec::new(),
    }
}

/// `accBindings`: every variable bound anywhere in `p` (with duplicates).
pub fn acc_bindings<A: GoodAnnotation>(p: &Process<A, SapicLVar>) -> Vec<SapicLVar> {
    pfold_map(p, &mut |node| bindings(node))
}

fn subtract_set(xs: Vec<SapicLVar>, drop: &BTreeSet<SapicLVar>) -> Vec<SapicLVar> {
    let mut out: Vec<SapicLVar> = xs.into_iter().filter(|v| !drop.contains(v)).collect();
    out.sort();
    out.dedup();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};
    use tamarin_term::vterm::var_term;
    use tamarin_theory::sapic::{ProcessParsedAnnotation, SapicAction};

    fn slv(name: &str) -> SapicLVar {
        SapicLVar::untyped(LVar::new(name, LSort::Msg, 0))
    }

    #[test]
    fn new_binds_variable() {
        let v = slv("k");
        let act: SapicAction<SapicLVar> = SapicAction::New(v.clone());
        assert_eq!(bindings_act(&act), vec![v]);
    }

    #[test]
    fn channel_in_binds_unmatched() {
        // ChIn channel = None, msg = pair(x, y), match_vars = {x}.
        // Should bind {y}.
        use tamarin_term::builtin::pair;
        let x = slv("x");
        let y = slv("y");
        let msg = pair(var_term(x.clone()), var_term(y.clone()));
        let mut match_vars = BTreeSet::new();
        match_vars.insert(x);
        let act: SapicAction<SapicLVar> = SapicAction::ChIn {
            chan: None,
            msg,
            match_vars,
        };
        assert_eq!(bindings_act(&act), vec![y]);
    }

    #[test]
    fn null_process_binds_nothing() {
        let p: Process<ProcessParsedAnnotation, SapicLVar> =
            Process::null(ProcessParsedAnnotation::empty());
        assert!(bindings(&p).is_empty());
        assert!(acc_bindings(&p).is_empty());
    }
}
