//! Port of `Term.Macro` from `lib/term/src/Term/Macro.hs`.
//!
//! A macro is a triple `(name, params, body)`. `apply_macros` recursively
//! expands every occurrence of any macro symbol in a term.

use crate::function_symbols::{Constructability, FunSym, NoEqSym, Privacy};
use crate::subst::{apply_vterm, Subst};
use crate::term::{f_app, Term};
use crate::vterm::VTerm;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Macro<C, V> {
    pub name: Vec<u8>,
    pub params: Vec<V>,
    pub body: VTerm<C, V>,
}

impl<C, V> Macro<C, V> {
    pub fn new(name: impl Into<Vec<u8>>, params: Vec<V>, body: VTerm<C, V>) -> Self {
        Macro { name: name.into(), params, body }
    }
}

/// `macroToFunSym`: synthesise a private destructor `NoEqSym` for a macro
/// of arity `params.len()`.
pub fn macro_to_fun_sym<C, V>(m: &Macro<C, V>) -> FunSym {
    FunSym::NoEq(NoEqSym::new(
        m.name.clone(),
        m.params.len(),
        Privacy::Private,
        Constructability::Destructor,
    ))
}

/// `applyMacros`: rewrite every term application whose head matches a
/// macro by substituting the body. Recursively expands macros in argument
/// positions before the rewrite.
pub fn apply_macros<C, V>(macros: &[Macro<C, V>], term: VTerm<C, V>) -> VTerm<C, V>
where
    C: Ord + Clone,
    V: Ord + Clone,
{
    match term {
        Term::Lit(l) => Term::Lit(l),
        Term::App(fsym, args) => {
            let processed: Vec<VTerm<C, V>> =
                args.iter().cloned().map(|a| apply_macros(macros, a)).collect();
            if let Some(m) = find_matching_macro(&fsym, macros) {
                let pairs = m
                    .params
                    .iter()
                    .cloned()
                    .zip(processed.into_iter())
                    .collect::<Vec<_>>();
                let s = Subst::from_list(pairs);
                let expanded = apply_vterm(&s, m.body.clone());
                apply_macros(macros, expanded)
            } else {
                f_app(fsym, processed)
            }
        }
    }
}

fn find_matching_macro<'a, C, V>(
    fsym: &FunSym,
    macros: &'a [Macro<C, V>],
) -> Option<&'a Macro<C, V>> {
    macros.iter().find(|m| &macro_to_fun_sym(m) == fsym)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lterm::LNTerm;
    use crate::vterm::var_term;
    use crate::builtin::{msg_var, pair};

    #[test]
    fn macro_to_fun_sym_arity() {
        let m: Macro<crate::lterm::Name, crate::lterm::LVar> = Macro::new(
            b"id".to_vec(),
            vec![crate::lterm::LVar::new("x", crate::lterm::LSort::Msg, 0)],
            var_term(crate::lterm::LVar::new("x", crate::lterm::LSort::Msg, 0)),
        );
        let fsym = macro_to_fun_sym(&m);
        if let FunSym::NoEq(s) = fsym {
            assert_eq!(s.arity, 1);
            assert_eq!(s.privacy, Privacy::Private);
            assert_eq!(s.constructability, Constructability::Destructor);
        } else {
            panic!();
        }
    }

    #[test]
    fn apply_macro_substitutes_body() {
        // Macro `swap(x, y) = pair(y, x)`. Apply to `swap(a, b)` →
        // `pair(b, a)`.
        let x = crate::lterm::LVar::new("x", crate::lterm::LSort::Msg, 0);
        let y = crate::lterm::LVar::new("y", crate::lterm::LSort::Msg, 0);
        let body: LNTerm = pair(var_term(y.clone()), var_term(x.clone()));
        let m = Macro::new(b"swap".to_vec(), vec![x, y], body);

        let invoke: LNTerm = crate::term::f_app_no_eq(
            macro_to_fun_sym(&m).into_no_eq(),
            vec![msg_var("a", 0), msg_var("b", 0)],
        );

        let expanded = apply_macros(std::slice::from_ref(&m), invoke);
        assert_eq!(expanded, pair(msg_var("b", 0), msg_var("a", 0)));
    }
}

// Helper for tests: extract the inner NoEqSym out of a FunSym we know is NoEq.
#[cfg(test)]
impl FunSym {
    fn into_no_eq(self) -> NoEqSym {
        match self {
            FunSym::NoEq(s) => s,
            _ => panic!("not a NoEq symbol"),
        }
    }
}
