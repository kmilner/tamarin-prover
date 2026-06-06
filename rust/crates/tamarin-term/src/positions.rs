//! Port of `Term.Positions` from `lib/term/src/Term/Positions.hs`.
//!
//! Positions in terms, subterm access, and replacement. AC operators with
//! n-ary applications are interpreted as right-leaning binary apps:
//! `*[t1,..,tk]` ≡ `t1 * (t2 * (… * tk))`. `0` selects the head, `1` the
//! tail multiset.

use crate::function_symbols::FunSym;
use crate::term::{f_app, Term};
use crate::vterm::{Lit, VTerm};

/// A position in a term — list of integers.
pub type Position = Vec<i64>;

/// `t @ p`: subterm of `t` at `p`. Returns `None` for invalid positions.
pub fn at_pos<C: Ord + Clone, V: Ord + Clone>(t: &VTerm<C, V>, p: &[i64]) -> Option<VTerm<C, V>> {
    if p.is_empty() { return Some(t.clone()); }
    match t {
        Term::Lit(_) => None,
        Term::App(FunSym::Ac(s), args) => match (p[0], &args[..]) {
            (_, []) => None,
            (0, [a, ..]) => at_pos(a, &p[1..]),
            (1, [_, only]) => at_pos(only, &p[1..]),
            (1, [_, rest @ ..]) if !rest.is_empty() => {
                let tail = f_app(FunSym::Ac(*s), rest.to_vec());
                at_pos(&tail, &p[1..])
            }
            _ => None,
        },
        Term::App(_, args) => {
            let i = p[0] as usize;
            if (p[0] as i64) < 0 || i >= args.len() { return None; }
            at_pos(&args[i], &p[1..])
        }
    }
}

/// `t.replace_pos(s, p)`: replace the subterm at `p` with `s`.
pub fn replace_pos<C: Ord + Clone, V: Ord + Clone>(
    t: &VTerm<C, V>,
    s: &VTerm<C, V>,
    p: &[i64],
) -> Option<VTerm<C, V>> {
    if p.is_empty() { return Some(s.clone()); }
    match t {
        Term::Lit(_) => None,
        Term::App(FunSym::Ac(sym), args) => match (p[0], &args[..]) {
            (0, [head, rest @ ..]) => {
                let new_head = replace_pos(head, s, &p[1..])?;
                let mut new_args = vec![new_head];
                new_args.extend(rest.iter().cloned());
                Some(f_app(FunSym::Ac(*sym), new_args))
            }
            (1, [head, rest @ ..]) if !rest.is_empty() => {
                let tail = f_app(FunSym::Ac(*sym), rest.to_vec());
                let new_tail = replace_pos(&tail, s, &p[1..])?;
                Some(f_app(FunSym::Ac(*sym), vec![head.clone(), new_tail]))
            }
            _ => None,
        },
        Term::App(fsym, args) => {
            let i = p[0] as usize;
            if (p[0] as i64) < 0 || i >= args.len() { return None; }
            let mut new: Vec<_> = args.iter().cloned().collect();
            new[i] = replace_pos(&args[i], s, &p[1..])?;
            Some(f_app(fsym.clone(), new))
        }
    }
}

/// `positions t`: every position in `t` (including the empty position at
/// the root). AC nesting follows the right-leaning binary interpretation.
pub fn positions<C, V>(t: &VTerm<C, V>) -> Vec<Position> {
    fn go<C, V>(t: &VTerm<C, V>, out: &mut Vec<Position>, prefix: &[i64]) {
        out.push(prefix.to_vec());
        if let Term::App(FunSym::Ac(_), args) = t {
            let len = args.len();
            for (i, a) in args.iter().enumerate() {
                let pre = ac_position(i, len);
                let mut new_prefix = prefix.to_vec();
                new_prefix.extend_from_slice(&pre);
                go(a, out, &new_prefix);
            }
        } else if let Term::App(_, args) = t {
            for (i, a) in args.iter().enumerate() {
                let mut new_prefix = prefix.to_vec();
                new_prefix.push(i as i64);
                go(a, out, &new_prefix);
            }
        }
    }
    let mut out = Vec::new();
    go(t, &mut out, &[]);
    out
}

/// `positionsNonVar`: like `positions` but excludes positions where the
/// subterm is a variable.
pub fn positions_non_var<C, V>(t: &VTerm<C, V>) -> Vec<Position> {
    fn go<C, V>(t: &VTerm<C, V>, out: &mut Vec<Position>, prefix: &[i64]) {
        match t {
            Term::Lit(Lit::Var(_)) => {}
            Term::Lit(Lit::Con(_)) => out.push(prefix.to_vec()),
            Term::App(FunSym::Ac(_), args) => {
                out.push(prefix.to_vec());
                let len = args.len();
                for (i, a) in args.iter().enumerate() {
                    let pre = ac_position(i, len);
                    let mut new_prefix = prefix.to_vec();
                    new_prefix.extend_from_slice(&pre);
                    go(a, out, &new_prefix);
                }
            }
            Term::App(_, args) => {
                out.push(prefix.to_vec());
                for (i, a) in args.iter().enumerate() {
                    let mut new_prefix = prefix.to_vec();
                    new_prefix.push(i as i64);
                    go(a, out, &new_prefix);
                }
            }
        }
    }
    let mut out = Vec::new();
    go(t, &mut out, &[]);
    out
}

fn ac_position(i: usize, len: usize) -> Vec<i64> {
    if i == len - 1 {
        vec![1; i]
    } else {
        let mut v = vec![1; i];
        v.push(0);
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtin::{msg_var, pair};
    use crate::lterm::LNTerm;

    #[test]
    fn at_pos_root() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let r = at_pos(&t, &[]).unwrap();
        assert_eq!(r, t);
    }

    #[test]
    fn at_pos_first_child() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let r = at_pos(&t, &[0]).unwrap();
        assert_eq!(r, msg_var("x", 0));
    }

    #[test]
    fn replace_pos_at_first_child() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let new = msg_var("z", 0);
        let r = replace_pos(&t, &new, &[0]).unwrap();
        assert_eq!(r, pair(msg_var("z", 0), msg_var("y", 0)));
    }

    #[test]
    fn positions_includes_root_and_each_subterm() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let ps = positions(&t);
        assert!(ps.contains(&Vec::<i64>::new()));
        assert!(ps.contains(&vec![0i64]));
        assert!(ps.contains(&vec![1i64]));
        assert_eq!(ps.len(), 3);
    }

    #[test]
    fn positions_non_var_excludes_variables() {
        let t: LNTerm = pair(msg_var("x", 0), msg_var("y", 0));
        let ps = positions_non_var(&t);
        // Only the root is non-variable.
        assert_eq!(ps, vec![Vec::<i64>::new()]);
    }
}
