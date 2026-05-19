//! Port of `Theory.Tools.IntruderRules` from
//! `lib/theory/src/Theory/Tools/IntruderRules.hs` — covers the
//! always-included "special" intruder rules. The DH/BP/XOR/multiset
//! variant computations need narrowing + Maude and are deferred.

use tamarin_term::lterm::{LSort, LVar};
use tamarin_term::vterm::var_term;

use crate::fact::{fresh_fact, in_fact, k_log_fact, kd_fact, ku_fact, out_fact, LNFact};
use crate::rule::{IntrRuleAC, IntrRuleACInfo, Rule};

/// `specialIntruderRules diff` returns the intruder rules that are
/// included independently of the message theory:
///
/// - `coerce` — `[ KD(x) ] --[ KU(x) ]-> [ KU(x) ]`
/// - `pub` — `[] --[ KU($x) ]-> [ KU($x) ]`
/// - `gen_fresh` — `[ Fr(~x) ] --[ KU(~x) ]-> [ KU(~x) ]`
/// - `isend` — `[ KU(x) ] --[ K(x) ]-> [ In(x) ]`
/// - `irecv` — `[ Out(x) ] --> [ KD(x) ]`
///
/// If `diff` is true the additional `iequality` rule is included:
/// `[ KU(x), KD(x) ] --> []`.
pub fn special_intruder_rules(diff: bool) -> Vec<IntrRuleAC> {
    let x = var_term(LVar::new("x", LSort::Msg, 0));
    let x_pub = var_term(LVar::new("x", LSort::Pub, 0));
    let x_fresh = var_term(LVar::new("x", LSort::Fresh, 0));

    let ku_rule = |info: IntrRuleACInfo,
                   prems: Vec<LNFact>,
                   t: tamarin_term::lterm::LNTerm,
                   nvs: Vec<tamarin_term::lterm::LNTerm>|
     -> IntrRuleAC {
        let mut r = Rule::new(info, prems, vec![ku_fact(t.clone())], vec![ku_fact(t)]);
        r.new_vars = nvs;
        r
    };

    let mut out = vec![
        ku_rule(IntrRuleACInfo::Coerce, vec![kd_fact(x.clone())], x.clone(), vec![]),
        ku_rule(IntrRuleACInfo::PubConstr, vec![], x_pub.clone(), vec![x_pub]),
        ku_rule(
            IntrRuleACInfo::FreshConstr,
            vec![fresh_fact(x_fresh.clone())],
            x_fresh,
            vec![],
        ),
        Rule::new(
            IntrRuleACInfo::ISend,
            vec![ku_fact(x.clone())],
            vec![in_fact(x.clone())],
            vec![k_log_fact(x.clone())],
        ),
        Rule::new(
            IntrRuleACInfo::IRecv,
            vec![out_fact(x.clone())],
            vec![kd_fact(x.clone())],
            vec![],
        ),
    ];

    if diff {
        out.push(Rule::new(
            IntrRuleACInfo::IEquality,
            vec![ku_fact(x.clone()), kd_fact(x.clone())],
            vec![],
            vec![],
        ));
    }

    out
}

/// `destructionRules diff st` — direct port of
/// `Theory.Tools.IntruderRules.destructionRules`.  Walks the LHS of a
/// context-subterm rewrite rule and emits a destructor `IntrRuleAC`
/// for every level on the path to the RHS position.
///
/// At each public-function step `(NoEq f Public) at index i`, emit:
///
/// ```text
///   [ KD(t_at_pos), KU(siblings)... ] --[]-> [ KD(rhs) ]
/// ```
///
/// where `t_at_pos` is the current sub-term and `siblings` are the
/// other arguments of the parent function (which the intruder must
/// derive in parallel).  Private symbols stop the descent.
pub fn destruction_rules(
    diff: bool,
    rule: &tamarin_term::subterm_rule::CtxtStRule,
) -> Vec<IntrRuleAC> {
    use tamarin_term::lterm::frees;
    use tamarin_term::positions::Position;
    use tamarin_term::function_symbols::{FunSym, NoEqSym, Privacy};
    use tamarin_term::term::Term;

    let lhs = &rule.lhs;
    let rhs = &rule.rhs.term;
    let positions: &[Position] = &rule.rhs.positions;
    if positions.is_empty() { return Vec::new(); }

    // `containsPrivate` mirror.
    fn contains_private(t: &tamarin_term::lterm::LNTerm) -> bool {
        match t {
            Term::Lit(_) => false,
            Term::App(FunSym::NoEq(NoEqSym { privacy, .. }), args) => {
                *privacy == Privacy::Private || args.iter().any(contains_private)
            }
            Term::App(_, args) => args.iter().any(contains_private),
        }
    }

    if !(diff || !frees(rhs).is_empty() || contains_private(rhs)) {
        return Vec::new();
    }

    // Process the first position; recurse on the rest of `positions`.
    if positions.len() > 1 {
        let mut out = destruction_rules(diff, &tamarin_term::subterm_rule::CtxtStRule {
            lhs: lhs.clone(),
            rhs: tamarin_term::subterm_rule::StRhs {
                positions: vec![positions[0].clone()],
                term: rhs.clone(),
            },
        });
        out.extend(destruction_rules(diff, &tamarin_term::subterm_rule::CtxtStRule {
            lhs: lhs.clone(),
            rhs: tamarin_term::subterm_rule::StRhs {
                positions: positions[1..].to_vec(),
                term: rhs.clone(),
            },
        }));
        return out;
    }

    let pos = &positions[0];
    let mut out: Vec<IntrRuleAC> = Vec::new();
    let mut t = lhs.clone();
    let mut uprems: Vec<tamarin_term::lterm::LNTerm> = Vec::new();
    let mut name_acc: Vec<u8> = Vec::new();
    let mut posname = String::new();
    let pos_iter: Vec<i64> = pos.clone();
    for (step_idx, &i) in pos_iter.iter().enumerate() {
        match &t {
            Term::App(FunSym::NoEq(sym), args) => {
                if sym.privacy == Privacy::Private {
                    return out;
                }
                let public = sym.privacy == Privacy::Public;
                if !public { return out; }
                // Haskell `destructionRules` pattern #2 (IntruderRules.hs:135):
                //     go _ (viewTerm -> FApp _ _) (_:[]) _ _ | (frees rhs /= []) = []
                // At the LAST position step, if the current term is an
                // FApp AND rhs has free vars, return [] — neither emit
                // nor recurse.  Current `t` is necessarily FApp here
                // (we're inside the Term::App arm).  Without this,
                // Rust emits extra rules at deep positions like
                // d_0_0_0_prefix_enc_pair or d_1_0_prefix_enc — see
                // denning_sacco_symmetric_cbc which has rule
                // `prefix(enc(<X,Y>,k)) = enc(X,k)` (positions [0,0,0]
                // and [0,1]); at the LAST step into pair(X,Y) and
                // enc(X,Y), Haskell skips.
                if pos_iter.len() == step_idx + 1 && !frees(rhs).is_empty() {
                    return out;
                }
                // Build uprems' = uprems ++ siblings.
                let mut new_uprems = uprems.clone();
                for (j, a) in args.iter().enumerate() {
                    if (j as i64) != i { new_uprems.push(a.clone()); }
                }
                let t_new = match args.get(i as usize) {
                    Some(t) => t.clone(),
                    None => return out, // invalid position
                };
                // Emit the rule unless the next step's term equals rhs
                // and rhs already in uprems' (Haskell's filter).
                let rhs_at_pos = at_pos(lhs, &pos_iter[..=step_idx]);
                let cond_emit = t_new != *rhs && !new_uprems.contains(rhs);
                let _ = rhs_at_pos;
                if cond_emit {
                    // Build the rule name: `_<i><pd>` ++ funs.
                    let posname_now = format!("_{}{}", i, posname);
                    let mut name = posname_now.as_bytes().to_vec();
                    let funs = {
                        let mut f = name_acc.clone();
                        f.extend_from_slice(b"_");
                        f.extend_from_slice(&sym.name);
                        f
                    };
                    name.extend_from_slice(&funs);
                    let info = IntrRuleACInfo::DestrRule(
                        name,
                        -1,
                        rhs == &at_pos(lhs, pos),
                        frees(rhs).is_empty(),
                    );
                    let mut prems = vec![kd_fact(t_new.clone())];
                    for u in &new_uprems { prems.push(ku_fact(u.clone())); }
                    out.push(Rule::new(info, prems, vec![kd_fact(rhs.clone())], vec![]));
                }
                // Update accumulators and walk down.
                name_acc.extend_from_slice(b"_");
                name_acc.extend_from_slice(&sym.name);
                posname = format!("_{}{}", i, posname);
                uprems = new_uprems;
                t = t_new;
            }
            Term::Lit(_) => {
                // Hit a leaf with positions still remaining — invalid.
                return out;
            }
            _ => return out,
        }
    }
    out
}

/// Read a sub-term at the given path.
fn at_pos(t: &tamarin_term::lterm::LNTerm, pos: &[i64]) -> tamarin_term::lterm::LNTerm {
    use tamarin_term::term::Term;
    let mut cur = t;
    for &i in pos {
        match cur {
            Term::App(_, args) => match args.get(i as usize) {
                Some(a) => cur = a,
                None => return t.clone(),
            },
            _ => return t.clone(),
        }
    }
    cur.clone()
}

/// `subtermIntruderRules` — direct port:
/// `concatMap (destructionRules diff) (S.toList stRules) ++ constructionRules`.
pub fn subterm_intruder_rules(
    diff: bool,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Vec<IntrRuleAC> {
    let mut out: Vec<IntrRuleAC> = Vec::new();
    for r in &sig.st_rules {
        out.extend(destruction_rules(diff, r));
    }
    out.extend(construction_rules(sig));
    out
}

/// `constructionRules`: for every public constructor `f/n` in the
/// signature, emit a KU rule:
///
/// `[KU(x_1), ..., KU(x_n)] --[KU(f(x_1, ..., x_n))]-> [KU(f(x_1, ..., x_n))]`
pub fn construction_rules(sig: &tamarin_term::maude_sig::MaudeSig) -> Vec<IntrRuleAC> {
    use tamarin_term::function_symbols::{
        Constructability, FunSym, NoEqSym, Privacy,
    };
    use tamarin_term::term::f_app_no_eq;
    let mut out = Vec::new();
    for funsym in &sig.fun_syms {
        let s = match funsym {
            FunSym::NoEq(s)
                if s.privacy == Privacy::Public
                && s.constructability == Constructability::Constructor =>
            {
                s.clone()
            }
            _ => continue,
        };
        let arity = s.arity;
        // Build vars x_0 ... x_{n-1} : Msg
        let xs: Vec<tamarin_term::lterm::LNTerm> = (0..arity)
            .map(|i| var_term(LVar::new("x", LSort::Msg, i as u64)))
            .collect();
        let prems: Vec<LNFact> = xs.iter().cloned().map(ku_fact).collect();
        let m = f_app_no_eq(s.clone(), xs);
        let conc = ku_fact(m.clone());
        let act = ku_fact(m);
        // Encode the constructor name in the IntrRuleACInfo.
        let mut name = b"_".to_vec();
        name.extend_from_slice(&s.name);
        let _ = NoEqSym::new(b"".to_vec(), 0,
            Privacy::Public, Constructability::Constructor); // suppress warning
        let info = IntrRuleACInfo::ConstrRule(name);
        out.push(Rule::new(info, prems, vec![conc], vec![act]));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn special_rules_count_excluding_diff() {
        let r = special_intruder_rules(false);
        assert_eq!(r.len(), 5);
        assert!(matches!(r[0].info, IntrRuleACInfo::Coerce));
        assert!(matches!(r[1].info, IntrRuleACInfo::PubConstr));
        assert!(matches!(r[2].info, IntrRuleACInfo::FreshConstr));
        assert!(matches!(r[3].info, IntrRuleACInfo::ISend));
        assert!(matches!(r[4].info, IntrRuleACInfo::IRecv));
    }

    #[test]
    fn special_rules_count_with_diff() {
        let r = special_intruder_rules(true);
        assert_eq!(r.len(), 6);
        assert!(matches!(r[5].info, IntrRuleACInfo::IEquality));
    }

    #[test]
    fn pub_constr_has_x_pub_in_new_vars() {
        let r = &special_intruder_rules(false)[1];
        assert_eq!(r.new_vars.len(), 1);
    }

    #[test]
    fn fresh_constr_has_fresh_premise() {
        let r = &special_intruder_rules(false)[2];
        assert_eq!(r.premises.len(), 1);
        assert!(matches!(
            r.premises[0].tag,
            crate::fact::FactTag::Fresh
        ));
    }

    #[test]
    fn isend_emits_in_conclusion() {
        let r = &special_intruder_rules(false)[3];
        assert!(matches!(r.conclusions[0].tag, crate::fact::FactTag::In));
    }

    // =========================================================================
    // construction_rules: per-symbol KU constructor generation.
    //
    // Direct Haskell-spec mirror — Theory.Tools.IntruderRules.hs:
    //
    //     constructionRules fSig =
    //         [ createRule s k | (s, (k, Public, Constructor)) <- S.toList fSig ]
    //       where
    //         createRule s k = Rule (ConstrRule (append (pack "_") s))
    //                              (map kuFact vars) [concfact] [concfact] []
    //           where vars = take k [varTerm (LVar "x" LSortMsg i) | i <- [0..]]
    //                 m = fAppNoEq (s, (k, Public, Constructor)) vars
    //                 concfact = kuFact m
    // =========================================================================

    #[test]
    fn construction_rules_pair_signature_emits_pair_rule() {
        // The default pair-only signature has `pair/2`, `fst/1`, `snd/1`.
        // pair is Public+Constructor → emits a KU rule;
        // fst, snd are Public+Destructor → no construction rule.
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let rules = construction_rules(&sig);
        // Find the pair rule.
        let pair_rule = rules.iter().find(|r| match &r.info {
            IntrRuleACInfo::ConstrRule(name) => name == b"_pair",
            _ => false,
        });
        let pair_rule = pair_rule.expect("expected pair construction rule");
        // pair/2 → 2 KU premises, 1 KU conclusion, 1 KU action.
        assert_eq!(pair_rule.premises.len(), 2);
        assert_eq!(pair_rule.conclusions.len(), 1);
        assert_eq!(pair_rule.actions.len(), 1);
        // All facts have KU tag.
        for f in pair_rule.premises.iter()
            .chain(&pair_rule.conclusions)
            .chain(&pair_rule.actions)
        {
            assert_eq!(f.tag, crate::fact::FactTag::Ku);
        }
    }

    #[test]
    fn construction_rules_only_emits_constructor_info() {
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let rules = construction_rules(&sig);
        // Every emitted rule should have `ConstrRule` info — never
        // a `DestrRule` (we filter on Constructability).
        for r in &rules {
            match &r.info {
                IntrRuleACInfo::ConstrRule(_) => {}
                other => panic!("expected ConstrRule, got {:?}", other),
            }
        }
        assert!(!rules.is_empty(), "default pair sig has at least one constructor");
    }

    /// Symmetric-encryption signature should emit one destructor rule
    /// for `sdec(senc(x, y), y) = x`.  The rule must have:
    ///   - First premise: KD(senc(x, y)).
    ///   - Second premise: KU(y).
    ///   - Conclusion: KD(x).
    #[test]
    fn destruction_rules_sym_enc_emits_decryption() {
        let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        // We expect exactly one destructor: the outermost decryption.
        assert!(!rules.is_empty(),
            "expected at least one sdec destructor; got {:?}", rules);
        // Inspect: first rule should have KD as first premise + at least one KU.
        let first = &rules[0];
        assert_eq!(first.premises[0].tag, crate::fact::FactTag::Kd);
        assert!(first.premises.iter().skip(1).all(|p| p.tag == crate::fact::FactTag::Ku),
            "follow-on premises must be KU; got {:?}", first.premises);
        assert_eq!(first.conclusions[0].tag, crate::fact::FactTag::Kd);
    }

    /// Pair signature emits `fst` / `snd` destructors.
    #[test]
    fn destruction_rules_pair_emits_fst_snd_destructors() {
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        // One destructor per rule; pair has fst + snd → 2 destructor rules.
        assert!(rules.len() >= 2,
            "expected >= 2 pair destructors (fst + snd); got {}", rules.len());
    }

    /// `subtermIntruderRules` on a sym-enc signature should combine
    /// construction (senc) + destruction (sdec).
    #[test]
    fn subterm_intruder_rules_combines_construction_and_destruction() {
        let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
        let rules = subterm_intruder_rules(false, &sig);
        let any_destr = rules.iter().any(|r|
            matches!(r.info, IntrRuleACInfo::DestrRule(..)));
        let any_constr = rules.iter().any(|r|
            matches!(r.info, IntrRuleACInfo::ConstrRule(_)));
        assert!(any_destr, "expected at least one DestrRule");
        assert!(any_constr, "expected at least one ConstrRule");
    }

    #[test]
    fn construction_rules_premise_count_equals_arity() {
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        for r in construction_rules(&sig) {
            // Pull the symbol's arity from the rule's KU action term.
            let conc_term = &r.conclusions[0].terms[0];
            let arity = match conc_term {
                tamarin_term::term::Term::App(_, args) => args.len(),
                tamarin_term::term::Term::Lit(_) => 0,
            };
            assert_eq!(r.premises.len(), arity,
                "premise count must equal symbol arity");
            assert_eq!(r.conclusions.len(), 1);
            assert_eq!(r.actions.len(), 1);
        }
    }
}
