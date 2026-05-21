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
/// `minimizeIntruderRules diff $ concatMap (destructionRules diff) (S.toList stRules) ++ constructionRules`.
///
/// IntruderRules.hs:210-213.  The `minimizeIntruderRules` pass strips
/// subsumed/duplicate destructor rules — without it, a single equation
/// containing multiple variable positions of the same rhs (e.g. chaum's
/// `unblind(sign(blind(m,r),k), r) = sign(m,k)` where m at [0,0,0] and
/// k at [0,1] both walk through position [0]) emits the same `_0_unblind`
/// destructor twice.  Those duplicates then cause `solve_chain_goal` to
/// fan out 2 identical destructor branches (idx-renamed but otherwise
/// equal), inflating source-case counts at saturate time
/// (chaum::unforgeability KU(sign) goes from Haskell's 1 case to Rust's
/// 4 cases).
pub fn subterm_intruder_rules(
    diff: bool,
    sig: &tamarin_term::maude_sig::MaudeSig,
) -> Vec<IntrRuleAC> {
    let mut out: Vec<IntrRuleAC> = Vec::new();
    for r in &sig.st_rules {
        out.extend(destruction_rules(diff, r));
    }
    out.extend(construction_rules(sig));
    minimize_intruder_rules(diff, out)
}

/// Port of `minimizeIntruderRules` (IntruderRules.hs:186-206).
///
/// Two-stage filter:
/// 1. **Subsumption** (skipped in `diff` mode): for each rule with
///    `(prems, concs)`, drop it if any OTHER rule has the same `concs`
///    and a premise set that is a subset of this rule's premises.
///    Mirrors Haskell's `go` accumulator iteration; preserves the order
///    of the first-kept duplicate.
/// 2. **Double-premise filter** (always applied): drop rules whose KD
///    first-premise is a msg-var `t` and whose premises also include
///    `KU(t)` of the same term (with all terms private-free).
fn minimize_intruder_rules(
    diff: bool,
    rules: Vec<IntrRuleAC>,
) -> Vec<IntrRuleAC> {
    let after_subsumption = if diff {
        rules
    } else {
        // Haskell `go checked unchecked`: process `unchecked` left-to-right,
        // dropping any rule subsumed by a peer in `checked ++ unchecked`.
        // We mirror exactly: walk by index, and when checking rule i, the
        // peers are { all kept rules so far } ∪ { all rules with index > i }.
        let n = rules.len();
        let mut kept: Vec<usize> = Vec::with_capacity(n);
        for i in 0..n {
            let r_i = &rules[i];
            let subsumed = (0..n).any(|j| {
                if j == i { return false; }
                // Peer eligibility: either already-kept earlier (j < i and j in kept)
                // or still in `unchecked` (j > i).  Haskell's `checked++unchecked`
                // semantics.
                if j < i && !kept.contains(&j) { return false; }
                let r_j = &rules[j];
                r_j.conclusions == r_i.conclusions
                    && is_subset_of(&r_j.premises, &r_i.premises)
            });
            if !subsumed { kept.push(i); }
        }
        kept.into_iter().map(|i| rules[i].clone()).collect()
    };
    after_subsumption.into_iter().filter(|r| !is_double_premise_rule(r)).collect()
}

/// Multiset-subset check: every premise of `a` (counted with multiplicity)
/// occurs in `b`.  Haskell's `subsetOf` on lists.
fn is_subset_of(a: &[crate::fact::LNFact], b: &[crate::fact::LNFact]) -> bool {
    let mut b_remaining: Vec<bool> = vec![true; b.len()];
    for fa in a {
        let mut found = false;
        for (j, fb) in b.iter().enumerate() {
            if b_remaining[j] && fa == fb {
                b_remaining[j] = false;
                found = true;
                break;
            }
        }
        if !found { return false; }
    }
    true
}

/// `isDoublePremiseRule` (IntruderRules.hs:201-206).
///
/// Drops destructor rules whose first premise is `KD(t)` where `t` is a
/// msg-var, conclusions are ground, no private function symbols appear
/// in premise/conclusion terms, and `KU(t)` also appears among the
/// premises.  These rules are redundant — the intruder can always supply
/// the term directly via the KU premise, so the KD-derivation pathway
/// is never useful.
fn is_double_premise_rule(r: &IntrRuleAC) -> bool {
    use crate::fact::FactTag;
    use tamarin_term::lterm::is_msg_var;
    let (kd_fact_term, rest_prems): (&tamarin_term::lterm::LNTerm, &[crate::fact::LNFact]) =
        match r.premises.split_first() {
            Some((first, rest)) => {
                if first.tag != FactTag::Kd { return false; }
                let t = match first.terms.first() {
                    Some(t) => t,
                    None => return false,
                };
                (t, rest)
            }
            None => return false,
        };
    // Conclusions must be ground.
    let frees_concs = r.conclusions.iter()
        .flat_map(|f| f.terms.iter())
        .any(|t| !tamarin_term::lterm::frees(t).is_empty());
    if frees_concs { return false; }
    // Reject if any term (KD-premise or any prems-term) contains a private symbol.
    fn contains_private(t: &tamarin_term::lterm::LNTerm) -> bool {
        use tamarin_term::function_symbols::{FunSym, NoEqSym, Privacy};
        use tamarin_term::term::Term;
        match t {
            Term::Lit(_) => false,
            Term::App(FunSym::NoEq(NoEqSym { privacy, .. }), args) => {
                *privacy == Privacy::Private || args.iter().any(contains_private)
            }
            Term::App(_, args) => args.iter().any(contains_private),
        }
    }
    if contains_private(kd_fact_term) { return false; }
    for f in r.premises.iter() {
        for t in f.terms.iter() {
            if contains_private(t) { return false; }
        }
    }
    // KD-premise term must be a msg-var.
    if !is_msg_var(kd_fact_term) { return false; }
    // KU(kd_fact_term) must appear among the remaining premises.
    let ku_t = crate::fact::ku_fact(kd_fact_term.clone());
    rest_prems.iter().any(|f| f == &ku_t)
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

    // =========================================================================
    // Haskell-faithfulness invariants for `destruction_rules`.
    //
    // Mirrors IntruderRules.hs:129-157.  Two patterns are easy to break
    // and were broken historically:
    //
    //   1. Pattern #1 line 135: at the LAST position step, if the
    //      current term is an FApp AND rhs has free vars, return [].
    //      (The "skip-last" — task #164 resolved this.)
    //
    //   2. Private-symbol stop (line 149): descending through a Private
    //      constructor terminates the loop early.
    // =========================================================================

    /// `destructionRules` for the sym-enc rule `sdec(senc(x, y), y) = x`
    /// must emit EXACTLY ONE destructor, not two.
    ///
    /// The rule has rhs position [0, 0] — two steps.  Without the
    /// skip-last guard, Rust emits a second (degenerate) destructor at
    /// the inner step, producing `KD(x) + KU(...) → KD(x)` — a
    /// self-loop that explodes the chain search on denning_sacco.
    /// See project_rust_destruction_rules_skip_last.md.
    #[test]
    fn destruction_rules_sym_enc_emits_exactly_one_destructor() {
        let sig = tamarin_term::maude_sig::sym_enc_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        assert_eq!(rules.len(), 1,
            "sym-enc rule `sdec(senc(x, y), y) = x` must yield EXACTLY ONE \
             destructor — the skip-last pattern (IntruderRules.hs:135) \
             elides the inner step.  Got {} rules.  If this regresses, \
             denning_sacco-class chain explosion will silently reappear \
             (see project_rust_destruction_rules_skip_last.md).",
            rules.len());
        let r = &rules[0];
        // Premise[0] = KD(senc(x, y)); follow-on premises = KU(y).
        assert_eq!(r.premises[0].tag, crate::fact::FactTag::Kd);
        // Inner step was elided, so no `KD(x) KU(x) → KD(x)` self-loop.
        for p in &r.premises[1..] {
            assert_eq!(p.tag, crate::fact::FactTag::Ku);
        }
    }

    /// `destructionRules` for the asym-enc rule
    /// `adec(aenc(x, pk(y)), y) = x` likewise emits EXACTLY ONE
    /// destructor (position [0, 0], rhs free var x).
    #[test]
    fn destruction_rules_asym_enc_emits_exactly_one_destructor() {
        let sig = tamarin_term::maude_sig::asym_enc_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        assert_eq!(rules.len(), 1,
            "asym-enc rule must yield EXACTLY ONE destructor; got {} rules. \
             Skip-last pattern was probably regressed.", rules.len());
    }

    /// `destructionRules` for pair `fst(<x,y>) = x` and `snd(<x,y>) = y`
    /// each yield EXACTLY ONE destructor.  Pair is a one-step rule
    /// (position [0]), but skip-last doesn't apply to the FIRST step
    /// because step_idx == 0 and pos_iter.len() == 1 → step_idx+1 == len,
    /// and `t` is `pair(x,y)` (FApp) and rhs is a var (free) — so
    /// skip-last DOES fire.  This means the destructor must be emitted
    /// at the WRAPPING-step (the outer match arm where we step from
    /// the destructor's lhs into pair), NOT at the inner step.
    ///
    /// (This is subtle and worth pinning explicitly.)
    #[test]
    fn destruction_rules_pair_emits_exactly_two_destructors() {
        let sig = tamarin_term::maude_sig::pair_maude_sig();
        let rules: Vec<IntrRuleAC> = sig.st_rules.iter()
            .flat_map(|r| destruction_rules(false, r))
            .collect();
        assert_eq!(rules.len(), 2,
            "pair signature must yield exactly fst + snd destructors \
             (2 total); got {} rules.  Pair rules are `fst(<x,y>) = x` \
             and `snd(<x,y>) = y` at position [0] each.", rules.len());
    }

    /// `destructionRules` short-circuits when the rhs is a closed term
    /// (no free vars) AND `diff=false` AND rhs has no Private symbol.
    /// This is the outer guard at IntruderRules.hs:130 — the function
    /// returns [] before even starting the position walk.
    ///
    /// Pin this by constructing a CtxtStRule whose rhs is a public
    /// constant (no free vars).
    #[test]
    fn destruction_rules_returns_empty_for_closed_rhs_in_non_diff_mode() {
        use tamarin_term::lterm::{LSort, LVar, Name, NameId, NameTag, LNTerm};
        use tamarin_term::subterm_rule::{CtxtStRule, StRhs};
        use tamarin_term::term::Term;
        use tamarin_term::vterm::Lit;
        use tamarin_term::builtin::{pair, senc};

        // Build: lhs = senc(x, pair($a, $b)), rhs = $a (pub const, no frees).
        // Position [1, 0] — into senc's arg 1 (the pair), then into pair's
        // arg 0 ($a).
        let x = LVar::new("x", LSort::Msg, 1);
        let pub_a = Name { tag: NameTag::Pub, id: NameId::new("a") };
        let pub_b = Name { tag: NameTag::Pub, id: NameId::new("b") };
        let pa: LNTerm = Term::Lit(Lit::Con(pub_a.clone()));
        let pb: LNTerm = Term::Lit(Lit::Con(pub_b));
        let lhs = senc(Term::Lit(Lit::Var(x)), pair(pa.clone(), pb));
        let rhs_st = StRhs { positions: vec![vec![1, 0]], term: pa };
        let rule = CtxtStRule::new(lhs, rhs_st);

        // diff=false, rhs has no free vars, rhs has no private symbol →
        // outer guard returns [].
        let out = destruction_rules(false, &rule);
        assert!(out.is_empty(),
            "diff=false + closed rhs (no frees, no private) must short-\
             circuit to empty.  Mirrors IntruderRules.hs:130 outer guard. \
             Got {} rules.", out.len());

        // BUT in diff mode, the guard is bypassed and we DO descend.
        let out_diff = destruction_rules(true, &rule);
        assert!(!out_diff.is_empty(),
            "diff=true must bypass the closed-rhs guard and emit destructors");
    }
}
