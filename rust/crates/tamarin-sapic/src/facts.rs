//! Port of `Sapic.Facts` (`lib/sapic/src/Sapic/Facts.hs`) — the
//! translation-specific fact/action types (`TransFact` / `TransAction`), their
//! conversion to real `LNFact`s (`factToFact` / `actionToFact`), the
//! `AnnotatedRule` carrier, and the final `toRule` that produces a
//! `ProtoRuleE` with HS-exact name / color / process / role attributes.
//!
//! Scope: the facts/actions reachable by the linear subset needed for
//! `typing2.spthy` — `Init`, `State_<pos>`, `Fr`, `Out`, and `TamarinAct`
//! (the `Test` event).  Other constructors are present (so the enums match HS)
//! but only the ones typing2 exercises are wired through `to_rule`.

use tamarin_term::lterm::{LVar, LNTerm};
use tamarin_term::vterm::{Lit, VTerm};
use tamarin_utils::color::{rgb_to_hex, rgb_to_hsv, hsv_to_rgb, Hsv, Rgb};

use tamarin_theory::fact::{proto_fact, fresh_fact, out_fact, in_fact, LNFact, Multiplicity};
use tamarin_theory::rule::{ProtoRuleE, ProtoRuleEInfo, ProtoRuleName, Rule, RuleAttributes};
use tamarin_theory::sapic::{
    pretty_position, GoodAnnotation, PlainProcess, Process, ProcessPosition, SapicLVar,
};
use tamarin_theory::pretty_sapic::pretty_sapic_top_level;

use crate::annotation::ProcessAnnotation;

// =============================================================================
// StateKind / TransFact / TransAction (Facts.hs:90-127, 53-77)
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateKind {
    LState,
    PState,
    LSemiState,
    PSemiState,
}

impl StateKind {
    /// `isSemiState` (Facts.hs:147-151).
    pub fn is_semi_state(self) -> bool {
        matches!(self, StateKind::LSemiState | StateKind::PSemiState)
    }
    /// `multiplicity` (Facts.hs:153-157).
    pub fn multiplicity(self) -> Multiplicity {
        match self {
            StateKind::LState | StateKind::LSemiState => Multiplicity::Linear,
            StateKind::PState | StateKind::PSemiState => Multiplicity::Persistent,
        }
    }
}

/// `TransFact` (Facts.hs:96-108) — premise/conclusion facts.  Only the
/// constructors used by the linear subset are filled in `factToFact`; the rest
/// are present for type-parity and will be wired in later phases.
#[derive(Debug, Clone, PartialEq)]
pub enum TransFact {
    Fr(LVar),
    In(LNTerm),
    Out(LNTerm),
    State(StateKind, ProcessPosition, Vec<LVar>),
    /// A literal user MSR fact (`TamarinFact`).
    TamarinFact(LNFact),
    /// `PureCell t1 t2` (Facts.hs:108): `L_PureState( t1, t2 )` — the pure-state
    /// cell content (used only when the state-channel optimisation is enabled).
    PureCell(LNTerm, LNTerm),
    /// `CellLocked t1 t2` (Facts.hs:109): `L_CellLocked( t1, t2 )` — the
    /// pure-state lock token.
    CellLocked(LNTerm, LNTerm),
}

/// `TransAction` (Facts.hs:43-77) — action facts.  Only the constructors used
/// by the linear subset are filled in `actionToFact`.
#[derive(Debug, Clone, PartialEq)]
pub enum TransAction {
    InitEmpty,
    EventEmpty,
    /// A literal user action fact (`TamarinAct`).
    TamarinAct(LNFact),
    /// `PredicateA f` (Facts.hs:74): renders `f` with its name prefixed by
    /// `Pred_` (used by the positive arm of `if t1 = t2`).
    PredicateA(LNFact),
    /// `NegPredicateA f` (Facts.hs:75): renders `f` with its name prefixed by
    /// `Pred_Not_` (the negative arm of `if t1 = t2`).
    NegPredicateA(LNFact),
    // --- mutable state (Phase 3, Facts.hs:59-62) ---
    /// `IsIn t v` (Facts.hs:220): `IsIn( t, v )` — the lookup-found action.
    IsIn(LNTerm, LVar),
    /// `IsNotSet t` (Facts.hs:221): `IsNotSet( t )` — the lookup-not-found action.
    IsNotSet(LNTerm),
    /// `InsertA t1 t2` (Facts.hs:222): `Insert( t1, t2 )`.
    InsertA(LNTerm, LNTerm),
    /// `DeleteA t` (Facts.hs:223): `Delete( t )`.
    DeleteA(LNTerm),
    // --- locks (Phase 4, Facts.hs:63-67) ---
    /// `LockNamed t v` (Facts.hs:228): `Lock_<idx v>( '<idx v>', v, t )`.
    LockNamed(LNTerm, LVar),
    /// `LockUnnamed t v` (Facts.hs:229): `Lock( '<idx v>', v, t )`.
    LockUnnamed(LNTerm, LVar),
    /// `UnlockNamed t v` (Facts.hs:230): `Unlock_<idx v>( '<idx v>', v, t )`.
    UnlockNamed(LNTerm, LVar),
    /// `UnlockUnnamed t v` (Facts.hs:231): `Unlock( '<idx v>', v, t )`.
    UnlockUnnamed(LNTerm, LVar),
}

/// `SpecialPosition` (Facts.hs:110-112).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialPosition {
    InitPosition,
    NoPosition,
}

/// `Either ProcessPosition SpecialPosition`.
#[derive(Debug, Clone, PartialEq)]
pub enum RulePosition {
    Pos(ProcessPosition),
    Special(SpecialPosition),
}

// =============================================================================
// State variable set: HS stores `tildex` as a `Set LVar`; `factToFact`
// renders it via `S.toList` (sorted, deduplicated).  We model it as a sorted,
// deduped `Vec<LVar>` to match the rendered order.
// =============================================================================

fn sorted_unique(mut vs: Vec<LVar>) -> Vec<LVar> {
    vs.sort();
    vs.dedup();
    vs
}

// =============================================================================
// factToFact / actionToFact (Facts.hs:213-271)
// =============================================================================

/// `factToFact` (Facts.hs:253-271).
pub fn fact_to_fact(f: &TransFact) -> LNFact {
    match f {
        TransFact::Fr(v) => fresh_fact(VTerm::Lit(Lit::Var(v.clone()))),
        TransFact::In(t) => in_fact(t.clone()),
        TransFact::Out(t) => out_fact(t.clone()),
        TransFact::State(kind, p, vars) => {
            let name = if kind.is_semi_state() { "Semistate" } else { "State" };
            let full = format!("{}_{}", name, pretty_position(p));
            let ts: Vec<LNTerm> = sorted_unique(vars.clone())
                .into_iter()
                .map(|v| VTerm::Lit(Lit::Var(v)))
                .collect();
            // multiplicity from the state kind.
            proto_fact_mult(kind.multiplicity(), &full, ts)
        }
        TransFact::TamarinFact(f) => f.clone(),
        // `factToFact (PureCell t1 t2) = protoFact Linear "L_PureState" [t1, t2]`
        // (Facts.hs:269).
        TransFact::PureCell(t1, t2) => {
            proto_fact(Multiplicity::Linear, "L_PureState", vec![t1.clone(), t2.clone()])
        }
        // `factToFact (CellLocked t1 t2) = protoFact Linear "L_CellLocked" [t1, t2]`
        // (Facts.hs:270).
        TransFact::CellLocked(t1, t2) => {
            proto_fact(Multiplicity::Linear, "L_CellLocked", vec![t1.clone(), t2.clone()])
        }
    }
}

/// `actionToFact` (Facts.hs:213-234).
pub fn action_to_fact(a: &TransAction) -> LNFact {
    match a {
        TransAction::InitEmpty => proto_fact(Multiplicity::Linear, "Init", vec![]),
        TransAction::EventEmpty => proto_fact(Multiplicity::Linear, "Event", vec![]),
        TransAction::TamarinAct(f) => f.clone(),
        // `actionToFact (PredicateA f) = mapFactName ("Pred_" ++) f`
        // (Facts.hs:226).
        TransAction::PredicateA(f) => map_fact_name(f, "Pred_"),
        // `actionToFact (NegPredicateA f) = mapFactName ("Pred_Not_" ++) f`
        // (Facts.hs:227).
        TransAction::NegPredicateA(f) => map_fact_name(f, "Pred_Not_"),
        // `actionToFact (IsIn t v) = protoFact Linear "IsIn" [t, varTerm v]`
        // (Facts.hs:220).
        TransAction::IsIn(t, v) => proto_fact(
            Multiplicity::Linear,
            "IsIn",
            vec![t.clone(), VTerm::Lit(Lit::Var(v.clone()))],
        ),
        // `actionToFact (IsNotSet t) = protoFact Linear "IsNotSet" [t]` (Facts.hs:221).
        TransAction::IsNotSet(t) => proto_fact(Multiplicity::Linear, "IsNotSet", vec![t.clone()]),
        // `actionToFact (InsertA t1 t2) = protoFact Linear "Insert" [t1, t2]`
        // (Facts.hs:222).
        TransAction::InsertA(t1, t2) => {
            proto_fact(Multiplicity::Linear, "Insert", vec![t1.clone(), t2.clone()])
        }
        // `actionToFact (DeleteA t) = protoFact Linear "Delete" [t]` (Facts.hs:223).
        TransAction::DeleteA(t) => proto_fact(Multiplicity::Linear, "Delete", vec![t.clone()]),
        // `actionToFact (LockNamed t v) =
        //    protoFact Linear (lockFactName v) [lockPubTerm v, varTerm v, t]`
        // (Facts.hs:228).
        TransAction::LockNamed(t, v) => proto_fact(
            Multiplicity::Linear,
            &lock_fact_name(v),
            vec![lock_pub_term(v), VTerm::Lit(Lit::Var(v.clone())), t.clone()],
        ),
        // `actionToFact (LockUnnamed t v) =
        //    protoFact Linear "Lock" [lockPubTerm v, varTerm v, t]` (Facts.hs:229).
        TransAction::LockUnnamed(t, v) => proto_fact(
            Multiplicity::Linear,
            "Lock",
            vec![lock_pub_term(v), VTerm::Lit(Lit::Var(v.clone())), t.clone()],
        ),
        // `actionToFact (UnlockNamed t v) =
        //    protoFact Linear (unlockFactName v) [lockPubTerm v, varTerm v, t]`
        // (Facts.hs:230).
        TransAction::UnlockNamed(t, v) => proto_fact(
            Multiplicity::Linear,
            &unlock_fact_name(v),
            vec![lock_pub_term(v), VTerm::Lit(Lit::Var(v.clone())), t.clone()],
        ),
        // `actionToFact (UnlockUnnamed t v) =
        //    protoFact Linear "Unlock" [lockPubTerm v, varTerm v, t]` (Facts.hs:231).
        TransAction::UnlockUnnamed(t, v) => proto_fact(
            Multiplicity::Linear,
            "Unlock",
            vec![lock_pub_term(v), VTerm::Lit(Lit::Var(v.clone())), t.clone()],
        ),
    }
}

/// `lockFactName v = "Lock_" ++ show (lvarIdx v)` (Facts.hs:180-181).
pub fn lock_fact_name(v: &LVar) -> String {
    format!("Lock_{}", v.idx)
}

/// `unlockFactName v = "Unlock_" ++ show (lvarIdx v)` (Facts.hs:183-184).
pub fn unlock_fact_name(v: &LVar) -> String {
    format!("Unlock_{}", v.idx)
}

/// `lockPubTerm v = pubTerm (show (lvarIdx v))` (Facts.hs:186-187): the public
/// constant `'<idx v>'` used as the first argument of the lock/unlock facts.
fn lock_pub_term(v: &LVar) -> LNTerm {
    tamarin_term::lterm::pub_term(v.idx.to_string())
}

/// `mapFactName (prefix ++)` (Facts.hs:173-177): prepend `prefix` to a
/// `ProtoFact` name (other tags are left unchanged).
fn map_fact_name(f: &LNFact, prefix: &str) -> LNFact {
    use tamarin_theory::fact::FactTag;
    let tag = match &f.tag {
        FactTag::Proto(m, s, i) => FactTag::Proto(*m, format!("{prefix}{s}"), *i),
        other => other.clone(),
    };
    let mut nf = tamarin_theory::fact::Fact::new(tag, f.terms.clone());
    nf = nf.with_annotations(f.annotations.clone());
    nf
}

/// `proto_fact` is fixed to `Linear`; the state fact needs an explicit
/// multiplicity, so build the tag directly.
fn proto_fact_mult(mult: Multiplicity, name: &str, terms: Vec<LNTerm>) -> LNFact {
    use tamarin_theory::fact::{Fact, FactTag};
    Fact::new(FactTag::Proto(mult, name.to_string(), terms.len()), terms)
}

// =============================================================================
// crc32 / colorForProcessName (Facts.hs:327-374)
// =============================================================================

/// `crc32` (Facts.hs:327-331).
fn crc32(s: &str) -> u32 {
    fn inner(c: u32) -> u32 {
        (c >> 1) ^ (0xedb8_8329u32 & 0u32.wrapping_sub(c & 1))
    }
    let mut acc: u32 = 0xffff_ffff;
    for ch in s.chars() {
        let m = ch as u32;
        let mut c = acc ^ m;
        for _ in 0..8 {
            c = inner(c);
        }
        acc = c;
    }
    acc
}

/// `colorHash` (Facts.hs:347-351): per-channel byte of the CRC, scaled to [0,1].
fn color_hash(s: &str) -> Rgb {
    let h = crc32(s);
    let nth = |n: u32| -> f64 { (((h >> (8 * n)) & 0xff) as f64) / 255.0 };
    Rgb::new(nth(0), nth(1), nth(2))
}

fn interpolate(a: Hsv, b: Hsv, t: f64) -> Hsv {
    Hsv::new(
        (b.h - a.h) * t + a.h,
        (b.s - a.s) * t + a.s,
        (b.v - a.v) * t + a.v,
    )
}

/// `colorForProcessName` (Facts.hs:360-374).
pub fn color_for_process_name(names: &[String]) -> Rgb {
    if names.is_empty() {
        // HS `RGB 255 255 255` — `rgbToHex` clamps `floor(256*255)` to 255 →
        // `#ffffff`.  Mirror with the same out-of-[0,1] value.
        return Rgb::new(255.0, 255.0, 255.0);
    }
    let palette: Vec<Hsv> = names.iter().map(|n| rgb_to_hsv(color_hash(n))).collect();
    let mut acc = palette[0];
    let mut i: i32 = 0;
    for v in &palette[1..] {
        let t = 2f64.powi(-i);
        acc = interpolate(acc, *v, t);
        i += 1;
    }
    // normalize (HSV h _ _) = HSV h 0.5 0.5
    let normalized = Hsv::new(acc.h, 0.5, 0.5);
    hsv_to_rgb(normalized)
}

/// The rendered `color=` hex value for a process-name list.
pub fn color_hex_for_process_name(names: &[String]) -> String {
    rgb_to_hex(color_for_process_name(names))
}

// =============================================================================
// AnnotatedRule + toRule (Facts.hs:114-127, 376-403)
// =============================================================================

/// `AnnotatedRule` (Facts.hs:114-127).  `process` is the subprocess this rule
/// was generated for (used for naming / color / `process=` attribute).
#[derive(Debug, Clone)]
pub struct AnnotatedRule<Ann> {
    pub process_name: Option<String>,
    pub process: Process<Ann, SapicLVar>,
    pub position: RulePosition,
    pub prems: Vec<TransFact>,
    pub acts: Vec<TransAction>,
    pub concs: Vec<TransFact>,
    /// Embedded restrictions (HS `restr :: [SyntacticLNFormula]`, Facts.hs:123).
    /// Carried as parser-AST formulas so they flow through the existing
    /// `_restrict` expansion (`rule_restriction::lift_rule_restrictions`).
    /// Non-empty only for `if <formula>` arms (the `Cond` combinator).
    pub restr: Vec<tamarin_parser::ast::Formula>,
    pub index: usize,
}

/// `prettyEitherPositionOrSpecial` (Facts.hs:319-322).
fn pretty_position_or_special(pos: &RulePosition) -> String {
    match pos {
        RulePosition::Pos(p) => pretty_position(p),
        RulePosition::Special(SpecialPosition::InitPosition) => "Init".to_string(),
        RulePosition::Special(SpecialPosition::NoPosition) => String::new(),
    }
}

/// `getTopLevelName` (Facts.hs:295-298) — the process-name list from the
/// (already-name-propagated) annotation of the subprocess.
fn get_top_level_name<Ann: GoodAnnotation>(p: &Process<Ann, SapicLVar>) -> Vec<String> {
    p.annotation().parsed().process_names.clone()
}

/// `roleFromProcessNameList` (Facts.hs:399-400).
fn role_from_process_name_list(names: &[String]) -> String {
    if names.is_empty() {
        "Process".to_string()
    } else {
        names.join("_")
    }
}

/// `stripNonAlphanumerical = filter isAlpha` (Facts.hs:401).
fn strip_non_alphabetic(s: &str) -> String {
    s.chars().filter(|c| c.is_alphabetic()).collect()
}

/// The `process="..."` attribute value: `prettySapicTopLevel'` of the
/// subprocess (rendered through the same printer HS uses, ProcessAnnotation
/// erased to the plain process).
pub fn process_attr_value<Ann: GoodAnnotation + Clone>(p: &Process<Ann, SapicLVar>) -> String {
    let plain = to_plain(p);
    pretty_sapic_top_level(&plain)
}

/// Erase the rich annotation back to a `PlainProcess` for printing (HS
/// `toProcess`).
fn to_plain<Ann: GoodAnnotation + Clone>(p: &Process<Ann, SapicLVar>) -> PlainProcess {
    match p {
        Process::Null(a) => Process::Null(a.parsed().clone()),
        Process::Action(ac, a, body) => {
            Process::Action(ac.clone(), a.parsed().clone(), Box::new(to_plain(body)))
        }
        Process::Comb(c, a, l, r) => Process::Comb(
            c.clone(),
            a.parsed().clone(),
            Box::new(to_plain(l)),
            Box::new(to_plain(r)),
        ),
    }
}

/// The HS-faithful rule name (Facts.hs:380-388).
pub fn rule_name<Ann: GoodAnnotation + Clone>(r: &AnnotatedRule<Ann>) -> String {
    match &r.process_name {
        Some(s) => s.clone(),
        None => {
            let plain = to_plain(&r.process);
            let base = pretty_sapic_top_level(&plain);
            let stripped = strip_non_alphabetic(&base);
            let un_null = if stripped.is_empty() { "p".to_string() } else { stripped };
            format!(
                "{}_{}_{}",
                un_null,
                r.index,
                pretty_position_or_special(&r.position)
            )
        }
    }
}

/// `toRule` (Facts.hs:376-403): build the final `ProtoRuleE` with HS-exact
/// `name`, `color`, `process`, `role`, `issapicrule` attributes.
///
/// `ignoreDerivChecks = isLookup process` (Facts.hs:404-405): the lookup rules
/// carry the `no_derivcheck` attribute so the message-derivation check skips
/// them (the bound lookup variable is unconstrained at that point).
pub fn to_rule(r: &AnnotatedRule<ProcessAnnotation<LVar>>) -> ProtoRuleE {
    let name = rule_name(r);
    let names = get_top_level_name(&r.process);
    // HS `isLookup (ProcessComb (Lookup _ _) _ _ _) = True; isLookup _ = False`
    // (Facts.hs:404-405) — the LITERAL process node this rule was generated for.
    let is_lookup_proc = matches!(
        &r.process,
        Process::Comb(tamarin_theory::sapic::ProcessCombinator::Lookup(_, _), _, _, _)
    );
    let attr = RuleAttributes {
        color: Some(color_for_process_name(&names)),
        process: Some(to_plain(&r.process)),
        ignore_deriv_checks: is_lookup_proc,
        is_sapic_rule: true,
        role: Some(role_from_process_name_list(
            &r.process.annotation().parsed().process_names,
        )),
    };
    let info = ProtoRuleEInfo {
        name: ProtoRuleName::Stand(name),
        attributes: attr,
        restrictions: Vec::new(),
    };
    let prems: Vec<LNFact> = r.prems.iter().map(fact_to_fact).collect();
    let acts: Vec<LNFact> = r.acts.iter().map(action_to_fact).collect();
    let concs: Vec<LNFact> = r.concs.iter().map(fact_to_fact).collect();
    let new_vars = compute_new_vars(&prems, &concs, &acts);
    Rule::new(info, prems, concs, acts).with_new_vars(new_vars)
}

/// `newVariables l r` (Rule.hs): variables in conclusions/actions not bound by
/// the premises.  Mirrors `elaborate.rs::compute_new_vars`.
pub fn compute_new_vars(prems: &[LNFact], concs: &[LNFact], acts: &[LNFact]) -> Vec<LNTerm> {
    use std::collections::BTreeSet;
    fn collect(t: &LNTerm, out: &mut BTreeSet<LVar>) {
        match t {
            VTerm::Lit(Lit::Var(v)) => {
                out.insert(v.clone());
            }
            VTerm::Lit(_) => {}
            VTerm::App(_, args) => {
                for a in args.iter() {
                    collect(a, out);
                }
            }
        }
    }
    let mut prem_vars: BTreeSet<LVar> = BTreeSet::new();
    for f in prems {
        for t in &f.terms {
            collect(t, &mut prem_vars);
        }
    }
    let mut new_set: BTreeSet<LVar> = BTreeSet::new();
    for f in concs.iter().chain(acts) {
        for t in &f.terms {
            let mut here = BTreeSet::new();
            collect(t, &mut here);
            for v in here {
                if !prem_vars.contains(&v) {
                    new_set.insert(v);
                }
            }
        }
    }
    new_set.into_iter().map(|v| VTerm::Lit(Lit::Var(v))).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crc32_known_values() {
        // CRC32 (the "reflected" 0xEDB88320 polynomial used by HS) of "" is
        // 0xFFFFFFFF before final-xor; HS does NOT apply the final xor, so for
        // the empty string `crc32 "" == 0xffffffff`.
        assert_eq!(crc32(""), 0xffff_ffff);
    }

    #[test]
    fn empty_names_is_white() {
        assert_eq!(color_hex_for_process_name(&[]), "#ffffff");
    }

    #[test]
    fn state_fact_name_and_mult() {
        let f = TransFact::State(StateKind::LState, vec![1], vec![]);
        let lnf = fact_to_fact(&f);
        match &lnf.tag {
            tamarin_theory::fact::FactTag::Proto(m, n, _) => {
                assert_eq!(n, "State_1");
                assert_eq!(*m, Multiplicity::Linear);
            }
            _ => panic!("expected proto fact"),
        }
    }

    #[test]
    fn empty_position_state_renders_state_underscore() {
        let f = TransFact::State(StateKind::LState, vec![], vec![]);
        let lnf = fact_to_fact(&f);
        if let tamarin_theory::fact::FactTag::Proto(_, n, _) = &lnf.tag {
            assert_eq!(n, "State_");
        } else {
            panic!();
        }
    }
}
