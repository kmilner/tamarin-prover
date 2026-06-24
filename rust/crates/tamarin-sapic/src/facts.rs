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
}

/// `TransAction` (Facts.hs:43-77) — action facts.  Only the constructors used
/// by the linear subset are filled in `actionToFact`.
#[derive(Debug, Clone, PartialEq)]
pub enum TransAction {
    InitEmpty,
    EventEmpty,
    /// A literal user action fact (`TamarinAct`).
    TamarinAct(LNFact),
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
    }
}

/// `actionToFact` (Facts.hs:213-234).
pub fn action_to_fact(a: &TransAction) -> LNFact {
    match a {
        TransAction::InitEmpty => proto_fact(Multiplicity::Linear, "Init", vec![]),
        TransAction::EventEmpty => proto_fact(Multiplicity::Linear, "Event", vec![]),
        TransAction::TamarinAct(f) => f.clone(),
    }
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
    /// Embedded restrictions — empty for the linear subset.
    pub restr: Vec<()>,
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
/// `ignoreDerivChecks = isLookup process` (false for the linear subset).
pub fn to_rule(r: &AnnotatedRule<ProcessAnnotation<LVar>>) -> ProtoRuleE {
    let name = rule_name(r);
    let names = get_top_level_name(&r.process);
    let attr = RuleAttributes {
        color: Some(color_for_process_name(&names)),
        process: Some(to_plain(&r.process)),
        ignore_deriv_checks: false,
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
fn compute_new_vars(prems: &[LNFact], concs: &[LNFact], acts: &[LNFact]) -> Vec<LNTerm> {
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
