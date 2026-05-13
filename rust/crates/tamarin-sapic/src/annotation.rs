//! Port of `Sapic.Annotation` from `lib/sapic/src/Sapic/Annotation.hs`.
//!
//! Translation-time process annotation. Wraps the `ProcessParsedAnnotation`
//! from `tamarin_theory::sapic` with extra fields used by the various
//! analysis passes (lock variables, secret-channel variables, etc.).

use tamarin_theory::sapic::{
    GoodAnnotation, Process, ProcessParsedAnnotation, SapicLVar,
};
use tamarin_term::lterm::LNTerm;

/// Variable annotation wrapper. Semantics: when combined with itself the
/// rightmost wins (matches Haskell `instance Semigroup AnVar`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AnVar<V>(pub V);

/// Annotations attached to a process during translation.
#[derive(Debug, Clone, PartialEq)]
pub struct ProcessAnnotation<V> {
    /// Original parsed annotation (carries process names, location,
    /// back-substitution).
    pub parsing_ann: ProcessParsedAnnotation,
    /// Fresh variable annotating a `lock` action.
    pub lock: Option<AnVar<V>>,
    /// Fresh variable annotating an `unlock` action; should match the
    /// corresponding `lock`.
    pub unlock: Option<AnVar<V>>,
    /// Variable annotating a channel known to be secret.
    pub secret_channel: Option<AnVar<V>>,
    /// Two terms used to model a `let`-binding with a destructor RHS.
    pub destructor_equation: Option<(LNTerm, LNTerm)>,
    /// Whether this process has a non-zero else branch (relevant for
    /// `let` translation).
    pub else_branch: bool,
    /// Whether this lock/insert/lookup is part of a "pure state" pattern
    /// that the optimiser can elide.
    pub pure_state: bool,
    /// Variable identifying the state cell associated with this op.
    pub state_channel: Option<AnVar<V>>,
    /// Term marking the binding of a state-channel.
    pub is_state_channel: Option<LNTerm>,
}

impl<V> Default for ProcessAnnotation<V> {
    fn default() -> Self {
        ProcessAnnotation {
            parsing_ann: ProcessParsedAnnotation::default(),
            lock: None,
            unlock: None,
            secret_channel: None,
            destructor_equation: None,
            else_branch: true,
            pure_state: false,
            state_channel: None,
            is_state_channel: None,
        }
    }
}

impl<V: Clone> ProcessAnnotation<V> {
    pub fn empty() -> Self { Self::default() }

    pub fn with_lock(v: V) -> Self {
        Self { lock: Some(AnVar(v)), ..Default::default() }
    }
    pub fn with_unlock(v: V) -> Self {
        Self { unlock: Some(AnVar(v)), ..Default::default() }
    }
    pub fn with_secret_channel(v: V) -> Self {
        Self { secret_channel: Some(AnVar(v)), ..Default::default() }
    }
    pub fn with_destructor_equation(t1: LNTerm, t2: LNTerm, else_branch: bool) -> Self {
        Self {
            destructor_equation: Some((t1, t2)),
            else_branch,
            ..Default::default()
        }
    }
    pub fn with_else_branch(b: bool) -> Self {
        Self { else_branch: b, ..Default::default() }
    }

    /// Combine two annotations. Optional fields prefer the *first* defined
    /// value (mirroring Haskell's `Maybe` semigroup which is left-biased
    /// only for `Just`/`Just`); booleans are OR'ed; `else_branch` is taken
    /// from the right operand.
    pub fn append(self, other: Self) -> Self {
        ProcessAnnotation {
            parsing_ann: self.parsing_ann.append(other.parsing_ann),
            lock: self.lock.or(other.lock),
            unlock: self.unlock.or(other.unlock),
            secret_channel: self.secret_channel.or(other.secret_channel),
            destructor_equation: self.destructor_equation.or(other.destructor_equation),
            else_branch: other.else_branch,
            pure_state: self.pure_state || other.pure_state,
            state_channel: self.state_channel.or(other.state_channel),
            is_state_channel: self.is_state_channel.or(other.is_state_channel),
        }
    }
}

impl<V: Clone> GoodAnnotation for ProcessAnnotation<V> {
    fn parsed(&self) -> &ProcessParsedAnnotation { &self.parsing_ann }
    fn set_parsed(self, p: ProcessParsedAnnotation) -> Self {
        ProcessAnnotation { parsing_ann: p, ..self }
    }
    fn default_annotation() -> Self { Self::default() }
}

/// `AnnotatedProcess`: SAPIC process post-translation, parameterised over
/// `V` (typically `tamarin_term::lterm::LVar`).
pub type AnnotatedProcess<V> = Process<ProcessAnnotation<V>, SapicLVar>;

/// `toAnProcess`: lift a parsed process into a translation annotation by
/// wrapping the parsed annotation in `ProcessAnnotation`.
pub fn to_annotated<V: Clone>(
    p: Process<ProcessParsedAnnotation, SapicLVar>,
) -> Process<ProcessAnnotation<V>, SapicLVar> {
    fn go<V: Clone>(
        p: Process<ProcessParsedAnnotation, SapicLVar>,
    ) -> Process<ProcessAnnotation<V>, SapicLVar> {
        match p {
            Process::Null(ann) => Process::Null(ProcessAnnotation {
                parsing_ann: ann,
                ..Default::default()
            }),
            Process::Action(a, ann, body) => Process::Action(
                a,
                ProcessAnnotation { parsing_ann: ann, ..Default::default() },
                Box::new(go(*body)),
            ),
            Process::Comb(c, ann, l, r) => Process::Comb(
                c,
                ProcessAnnotation { parsing_ann: ann, ..Default::default() },
                Box::new(go(*l)),
                Box::new(go(*r)),
            ),
        }
    }
    go(p)
}

/// Drop the translation annotations and recover the parsed-stage form.
pub fn to_parsed<V>(
    p: Process<ProcessAnnotation<V>, SapicLVar>,
) -> Process<ProcessParsedAnnotation, SapicLVar> {
    match p {
        Process::Null(ann) => Process::Null(ann.parsing_ann),
        Process::Action(a, ann, body) => {
            Process::Action(a, ann.parsing_ann, Box::new(to_parsed(*body)))
        }
        Process::Comb(c, ann, l, r) => Process::Comb(
            c,
            ann.parsing_ann,
            Box::new(to_parsed(*l)),
            Box::new(to_parsed(*r)),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tamarin_term::lterm::{LSort, LVar};

    type V = LVar;

    #[test]
    fn empty_annotation_default_else_branch_is_true() {
        let a: ProcessAnnotation<V> = ProcessAnnotation::empty();
        assert!(a.else_branch);
        assert!(a.lock.is_none());
    }

    #[test]
    fn append_or_left_for_options() {
        let v1 = LVar::new("a", LSort::Msg, 0);
        let v2 = LVar::new("b", LSort::Msg, 0);
        let a = ProcessAnnotation::<V>::with_lock(v1.clone());
        let b = ProcessAnnotation::<V>::with_lock(v2);
        let c = a.append(b);
        // Haskell's `Maybe` semigroup uses `<>`-of-Just, but the
        // ProcessAnnotation impl uses `Maybe`'s default (first-Just-wins
        // via `or`). Verify our convention.
        assert_eq!(c.lock.map(|AnVar(v)| v), Some(v1));
    }

    #[test]
    fn round_trip_to_annotated_and_back() {
        let parsed: Process<ProcessParsedAnnotation, SapicLVar> = Process::Null(
            ProcessParsedAnnotation::default(),
        );
        let annotated: Process<ProcessAnnotation<V>, SapicLVar> = to_annotated(parsed.clone());
        let back = to_parsed(annotated);
        assert_eq!(parsed, back);
    }
}
