//! Surface-syntax AST for `.spthy` files.

use std::fmt;

// =============================================================================
// Top-level theory
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Theory {
    pub is_diff: bool,
    pub name: String,
    pub configuration: Option<String>,
    pub items: Vec<TheoryItem>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TheoryItem {
    Builtins(Vec<String>),
    Functions(Vec<FunctionDecl>),
    Equations { convergent: bool, eqs: Vec<Equation> },
    Macros(Vec<Macro>),
    Predicates(Vec<Predicate>),
    Options(Vec<String>),
    Heuristic(String),
    Tactic(Tactic),
    Restriction(Restriction),
    LegacyAxiom(Restriction),
    Rule(Rule),
    IntrRule(Rule),
    Lemma(Lemma),
    DiffLemma(DiffLemma),
    AccLemma(AccLemma),
    CaseTest(CaseTest),
    ProcessDef(ProcessDef),
    TopLevelProcess(Process),
    EquivLemma(Process, Process),
    DiffEquivLemma(Process),
    Export { tag: String, body: String },
    FormalComment { header: String, body: String },
    IfDef { cond: FlagFormula, then_items: Vec<TheoryItem>, else_items: Option<Vec<TheoryItem>> },
    Define(String),
    Include(String),
}

// =============================================================================
// Functions / equations / macros / predicates / restrictions
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDecl {
    pub name: String,
    pub arg_types: Vec<Option<String>>,
    pub out_type: Option<String>,
    pub private: bool,
    pub destructor: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Equation {
    pub lhs: Term,
    pub rhs: Term,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
    pub name: String,
    pub args: Vec<VarSpec>,
    pub body: Term,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Predicate {
    pub fact: Fact,
    pub formula: Formula,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Restriction {
    pub name: String,
    pub formula: Formula,
    pub attributes: Vec<RestrictionAttr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RestrictionAttr {
    LeftRestriction,
    RightRestriction,
}

// =============================================================================
// Rules
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Rule {
    pub name: String,
    pub modulo: Option<String>, // E or AC
    pub attributes: Vec<RuleAttr>,
    pub let_block: Vec<LetBinding>,
    pub premises: Vec<Fact>,
    pub actions: Vec<Fact>,
    pub conclusions: Vec<Fact>,
    pub embedded_restrictions: Vec<Formula>,
    pub variants: Vec<Rule>,
    pub left_right: Option<(Box<Rule>, Box<Rule>)>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RuleAttr {
    Color(String),
    Process(String),
    NoDerivCheck,
    Role(String),
    IsSapicRule,
    External(String, Option<String>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetBinding {
    pub var: Term, // pattern
    pub value: Term,
}

// =============================================================================
// Lemmas / accountability / case tests / proof skeletons
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Lemma {
    pub name: String,
    pub modulo: Option<String>,
    pub attributes: Vec<LemmaAttr>,
    pub trace_quantifier: TraceQuantifier,
    pub formula: Formula,
    pub proof: Option<ProofSkeleton>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DiffLemma {
    pub name: String,
    pub attributes: Vec<LemmaAttr>,
    pub proof: Option<ProofSkeleton>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AccLemma {
    pub name: String,
    pub attributes: Vec<LemmaAttr>,
    pub formula: Formula,
    pub case_test_idents: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseTest {
    pub name: String,
    pub formula: Formula,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TraceQuantifier {
    AllTraces,
    ExistsTrace,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LemmaAttr {
    Sources,
    Reuse,
    DiffReuse,
    UseInduction,
    HideLemma(String),
    Heuristic(String),
    Output(Vec<String>),
    Left,
    Right,
    Hint(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ProofSkeleton {
    pub raw: String,
}

// =============================================================================
// Tactics
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Tactic {
    pub name: String,
    pub raw: String,
}

// =============================================================================
// Processes (SAPIC)
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct ProcessDef {
    pub name: String,
    pub vars: Option<Vec<VarSpec>>,
    pub body: Process,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Process {
    Null,
    Action {
        action: SapicAction,
        body: Box<Process>,
    },
    Comb {
        comb: ProcessComb,
        left: Box<Process>,
        right: Box<Process>,
    },
    Replication(Box<Process>),
    /// Process called by name (with optional argument list).
    Call { name: String, args: Vec<Term> },
    /// (...) @ term — annotation
    AtAnnotation(Box<Process>, Term),
}

#[derive(Debug, Clone, PartialEq)]
pub enum SapicAction {
    New(VarSpec),
    Insert(Term, Term),
    Delete(Term),
    ChIn { chan: Option<Term>, msg: Term },
    ChOut { chan: Option<Term>, msg: Term },
    Lock(Term),
    Unlock(Term),
    Event(Fact),
    /// embedded MSR rule
    Msr { prems: Vec<Fact>, acts: Vec<Fact>, concs: Vec<Fact>, restrictions: Vec<Formula> },
}

#[derive(Debug, Clone, PartialEq)]
pub enum ProcessComb {
    Parallel,
    Ndc,
    /// `if cond then ... else ...`
    Cond(Condition),
    /// `lookup t as v in ... else ...`
    Lookup(Term, VarSpec),
    /// `let pat = t in ... else ...`
    Let { pat: Term, value: Term },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Condition {
    Eq(Term, Term),
    Formula(Formula),
}

// =============================================================================
// Facts
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub struct Fact {
    pub persistent: bool,
    pub name: String,
    pub args: Vec<Term>,
    pub annotations: Vec<FactAnnotation>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FactAnnotation {
    SolveFirst,
    SolveLast,
    NoSources,
}

// =============================================================================
// Formulas
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Formula {
    False,
    True,
    Atom(Atom),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    Forall(Vec<VarSpec>, Box<Formula>),
    Exists(Vec<VarSpec>, Box<Formula>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Atom {
    Eq(Term, Term),
    Less(Term, Term),       // tp < tp
    LessMset(Term, Term),   // t (<) t
    Subterm(Term, Term),
    /// `F @ t`
    Action(Fact, Term),
    /// `last(t)`
    Last(Term),
    /// predicate (parsed as fact)
    Pred(Fact),
}

// =============================================================================
// Terms
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Var(VarSpec),
    PubLit(String),    // 'foo'
    FreshLit(String),  // ~'n'
    NatLit(String),    // %'n'
    Number(u64),       // bare integer literal (e.g. for %+)
    NumberOne,         // 1
    NatOne,            // 1:nat / %1
    DhNeutral,
    /// Function or operator application by name.
    App(String, Vec<Term>),
    /// `op{arg1}arg2` algebraic syntax.
    AlgApp(String, Box<Term>, Box<Term>),
    /// Pair / tuple `<a, b, c>` (right-associative).
    Pair(Vec<Term>),
    /// `diff(a, b)`
    Diff(Box<Term>, Box<Term>),
    /// AC binary operations (left-associative).
    BinOp(BinOp, Box<Term>, Box<Term>),
    /// SAPIC pattern-match syntax `=t`: literal-match the inner term rather
    /// than bind it.
    PatMatch(Box<Term>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Exp,    // ^
    Mult,   // *
    Union,  // + or ++
    Xor,    // XOR or ⊕
    NatPlus,// %+
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarSpec {
    pub name: String,
    pub idx: u64,
    pub sort: SortHint,
    pub typ: Option<String>, // SAPIC type annotation
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SortHint {
    Msg,
    Pub,    // $x
    Fresh,  // ~x
    Node,   // #x
    Nat,    // %x
    /// Sort given by suffix `: msg | : pub | : fresh | : node | : nat`.
    Suffix(SuffixSort),
    /// No sort hint: bare identifier, sort to be inferred.
    Untagged,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SuffixSort { Msg, Pub, Fresh, Node, Nat }

impl Default for SortHint {
    fn default() -> Self { SortHint::Untagged }
}

// =============================================================================
// Flag formulas (for #ifdef)
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum FlagFormula {
    Atom(String),
    Not(Box<FlagFormula>),
    And(Box<FlagFormula>, Box<FlagFormula>),
    Or(Box<FlagFormula>, Box<FlagFormula>),
}

// =============================================================================
// Pretty
// =============================================================================

impl fmt::Display for Theory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "theory {}", self.name)?;
        if let Some(c) = &self.configuration {
            write!(f, " configuration: {:?}", c)?;
        }
        writeln!(f, " (items: {})", self.items.len())?;
        Ok(())
    }
}
