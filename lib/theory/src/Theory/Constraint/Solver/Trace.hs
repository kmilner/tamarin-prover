{-# LANGUAGE FlexibleContexts #-}
-- |
-- Reusable Haskell-side tracing infrastructure for solver investigations
-- against the Rust port.
--
-- All trace points are env-var-gated, so they have zero overhead when
-- flags are unset.  Flags:
--
--   TAM_HS_TRACE_CONTRA  — every `contradictoryIfT` call: site label,
--                          whether it fired, plus a one-line system summary
--                          when it does fire.  This is the workhorse for
--                          locating "which simplify-time contradiction
--                          Haskell catches that the Rust port misses".
--
--   TAM_HS_TRACE_SIMPLIFY — entry/exit of each simplify pass (which CR-rule)
--                           and the size of the system before/after.
--
--   TAM_HS_TRACE_CASES — every case kept/dropped by `process` in
--                        execProofMethod: case name, whether it survived
--                        runReduction (i.e. wasn't mzero'd), final case
--                        count after `distinguish`.
--
--   TAM_HS_TRACE_SOURCES — case-name list per source after each
--                          saturateSources iteration.  Used to diagnose
--                          source-case overenumeration (e.g. denning_sacco
--                          Initiator2_case_N cluster).
--
--   TAM_HS_TRACE_CHAINS — every `solveChain` invocation: chain conc,
--                         destructor rule attempted, branch outcome
--                         (direct-edge close vs destructor extend).
--                         Used to pin down chain-extension branching
--                         factor for #164.
--
--   TAM_HS_TRACE_EXEC — synchronized exec-trace at major solver entry
--                       points (solveGoal, solveChain, exploitPrems,
--                       simplifySystem, insertEdges, solveTermEqs,
--                       applyEqStore, someRuleACInst, FrNarrow).
--                       Designed to diff against TAM_RS_TRACE_EXEC for
--                       identifying the FIRST execution-trace divergence
--                       between Rust and Haskell.  Output format:
--                       `[EXEC] <function> <canonical-data>` — one line
--                       per call, no sequence numbers (so the diff isn't
--                       dominated by counter drift), data is normalized
--                       to suppress fresh-var index variation.
--
-- Usage in code:
--
--   import qualified Theory.Constraint.Solver.Trace as T
--   T.contradictoryIfT "enforceEdgeUniqueness:premIdxMismatch" cond
--   T.traceExec ("solveChain ENTER")
--
-- The label should be specific enough to identify the call site in the
-- log output.
module Theory.Constraint.Solver.Trace (
    contradictoryIfT
  , tracePass
  , tracePassPair
  , traceCase
  , traceExec
  , traceExecM
  , dumpSystemSummary
  , flagContra
  , flagSimplify
  , flagCases
  , flagSources
  , flagChains
  , flagExec
  , flagSourcesLeaf
  , flagApplySrc
  , flagState
  , traceStateM
  , tracePickM
  , setCasePath
  , getCasePath
  , casePathString
  , traceFormM
  , guardedRepr
  , traceProveEntry
  ) where

import           Control.Monad.Disj            (MonadDisj, contradictoryIf)
import           Data.List                     (intercalate, sort)
import qualified Data.Map                      as M
import qualified Data.Set                      as S
import qualified Data.IORef                    as IORef
import           Debug.Trace                   (trace, traceM, traceIO)
import qualified Extension.Data.Label          as L
import           System.IO.Unsafe              (unsafePerformIO)
import qualified System.Environment            as SysEnv

import           Term.Substitution             (substToList, substToListVFresh)
import           Theory.Constraint.System
import           Theory.Constraint.System.Constraints
                                                (Goal(..))
import           Theory.Constraint.System.Guarded
                                                (LNGuarded, Guarded(..))
import           Logic.Connectives             (getDisj, getConj)
import           Theory.Model
                  (LNFact, Fact(..), FactTag(..), showRuleCaseName, rActs)


-- | Read an env var at module load time (cached via NOINLINE so the
-- unsafePerformIO fires exactly once per program run).
flagContra :: Bool
flagContra = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_CONTRA"
{-# NOINLINE flagContra #-}

flagSimplify :: Bool
flagSimplify = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_SIMPLIFY"
{-# NOINLINE flagSimplify #-}

flagCases :: Bool
flagCases = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_CASES"
{-# NOINLINE flagCases #-}

flagSources :: Bool
flagSources = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_SOURCES"
{-# NOINLINE flagSources #-}

flagChains :: Bool
flagChains = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_CHAINS"
{-# NOINLINE flagChains #-}

flagExec :: Bool
flagExec = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_EXEC"
{-# NOINLINE flagExec #-}

-- TAM_HS_TRACE_SOURCES_LEAF: dump per-leaf state in solveAllSafeGoals.
-- Each time `solve` returns `caseNames` (no safe goal remains),
-- one line is printed: `[LEAF] cn=... chains=... nodes=... goals=...`.
-- Used to count actual leaves in HS's Disj-monad tree for comparison
-- with Rust's `close_chains_dfs` closure count.
flagSourcesLeaf :: Bool
flagSourcesLeaf = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_SOURCES_LEAF"
{-# NOINLINE flagSourcesLeaf #-}

-- TAM_HS_TRACE_STATE: dump a canonical system-state line before each
-- `solveGoal` dispatch in ProofMethod.solve.  Format-matched against
-- Rust's `TAM_RS_TRACE_STATE` output (see
-- `rust/crates/tamarin-theory/src/constraint/solver/trace.rs`) so the
-- two logs can be diffed side-by-side to find the FIRST system-state
-- divergence between the implementations.
--
-- Line shape:
--   [STATE] nodes=[<RuleName×N, ...>] goals=[<Kind(head), ...>] formulas=N solved_formulas=M
--
-- - `nodes`: sorted, count-compressed rule-case-name list.  Var idxs
--   suppressed so two structurally-identical systems compare equal
--   across HS/Rust idx allocation drift.
-- - `goals`: sorted list of UNSOLVED goal kinds + canonical fact heads.
--   Use the same `factCanonical` style as `goalKind` (Goals.hs:218-234).
-- - `formulas`/`solved_formulas`: counts only.  Full bodies elided to
--   keep the line readable; depth dumps available via TAM_HS_TRACE_SIMP.
--
-- Reusable for any future state-divergence investigation: enable the
-- env vars on both sides, run the same theory, diff the outputs.
flagState :: Bool
flagState = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_STATE"
{-# NOINLINE flagState #-}

-- TAM_HS_TRACE_STATE_FULL: like TAM_HS_TRACE_STATE but additionally emits
-- a [STATE_FULL] line with FULL action terms (var idxs suppressed) so
-- HS-vs-Rust diffs can see exactly which actions each side has at the
-- divergent state.  Mirrors Rust's TAM_RS_TRACE_STATE_FULL.
flagStateFull :: Bool
flagStateFull = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_STATE_FULL"
{-# NOINLINE flagStateFull #-}

-- TAM_HS_TRACE_STATE_EQS: emit a [STATE_EQS] line containing the
-- canonical eq_store substitution at each [STATE] checkpoint.
-- Mirrors Rust's TAM_RS_TRACE_STATE_EQS.  Used to find the first
-- divergent eq-store binding between the implementations.  Idxs
-- suppressed so the diff catches semantic divergences rather than
-- idx-allocation drift.
flagStateEqs :: Bool
flagStateEqs = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_STATE_EQS"
{-# NOINLINE flagStateEqs #-}

-- TAM_HS_TRACE_APPLY_SRC: dump per-application of a precomputed source
-- case in `_applySource`.  For each `(goal, case)` pair, emit:
--   [APPLY_SRC] path=<casePath> goal=<goal> case=<names>
--   [APPLY_SRC]   keep=<keepVarBindings>
--   [APPLY_SRC]   freshBefore=<global counter>
--   [APPLY_SRC]   preFrees=<frees of sysTh0 in traversal order>
--   [APPLY_SRC]   freshAfter=<global counter>
--   [APPLY_SRC]   postFrees=<frees of sysTh in traversal order>
-- Used to bisect the KAS_key_secrecy divergence (idx-allocation order
-- between HS's someInst+importBinding and Rust's freshen_system_keep).
flagApplySrc :: Bool
flagApplySrc = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_APPLY_SRC"
{-# NOINLINE flagApplySrc #-}

-- | Global mutable proof-tree case-name path.  Driver code
-- (`proveSystemDFS`) sets this before each `prove` call so the trace
-- knows which proof-tree position is being evaluated.  Because the
-- proof tree is built lazily, we MUST set this immediately before
-- forcing the system at each level — see Theory.Proof.proveSystemDFS
-- for the wiring.
casePathRef :: IORef.IORef [String]
casePathRef = unsafePerformIO (IORef.newIORef [])
{-# NOINLINE casePathRef #-}

setCasePath :: [String] -> IO ()
setCasePath p = IORef.writeIORef casePathRef p

getCasePath :: IO [String]
getCasePath = IORef.readIORef casePathRef

casePathString :: [String] -> String
casePathString xs =
    let nonEmpty = filter (not . null) xs
    in if null nonEmpty then "/" else "/" ++ intercalate "/" nonEmpty


-- | Drop-in replacement for `contradictoryIf` with a site label.  When
-- `TAM_HS_TRACE_CONTRA=1` and the condition fires (i.e. the case is
-- about to be mzero'd), prints `[CONTRA-FIRE] <label>` so we can see
-- exactly which simplify-time contradiction caught the case.
--
-- When the condition is False (no contradiction), nothing is printed
-- (would be too noisy — every solveFactEqs would log).
contradictoryIfT :: MonadDisj m => String -> Bool -> m ()
contradictoryIfT label cond
    | cond && flagContra = traceM ("[CONTRA-FIRE] " ++ label) >> contradictoryIf cond
    | otherwise          = contradictoryIf cond
{-# INLINE contradictoryIfT #-}


-- | Trace entry to a simplify pass, returning the result unchanged.
-- The `before` System is used to compute a one-line summary; the result
-- is the System after the pass.
tracePass :: String -> a -> a
tracePass label x
    | flagSimplify = trace ("[PASS] " ++ label) x
    | otherwise    = x
{-# INLINE tracePass #-}


-- | Wrap a monadic action with `[SUBPASS] enter/exit <label>` traces gated
-- on `TAM_HS_TRACE_SIMPLIFY=1`.  Use this around each subpass inside
-- `simplifySystem`'s go-loop: if the action mzero's mid-pass, the `exit`
-- trace does NOT fire, so a per-pass enter/exit count mismatch identifies
-- exactly which CR-rule killed the case.
tracePassPair :: Monad m => String -> m a -> m a
tracePassPair label m
    | flagSimplify = do
        traceM ("[SUBPASS] enter " ++ label)
        r <- m
        traceM ("[SUBPASS] exit  " ++ label)
        return r
    | otherwise = m
{-# NOINLINE tracePassPair #-}


-- | Trace a case-survival decision in `process` (execProofMethod).
-- Called with the case name and whether it survived `runReduction`.
traceCase :: String -> Bool -> a -> a
traceCase name kept x
    | flagCases = trace ("[CASE] " ++ name ++ " kept=" ++ show kept) x
    | otherwise = x
{-# INLINE traceCase #-}


-- | `traceExec label x` returns x; when `TAM_HS_TRACE_EXEC=1`, also
-- emits `[EXEC] <label>` to stderr.  Use at major function entries
-- so the trace can be diffed against the Rust port's equivalent
-- `TAM_RS_TRACE_EXEC` output to find the first execution-trace
-- divergence.
--
-- Format `[EXEC] <function-name> <canonical-data>` — keep `label` in
-- the same form on both sides for the diff to be meaningful.  Avoid
-- including fresh indices, node ids, or other counters that differ
-- between implementations.
traceExec :: String -> a -> a
traceExec label x
    | flagExec  = trace ("[EXEC] " ++ label) x
    | otherwise = x
{-# INLINE traceExec #-}


-- | Monadic version of `traceExec` — emits the trace as a side effect.
-- Uses Debug.Trace.traceM directly.  Note: the previous
-- unsafePerformIO+hPutStrLn variant produced interleaved characters
-- because hPutStrLn isn't atomic under lazy evaluation order.
traceExecM :: Applicative m => String -> m ()
traceExecM label
    | flagExec  = traceM ("[EXEC] " ++ label)
    | otherwise = pure ()
{-# NOINLINE traceExecM #-}


-- | One-line summary of a System for trace output.  Captures sizes so
-- we can correlate the system state with the contradiction firing
-- without flooding the log.
dumpSystemSummary :: System -> String
dumpSystemSummary sys =
    "nodes=" ++ show (M.size (L.get sNodes sys)) ++
    " edges=" ++ show (S.size (L.get sEdges sys)) ++
    " less=" ++ show (S.size (L.get sLessAtoms sys)) ++
    " goals=" ++ show (M.size (L.get sGoals sys)) ++
    " formulas=" ++ show (S.size (L.get sFormulas sys))

-- | Emit a `[STATE]` line summarising the system state.  Format-matched
-- against Rust's `TAM_RS_TRACE_STATE` output (see
-- `rust/crates/tamarin-theory/src/constraint/solver/trace.rs::trace_state`)
-- so the two logs can be diffed side-by-side to find the FIRST
-- system-state divergence between the implementations.
--
-- Reusable: enable `TAM_HS_TRACE_STATE=1` (HS) + `TAM_RS_TRACE_STATE=1`
-- (Rust) on the same theory, then `diff` the stderr outputs.
--
-- Line format:
--
--   [STATE] nodes=[<RuleName×N, ...>] goals=[<Kind(head), ...>] formulas=N solved_formulas=M
--
-- - `nodes`: sorted, count-compressed list of rule-case-names.  Var idxs
--   are suppressed so two structurally-identical systems compare equal
--   across HS/Rust idx allocation drift.
-- - `goals`: sorted list of UNSOLVED goal kinds + canonical fact heads,
--   following `goalKind`'s `factCanonical` shape (Goals.hs:218-234).
-- - `formulas`/`solved_formulas`: counts only.  Full bodies elided to
--   keep the line readable; depth dumps available via other flags.
traceStateM :: Monad m => System -> m ()
traceStateM sys
    | flagState = do
        let path = unsafePerformIO getCasePath
        traceM ("[STATE] path=" ++ casePathString path
              ++ " nodes=" ++ canonicalNodes sys
              ++ " goals=" ++ canonicalOpenGoals sys
              ++ " formulas=" ++ show (S.size (L.get sFormulas sys))
              ++ " solved_formulas=" ++ show (S.size (L.get sSolvedFormulas sys)))
        if flagStateFull
            then do
                traceM ("[STATE_FULL] node_actions=" ++ canonicalNodeActions sys)
                traceM ("[STATE_FULL] open_actions=" ++ canonicalOpenActions sys)
            else pure ()
        if flagStateEqs
            then do
                traceM ("[STATE_EQS] path=" ++ casePathString path
                  ++ " subst=" ++ canonicalEqStoreSubst sys
                  ++ " conj=" ++ show (length (L.get sConjDisjEqs sys)))
                -- Per-disjunct subst dump (mirrors Rust's
                -- `[STATE_EQS]   disj[di].subst[si]=SplitId(N) [...]`).
                -- Each subst is dumped as a list of `name.idx/sort→term`
                -- pairs WITH idxs preserved so HS↔Rust can cross-diff
                -- the exact `~ltkA.0 → ~lkR.X` collapse entries.
                let dumpDisj di (sid, sset) =
                        mapM_ (\(si, s) ->
                            traceM ("[STATE_EQS]   disj[" ++ show di
                                ++ "].subst[" ++ show si
                                ++ "]=SplitId(" ++ show sid ++ ") "
                                ++ show (substToListVFresh s)))
                            (zip [(0::Int)..] (S.toList sset))
                mapM_ (\(di, x) -> dumpDisj di x)
                      (zip [(0::Int)..] (getConj (L.get sConjDisjEqs sys)))
            else pure ()
        if flagStateForms
            then do
                let formulas = S.toList (L.get sFormulas sys)
                    solved   = S.toList (L.get sSolvedFormulas sys)
                mapM_ (\(i, f) -> traceM ("[STATE_FORM] path=" ++ casePathString path
                                       ++ " formulas[" ++ show i ++ "]=" ++ show f))
                      (zip [(0::Int)..] formulas)
                mapM_ (\(i, f) -> traceM ("[STATE_FORM] path=" ++ casePathString path
                                       ++ " solved[" ++ show i ++ "]=" ++ show f))
                      (zip [(0::Int)..] solved)
            else pure ()
        if flagStateNodes
            then do
                -- Dump each node with full rule name + actions + var idxs
                -- preserved.  Used for chain-depth diff: Rust↔HS may
                -- merge differently, producing different action levels
                -- (e.g. Loop(~n, f(k.1), kOrig) vs Loop(~n, f(f(k.1)),
                -- kOrig)) — Helper_Loop_and_success root cause.
                mapM_ (\(i, ru) -> traceM ("[STATE_NODE] path=" ++ casePathString path
                                        ++ " " ++ show i ++ "=" ++ showRuleCaseName ru
                                        ++ " actions=" ++ show (L.get rActs ru)))
                      (M.toList (L.get sNodes sys))
                mapM_ (\e -> traceM ("[STATE_EDGE] path=" ++ casePathString path
                                  ++ " " ++ show e))
                      (S.toList (L.get sEdges sys))
                -- Less atoms and last_atom — drive Cyclic contradiction
                -- detection.  Mirrors Rust's [STATE_LESS] / [STATE_LAST].
                mapM_ (\l -> traceM ("[STATE_LESS] path=" ++ casePathString path
                                  ++ " " ++ show l))
                      (S.toList (L.get sLessAtoms sys))
                case L.get sLastAtom sys of
                    Just la -> traceM ("[STATE_LAST] path=" ++ casePathString path
                                    ++ " last=" ++ show la)
                    Nothing -> pure ()
            else pure ()
    | otherwise = pure ()
{-# NOINLINE traceStateM #-}

-- TAM_HS_TRACE_STATE_FORMS: emit `[STATE_FORM]` lines dumping the
-- FULL guarded-formula content of sFormulas / sSolvedFormulas at each
-- [STATE] checkpoint.  Mirrors Rust's TAM_RS_TRACE_STATE_FORMS for
-- pin-pointing which specific formula(s) are missing on one side when
-- the counts diverge.
flagStateForms :: Bool
flagStateForms = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_STATE_FORMS"
{-# NOINLINE flagStateForms #-}

-- TAM_HS_TRACE_STATE_NODES: emit `[STATE_NODE]` + `[STATE_EDGE]` lines
-- dumping each node (rule name, actions with var idxs preserved) and
-- each edge.  Mirrors Rust's TAM_RS_TRACE_STATE_NODES for pin-pointing
-- chain-depth divergences (e.g. Helper_Loop_and_success: HS has Loop
-- chain ~n → k.1 → f(k.1) → f(f(k.1)); Rust merges to 2 levels only).
flagStateNodes :: Bool
flagStateNodes = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_STATE_NODES"
{-# NOINLINE flagStateNodes #-}

-- | Emit a [PICK] line showing which goal was picked at this dispatch.
-- Paired with Rust's `TAM_RS_TRACE_STATE=1` emission for goal-ranking
-- divergence diagnosis.  Use AFTER `traceStateM sys` so the [PICK]
-- attaches to the [STATE] line just emitted.
tracePickM :: Applicative m => Goal -> m ()
tracePickM g
    | flagState = traceM ("[PICK] " ++ goalCanonical g)
    | otherwise = pure ()
{-# NOINLINE tracePickM #-}

-- | TAM_HS_TRACE_FORM=1: emit `[FORMULA_ADD] path=... kind=... <repr>`
-- whenever a guarded formula is inserted into sFormulas / DisjG goal.
-- Pairs with Rust's `TAM_RS_TRACE_FORM` to find insertion divergences.
flagForm :: Bool
flagForm = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_FORM"
{-# NOINLINE flagForm #-}

traceFormM :: Monad m => String -> LNGuarded -> m ()
traceFormM kind fm
    | flagForm = do
        let path = unsafePerformIO getCasePath
        traceM ("[FORMULA_ADD] path=" ++ casePathString path
              ++ " kind=" ++ kind ++ " " ++ guardedRepr fm)
    | otherwise = pure ()
{-# NOINLINE traceFormM #-}

-- | Unconditional state-emission at proveSystemDFS::prove entry.
-- Mirrors the [STATE] format from `traceStateM` but doesn't go through
-- the ProofMethod.solve path — so EVERY proof-tree position gets
-- traced, not just SolveGoal dispatches.  Required for branch-aware
-- lockstep with Rust which also traces every `expand` call.
traceProveEntry :: [String] -> System -> IO ()
traceProveEntry path sys
    | flagState = do
        traceIO ("[STATE] path=" ++ casePathString path
              ++ " nodes=" ++ canonicalNodes sys
              ++ " goals=" ++ canonicalOpenGoals sys
              ++ " formulas=" ++ show (S.size (L.get sFormulas sys))
              ++ " solved_formulas=" ++ show (S.size (L.get sSolvedFormulas sys)))
        if flagGoalsAll
            then traceIO ("[STATE_GOALS_ALL] path=" ++ casePathString path
                  ++ " goals=" ++ allGoalsCanonical sys)
            else pure ()
    | otherwise = pure ()
{-# NOINLINE traceProveEntry #-}

-- | TAM_HS_TRACE_GOALS_ALL=1 dumps ALL goals (incl. solved + DisjG) with
-- solved status — for diagnosing where Disj goals end up after HS's
-- combineGoalStatus merges or markGoalAsSolved removes them.
flagGoalsAll :: Bool
flagGoalsAll = unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_GOALS_ALL"
{-# NOINLINE flagGoalsAll #-}

allGoalsCanonical :: System -> String
allGoalsCanonical sys =
    let pairs = M.toList (L.get sGoals sys)
        rendered = [ goalDetailed g ++ "[solved=" ++ show (L.get gsSolved gs) ++ "]"
                   | (g, gs) <- pairs ]
    in "[" ++ intercalate "," rendered ++ "]"

-- | Detailed goal renderer (full content) — for full-fidelity sGoals
-- dump when investigating HS's Disj-key merging behaviour.
goalDetailed :: Goal -> String
goalDetailed g = case g of
    ActionG  _ fa -> "Action(" ++ factCanonical fa ++ ")"
    PremiseG _ fa -> "Premise(" ++ factCanonical fa ++ ")"
    ChainG _ _    -> "Chain"
    SplitG _      -> "Split"
    DisjG d       -> "DisjG{" ++ show d ++ "}"
    SubtermG _    -> "Subterm"

-- | Canonicalized Guarded formula renderer matching Rust's `guarded_repr`.
-- Includes the full `show`-rendered atoms / quantifier bodies so two
-- alpha-distinct or instantiation-distinct firings can be compared
-- structurally across HS and Rust.
guardedRepr :: LNGuarded -> String
guardedRepr fm = case fm of
    GAto a -> "Atom(" ++ show a ++ ")"
    GConj items -> "Conj[" ++ intercalate "," (map guardedRepr (getConj items)) ++ "]"
    GDisj items -> "Disj[" ++ intercalate "|" (map guardedRepr (getDisj items)) ++ "]"
    GGuarded q ss gs body ->
        show q ++ show (length ss) ++ "v["
            ++ intercalate "," (map show gs) ++ "]("
            ++ guardedRepr body ++ ")"

canonicalNodes :: System -> String
canonicalNodes sys =
    compressDups $ sort $ map (showRuleCaseName . snd) $ M.toList $ L.get sNodes sys

canonicalOpenGoals :: System -> String
canonicalOpenGoals sys =
    let pairs = M.toList (L.get sGoals sys)
        unsolved = [ g | (g, gs) <- pairs, not (L.get gsSolved gs) ]
        digests  = sort (map goalCanonical unsolved)
    in "[" ++ intercalate "," digests ++ "]"

goalCanonical :: Goal -> String
goalCanonical g = case g of
    ActionG _ fa  -> "Action(" ++ factCanonical fa ++ ")"
    PremiseG _ fa -> "Premise(" ++ factCanonical fa ++ ")"
    ChainG _ _    -> "Chain"
    SplitG _      -> "Split"
    DisjG d       -> "Disj[" ++ intercalate "|" (map guardedHead (getDisj d)) ++ "]"
    SubtermG _    -> "Subterm"

-- | Canonical short rendering of a fact's tag + arity.  Suppresses
-- term content entirely; the goal-set count and tag distribution are
-- sufficient for the lockstep-state diff.  If a finer-grained head
-- comparison becomes necessary, extend with `viewTerm` matching
-- (mirror `goalKind` in Goals.hs:218-234).
factCanonical :: LNFact -> String
factCanonical (Fact tag _ ts) =
    showFactTag tag ++ "/" ++ show (length ts)
  where
    showFactTag KUFact            = "KU"
    showFactTag KDFact            = "KD"
    showFactTag FreshFact         = "Fr"
    showFactTag OutFact           = "Out"
    showFactTag InFact            = "In"
    showFactTag (ProtoFact _ n _) = n

guardedHead :: LNGuarded -> String
guardedHead g = case g of
    GAto _              -> "Atom"
    GConj _             -> "Conj"
    GDisj _             -> "Disj"
    GGuarded q vs _ _   -> show q ++ show (length vs) ++ "v"

compressDups :: [String] -> String
compressDups xs = "[" ++ intercalate "," (go xs) ++ "]"
  where
    go []     = []
    go (y:ys) =
        let (eqs, rest) = span (== y) ys
            n           = 1 + length eqs
        in (if n > 1 then y ++ "\215" ++ show n else y) : go rest

-- | Canonicalize a fact for STATE_FULL output.  Uses HS's `show`
-- on the fact (which renders terms with idxs) and then strips
-- numeric var idx suffixes via a simple regex-style cleanup —
-- enough to make HS / Rust output diff-able after both passes.
--
-- Concretely, after this: `~ni.5:fresh` becomes `~ni:fresh`,
-- `t.3:msg` becomes `t:msg`, etc.  Compound terms remain in their
-- normal HS rendering, just without the `.N` var-idx annotations.
canonicalFactStr :: LNFact -> String
canonicalFactStr fa = stripVarIdxs (show fa)
  where
    -- Strip a `.N` immediately after an identifier (var idx suffix).
    -- Walks the string char-by-char keeping a state machine.
    stripVarIdxs []                = []
    stripVarIdxs ('.' : cs)
        | (digits, rest) <- span (`elem` "0123456789") cs
        , not (null digits)
        = stripVarIdxs rest
    stripVarIdxs (c : cs)           = c : stripVarIdxs cs

canonicalNodeActions :: System -> String
canonicalNodeActions sys =
    let acts = [ canonicalFactStr fa
               | (_, ru) <- M.toList (L.get sNodes sys)
               , fa <- L.get rActs ru ]
    in compressDups (sort acts)

canonicalOpenActions :: System -> String
canonicalOpenActions sys =
    let pairs = M.toList (L.get sGoals sys)
        actions = [ canonicalFactStr fa
                  | (ActionG _ fa, gs) <- pairs
                  , not (L.get gsSolved gs) ]
    in compressDups (sort actions)

-- | Canonical dump of `sys ^. sSubst`: sorted list of `var → term`
-- bindings with var idxs suppressed.  Mirrors Rust's
-- `canonical_eq_store_subst` so the lines diff line-by-line.  Used to
-- find the first divergent eq-store binding between HS and Rust at the
-- same proof-tree path.
canonicalEqStoreSubst :: System -> String
canonicalEqStoreSubst sys =
    let pairs = substToList (L.get sSubst sys)
        entries = sort [ stripVarIdxs (show v ++ "→" ++ show t)
                       | (v, t) <- pairs ]
    in "[" ++ intercalate ", " entries ++ "]"
  where
    -- Reuse the var-idx-stripping logic.
    stripVarIdxs []                = []
    stripVarIdxs ('.' : cs)
        | (digits, rest) <- span (`elem` "0123456789") cs
        , not (null digits)
        = stripVarIdxs rest
    stripVarIdxs (c : cs)           = c : stripVarIdxs cs
