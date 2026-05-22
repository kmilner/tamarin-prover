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
  ) where

import           Control.Monad.Disj            (MonadDisj, contradictoryIf)
import qualified Data.Map                      as M
import qualified Data.Set                      as S
import           Debug.Trace                   (trace, traceM)
import qualified Extension.Data.Label          as L
import           System.IO.Unsafe              (unsafePerformIO)
import qualified System.Environment            as SysEnv

import           Theory.Constraint.System


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
        () <- trace ("[SUBPASS] enter " ++ label) (return ())
        r <- m
        () <- trace ("[SUBPASS] exit  " ++ label) (return ())
        return r
    | otherwise = m
{-# INLINE tracePassPair #-}


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
traceExecM :: Monad m => String -> m ()
traceExecM label
    | flagExec  = (trace ("[EXEC] " ++ label) (return ()) :: Monad m => m ())
    | otherwise = return ()
{-# INLINE traceExecM #-}


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
