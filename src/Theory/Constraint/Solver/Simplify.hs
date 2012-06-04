{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ViewPatterns       #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- This module implements all rules that do not result in case distinctions
-- and equation solving. Some additional cases may although result from
-- splitting over multiple AC-unifiers. Note that a few of these rules are
-- implemented directly in the methods for inserting constraints to the
-- constraint system.  These methods are provided by
-- "Theory.Constraint.Solver.Reduction".
--
module Theory.Constraint.Solver.Simplify (

  simplifySystem

  ) where

import           Debug.Trace

import           Prelude                            hiding (id, (.))

import qualified Data.DAG.Simple                    as D
import           Data.Data
import           Data.Either                        (partitionEithers)
import qualified Data.Foldable                      as F
import           Data.List
import qualified Data.Map                           as M
import           Data.Monoid                        (Monoid(..))
import qualified Data.Set                           as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Disj
import           Control.Monad.Fresh
import           Control.Monad.Reader
import           Control.Monad.State                (gets)

import           Text.PrettyPrint.Class

import           Extension.Data.Label
import           Extension.Prelude

import           Theory.Constraint.Solver.Goals
import           Theory.Constraint.Solver.Reduction
import           Theory.Constraint.Solver.Types
import           Theory.Constraint.System
import           Theory.Model


-- | Apply CR-rules that don't result in case splitting until the constraint
-- system does not change anymore.
simplifySystem :: Reduction ()
simplifySystem = do
    -- Start simplification, indicating that some change happened
    go (0 :: Int) [Changed]
    -- Add all ordering constraint implied by CR-rule *N6*.
    exploitUniqueMsgOrder
    -- Remove equation split goals that do not exist anymore
    removeSolvedSplitGoals
  where
    go n changes0
      -- We stop as soon as all simplification steps have been run without
      -- reporting any change to the constraint systemm.
      | Unchanged == mconcat changes0 = return ()
      | otherwise                     = do
          -- Store original system for reporting
          se0 <- gets id
          -- Perform one initial substitution. We do not have to consider its
          -- changes as 'substSystem' is idempotent.
          void substSystem
          -- Perform one simplification pass.
          (c1,c2,c3) <- enforceNodeUniqueness
          c4 <- enforceEdgeUniqueness
          c5 <- solveUniqueActions
          c6 <- reduceFormulas
          c7 <- evalFormulaAtoms
          c8 <- insertImpliedFormulas

          -- Report on looping behaviour if necessary
          let changes = [c1, c2, c3, c4, c5, c6, c7, c8]
              traceIfLooping
                | n <= 10   = id
                | otherwise = trace $ render $ vcat
                    [ text "Simplifier iteration" <-> int n <> colon
                    , nest 2 (text (show changes))
                    , nest 2 (prettySystem se0)
                    ]

          traceIfLooping $ go (n + 1) changes


-- | CR-rule *N6*: add ordering constraints between all KU-actions and
-- KD-conclusions.
exploitUniqueMsgOrder :: Reduction ()
exploitUniqueMsgOrder = do
    kdConcs   <- gets (M.fromList . map (\(i, _, m) -> (m, i)) . allKDConcs)
    kuActions <- gets (M.fromList . map (\(i, _, m) -> (m, i)) . allKUActions)
    -- We can add all elements where we have an intersection
    F.mapM_ (uncurry insertLess) $ M.intersectionWith (,) kdConcs kuActions

-- | CR-rules *DG4*, *N5_u*, and *N5_d*: enforcing uniqueness of *Fresh* rule
-- instances, *KU*-actions, and *KD*-conclusions.
--
-- Returns 'Changed' if a change was done.
enforceNodeUniqueness :: Reduction (ChangeIndicator, ChangeIndicator, ChangeIndicator)
enforceNodeUniqueness =
    (,,)
      <$> (merge (const $ return Unchanged) freshRuleInsts)
      <*> (merge (solveRuleEqs SplitNow)    kdConcs)
      <*> (merge (solveFactEqs SplitNow)    kuActions)
  where
    -- *DG4*
    freshRuleInsts se = do
        (i, ru) <- M.toList $ get sNodes se
        guard (isFreshRule ru)
        return (ru, ((), i))  -- no need to merge equal rules

    -- *N5_d*
    kdConcs sys = (\(i, ru, m) -> (m, (ru, i))) <$> allKDConcs sys

    -- *N5_u*
    kuActions se = (\(i, fa, m) -> (m, (fa, i))) <$> allKUActions se

    merge :: Ord b
          => ([Equal a] -> Reduction ChangeIndicator)
             -- ^ Equation solver for 'Equal a'
          -> (System -> [(b,(a,NodeId))])
             -- ^ Candidate selector
          -> Reduction ChangeIndicator                  --
    merge solver candidates = do
        changes <- gets (map mergers . groupSortOn fst . candidates)
        mconcat <$> sequence changes
      where
        mergers []                          = unreachable "enforceUniqueness"
        mergers ((_,(xKeep, iKeep)):remove) =
            mappend <$> solver         (map (Equal xKeep . fst . snd) remove)
                    <*> solveNodeIdEqs (map (Equal iKeep . snd . snd) remove)


-- | CR-rules *DG2_1* and *DG3*: merge multiple incoming edges to all facts
-- and multiple outgoing edges from linear facts.
enforceEdgeUniqueness :: Reduction ChangeIndicator
enforceEdgeUniqueness = do
    se <- gets id
    let edges = S.toList (get sEdges se)
    (<>) <$> mergeNodes eSrc eTgt edges
         <*> mergeNodes eTgt eSrc (filter (proveLinearConc se . eSrc) edges)
  where
    -- | @proveLinearConc se (v,i)@ tries to prove that the @i@-th
    -- conclusion of node @v@ is a linear fact.
    proveLinearConc se (v, i) =
        maybe False (isLinearFact . (get (rConc i))) $
            M.lookup v $ get sNodes se

    -- merge the nodes on the 'mergeEnd' for edges that are equal on the
    -- 'compareEnd'
    mergeNodes mergeEnd compareEnd edges
      | null eqs  = return Unchanged
      | otherwise = do
            -- all indices of merged premises and conclusions must be equal
            contradictoryIf (not $ and [snd l == snd r | Equal l r <- eqs])
            -- nodes must be equal
            solveNodeIdEqs $ map (fmap fst) eqs
      where
        eqs = concatMap (merge mergeEnd) $ groupSortOn compareEnd edges

        merge _    []            = error "exploitEdgeProps: impossible"
        merge proj (keep:remove) = map (Equal (proj keep) . proj) remove

-- | Special version of CR-rule *S_at*, which is only applied to solve actions
-- that are guaranteed not to result in case splits.
solveUniqueActions :: Reduction ChangeIndicator
solveUniqueActions = do
    rules       <- nonSilentRules <$> askM pcRules
    actionAtoms <- gets unsolvedActionAtoms

    -- FIXME: We might cache the result of this static computation in the
    -- proof-context, e.g., in the 'ClassifiedRules'.
    let uniqueActions = [ x | [x] <- group (sort ruleActions) ]
        ruleActions   = [ (tag, length ts)
                        | ru <- rules, Fact tag ts <- get rActs ru ]

        isUnique (Fact tag ts) = (tag, length ts) `elem` uniqueActions

        trySolve (i, fa)
          | isUnique fa = solveGoal (ActionG i fa) >> return Changed
          | otherwise   = return Unchanged

    mconcat <$> mapM trySolve actionAtoms

-- | Reduce all formulas as far as possible. See 'insertFormula' for the
-- CR-rules exploited in this step. Note that this step is normally only
-- required to decompose the formula in the initial constraint system.
reduceFormulas :: Reduction ChangeIndicator
reduceFormulas = do
    formulas <- getM sFormulas
    applyChangeList $ do
        fm <- S.toList formulas
        guard (reducibleFormula fm)
        return $ do modM sFormulas $ S.delete fm
                    insertFormula fm

-- | Try to simplify the atoms contained in the formulas. See
-- 'partialAtomValuation' for an explanation of what CR-rules are exploited
-- here.
evalFormulaAtoms :: Reduction ChangeIndicator
evalFormulaAtoms = do
    ctxt      <- ask
    valuation <- gets (partialAtomValuation ctxt)
    formulas  <- getM sFormulas
    applyChangeList $ do
        fm <- S.toList formulas
        case simplifyGuarded valuation fm of
          Just fm' -> return $ do
              case fm of
                GDisj disj -> markGoalAsSolved "simplified" (DisjG disj)
                _          -> return ()
              modM sFormulas       $ S.delete fm
              modM sSolvedFormulas $ S.insert fm
              insertFormula fm'
          Nothing  -> []

-- | A partial valuation for atoms. The return value of this function is
-- interpreted as follows.
--
-- @partialAtomValuation ctxt sys ato == Just True@ if for every valuation
-- @theta@ satisfying the graph constraints and all atoms in the constraint
-- system @sys@, the atom @ato@ is also satisfied by @theta@.
--
-- The interpretation for @Just False@ is analogous. @Nothing@ is used to
-- represent *unknown*.
--
partialAtomValuation :: ProofContext -> System -> LNAtom -> Maybe Bool
partialAtomValuation ctxt sys =
    eval
  where
    runMaude   = (`runReader` get pcMaudeHandle ctxt)
    before     = alwaysBefore sys
    lessRel    = rawLessRel sys
    nodesAfter = \i -> filter (i /=) $ S.toList $ D.reachableSet [i] lessRel

    -- | 'True' iff there in every solution to the system the two node-ids are
    -- instantiated to a different index *in* the trace.
    nonUnifiableNodes :: NodeId -> NodeId -> Bool
    nonUnifiableNodes i j = maybe False (not . runMaude) $
        (unifiableRuleACInsts) <$> M.lookup i (get sNodes sys)
                               <*> M.lookup j (get sNodes sys)

    -- | Try to evaluate the truth value of this atom in all models of the
    -- constraint system 'sys'.
    eval ato = case ato of
          Action (ltermNodeId' -> i) fa
            | ActionG i fa `M.member` get sGoals sys -> Just True
            | otherwise ->
                case M.lookup i (get sNodes sys) of
                  Just ru
                    | any (fa ==) (get rActs ru)                                -> Just True
                    | all (not . runMaude . unifiableLNFacts fa) (get rActs ru) -> Just False
                  _                                                             -> Nothing

          Less (ltermNodeId' -> i) (ltermNodeId' -> j)
            | i == j || j `before` i             -> Just False
            | i `before` j                       -> Just True
            | isLast sys i && isInTrace sys j    -> Just False
            | isLast sys j && isInTrace sys i &&
              nonUnifiableNodes i j              -> Just True
            | otherwise                          -> Nothing

          EqE x y
            | x == y                                -> Just True
            | not (runMaude (unifiableLNTerms x y)) -> Just False
            | otherwise                             ->
                case (,) <$> ltermNodeId x <*> ltermNodeId y of
                  Just (i, j)
                    | i `before` j || j `before` i  -> Just False
                    | nonUnifiableNodes i j         -> Just False
                  _                                 -> Nothing

          Last (ltermNodeId' -> i)
            | isLast sys i                       -> Just True
            | any (isInTrace sys) (nodesAfter i) -> Just False
            | otherwise ->
                case get sLastAtom sys of
                  Just j | nonUnifiableNodes i j -> Just False
                  _                              -> Nothing



-- | CR-rule *S_∀*: insert all newly implied formulas.
insertImpliedFormulas :: Reduction ChangeIndicator
insertImpliedFormulas = do
    sys <- gets id
    hnd <- getMaudeHandle
    applyChangeList $ do
        clause  <- (S.toList $ get sFormulas sys) ++
                   (S.toList $ get sLemmas sys)
        implied <- impliedFormulas hnd sys clause
        if ( implied `S.notMember` get sFormulas sys &&
             implied `S.notMember` get sSolvedFormulas sys )
          then return (insertFormula implied)
          else []

-- | @impliedFormulas se imp@ returns the list of guarded formulas that are
-- implied by @se@.
impliedFormulas :: MaudeHandle -> System -> LNGuarded -> [LNGuarded]
impliedFormulas hnd sys gf0 =
    case openGuarded gf `evalFresh` avoid gf of
      Just (All, _vs, antecedent, succedent) -> do
        let (actions, otherAtoms) = partitionEithers $ map prepare antecedent
            succedent'             = gall [] otherAtoms succedent
        subst <- candidateSubsts emptySubst actions
        return $ unskolemizeLNGuarded $ applySkGuarded subst succedent'
      _ -> []
  where
    gf = skolemizeGuarded gf0

    prepare (Action i fa) = Left (i, fa)
    prepare ato           = Right (fmap (fmapTerm (fmap Free)) ato)

    sysActions = do (i, fa) <- allActions sys
                    return (skolemizeTerm (varTerm i), skolemizeFact fa)

    candidateSubsts subst []     = do
        return subst
    candidateSubsts subst (a:as) = do
        sysAct <- sysActions
        subst' <- (`runReader` hnd) $ matchAction sysAct (applySkAction subst a)
        candidateSubsts (compose subst' subst) as


------------------------------------------------------------------------------
-- Terms, facts, and formulas with skolem constants
------------------------------------------------------------------------------

-- | A constant type that supports names and skolem constants. We use the
-- skolem constants to represent fixed free variables from the constraint
-- system during matching the atoms of a guarded clause to the atoms of the
-- constraint system.
data SkConst = SkName  Name
             | SkConst LVar
             deriving( Eq, Ord, Show, Data, Typeable )

type SkTerm    = VTerm SkConst LVar
type SkFact    = Fact SkTerm
type SkSubst   = Subst SkConst LVar
type SkGuarded = LGuarded SkConst

-- | A term with skolem constants and bound variables
type BSkTerm   = VTerm SkConst BLVar

-- | An term with skolem constants and bound variables
type BSkAtom   = Atom BSkTerm

instance IsConst SkConst


-- Skolemization of terms without bound variables.
--------------------------------------------------

skolemizeTerm :: LNTerm -> SkTerm
skolemizeTerm = fmapTerm conv
 where
  conv :: Lit Name LVar -> Lit SkConst LVar
  conv (Var v) = Con (SkConst v)
  conv (Con n) = Con (SkName n)

skolemizeFact :: LNFact -> Fact SkTerm
skolemizeFact = fmap skolemizeTerm

skolemizeAtom :: BLAtom -> BSkAtom
skolemizeAtom = fmap skolemizeBTerm

skolemizeGuarded :: LNGuarded -> SkGuarded
skolemizeGuarded = mapGuardedAtoms (const skolemizeAtom)

applySkTerm :: SkSubst -> SkTerm -> SkTerm
applySkTerm subst t = applyVTerm subst t

applySkFact :: SkSubst -> SkFact -> SkFact
applySkFact subst = fmap (applySkTerm subst)

applySkAction :: SkSubst -> (SkTerm,SkFact) -> (SkTerm,SkFact)
applySkAction subst (t,f) = (applySkTerm subst t, applySkFact subst f)


-- Skolemization of terms with bound variables.
-----------------------------------------------

skolemizeBTerm :: VTerm Name BLVar -> BSkTerm
skolemizeBTerm = fmapTerm conv
 where
  conv :: Lit Name BLVar -> Lit SkConst BLVar
  conv (Var (Free x))  = Con (SkConst x)
  conv (Var (Bound b)) = Var (Bound b)
  conv (Con n)         = Con (SkName n)

unskolemizeBTerm :: BSkTerm -> VTerm Name BLVar
unskolemizeBTerm t = fmapTerm conv t
 where
  conv :: Lit SkConst BLVar -> Lit Name BLVar
  conv (Con (SkConst x)) = Var (Free x)
  conv (Var (Bound b))   = Var (Bound b)
  conv (Var (Free v))    = error $ "unskolemizeBTerm: free variable " ++
                                   show v++" found in "++show t
  conv (Con (SkName n))  = Con n

unskolemizeBLAtom :: BSkAtom -> BLAtom
unskolemizeBLAtom = fmap unskolemizeBTerm

unskolemizeLNGuarded :: SkGuarded -> LNGuarded
unskolemizeLNGuarded = mapGuardedAtoms (const unskolemizeBLAtom)

applyBSkTerm :: SkSubst -> VTerm SkConst BLVar -> VTerm SkConst BLVar
applyBSkTerm subst =
    go
  where
    go t = case viewTerm t of
      Lit l     -> applyBLLit l
      FApp o as -> fApp o (map go as)

    applyBLLit :: Lit SkConst BLVar -> VTerm SkConst BLVar
    applyBLLit l@(Var (Free v)) =
        maybe (lit l) (fmapTerm (fmap Free)) (imageOf subst v)
    applyBLLit l                = lit l

applyBSkAtom :: SkSubst -> Atom (VTerm SkConst BLVar) -> Atom (VTerm SkConst BLVar)
applyBSkAtom subst = fmap (applyBSkTerm subst)

applySkGuarded :: SkSubst -> LGuarded SkConst -> LGuarded SkConst
applySkGuarded subst = mapGuardedAtoms (const $ applyBSkAtom subst)

-- Matching
-----------

matchAction :: (SkTerm, SkFact) ->  (SkTerm, SkFact) -> WithMaude [SkSubst]
matchAction (i1, fa1) (i2, fa2) =
    solveMatchLTerm sortOfSkol (i1 `matchWith` i2 <> fa1 `matchFact` fa2)
  where
    sortOfSkol (SkName  n) = sortOfName n
    sortOfSkol (SkConst v) = lvarSort v