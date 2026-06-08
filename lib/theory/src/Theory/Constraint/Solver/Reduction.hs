{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns  #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- A monad for writing constraint reduction steps together with basic steps
-- for inserting nodes, edges, actions, and equations and applying
-- substitutions.
module Theory.Constraint.Solver.Reduction (
  -- * The constraint 'Reduction' monad
    Reduction
  , execReduction
  , runReduction

  -- ** Change management
  , ChangeIndicator(..)
  , whenChanged
  , applyChangeList
  , whileChanging

  -- ** Accessing the 'ProofContext'
  , getProofContext
  , getMaudeHandle
  , getVerbose

  -- ** Inserting nodes, edges, and atoms
  , labelNodeId
  , insertFreshNode
  , insertFreshNodeConc

  , insertGoal
  , insertAtom
  , insertEdges
  , insertEdgesLabeled
  , insertChain
  , insertAction
  , insertLess
  , insertFormula
  , reducibleFormula

  -- ** Goal management
  , markGoalAsSolved
  , removeSolvedSplitGoals

  -- ** Substitution application
  , substSystem
  , substNodes
  , substEdges
  , substLastAtom
  , substLessAtoms
  , substFormulas
  , substSolvedFormulas

  -- ** Solving equalities
  , SplitStrategy(..)

  , solveNodeIdEqs
  , solveTermEqs
  , solveTermEqsLabeled
  , solveFactEqs
  , solveRuleEqs
  , solveSubstEqs

  -- ** Conjunction with another constraint 'System'
  , conjoinSystem

  -- ** Convenience export
  , module Logic.Connectives

  ) where

import           Debug.Trace
import qualified System.IO.Unsafe                        as Unsafe
import qualified System.Environment                      as SysEnv
import qualified Control.Exception                       as CtlExc
import           Control.Exception                       (evaluate)
import           Prelude                                 hiding (id, (.))

import qualified Data.Foldable                           as F
import qualified Data.Map                                as M
import qualified Data.Map.Strict                         as M'
import qualified Data.Set                                as S
import qualified Data.ByteString.Char8                   as BC
import           Data.List                               (mapAccumL)
import qualified Data.List
import           Safe

import           Control.Basics
import           Control.Category
import           Control.Monad.Bind
import           Control.Monad.Disj
import           Control.Monad.Reader
import           Control.Monad.State                     (StateT, execStateT, gets, runStateT)

import           Text.PrettyPrint.Class

import           Extension.Data.Label
-- import           Extension.Data.Monoid                   (Monoid(..))
import           Extension.Prelude

import           Logic.Connectives

import           Theory.Constraint.Solver.Contradictions
import qualified Theory.Constraint.Solver.Trace          as T
import           Theory.Constraint.System
import           Theory.Model

------------------------------------------------------------------------------
-- The constraint reduction monad
------------------------------------------------------------------------------

-- | A constraint reduction step. Its state is the current constraint system,
-- it can generate fresh names, split over cases, and access the proof
-- context.
type Reduction = StateT System (FreshT (DisjT (Reader ProofContext)))


-- Permanent debug instrumentation flags
----------------------------------------

-- | TAM_HS_DBG_SOLVE_TERM_EQS=1 dumps every solveTermEqs call's site
-- label, split strategy, equation count, and the equations.  Pair with
-- Rust's TAM_RS_DBG_SOLVE_TERM_EQS for HS↔Rust diffing of the goal-by-
-- goal solver flow.  Cached via unsafePerformIO to stay zero-cost when
-- the env var is unset.
dbgSolveTermEqsOn :: Bool
dbgSolveTermEqsOn = Unsafe.unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_DBG_SOLVE_TERM_EQS"
{-# NOINLINE dbgSolveTermEqsOn #-}

hsTraceSBindHere :: Bool
hsTraceSBindHere = Unsafe.unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_S_BIND"
{-# NOINLINE hsTraceSBindHere #-}

hsTraceSubstNodeIdsOn :: Bool
hsTraceSubstNodeIdsOn = Unsafe.unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_SUBST_NODE_IDS"
{-# NOINLINE hsTraceSubstNodeIdsOn #-}

-- Executing reductions
-----------------------

-- | Run a constraint reduction. Returns a list of constraint systems whose
-- combined solutions are equal to the solutions of the given system. This
-- property is obviously not enforced, but it must be respected by all
-- functions of type 'Reduction'.
runReduction :: Reduction a -> ProofContext -> System -> FreshState
             -> Disj ((a, System), FreshState)
runReduction m ctxt se fs =
    Disj $ (`runReader` ctxt) $ runDisjT $ (`runFreshT` fs) $ runStateT m se

-- | Run a constraint reduction returning only the updated constraint systems
-- and the new freshness states.
execReduction :: Reduction a -> ProofContext -> System -> FreshState
              -> Disj (System, FreshState)
execReduction m ctxt se fs =
    Disj $ (`runReader` ctxt) . runDisjT . (`runFreshT` fs) $ execStateT m se

-- Change management
--------------------

-- | Indicate whether the constraint system was changed or not.
data ChangeIndicator = Unchanged | Changed
       deriving( Eq, Ord, Show )

instance Semigroup ChangeIndicator where
    Changed   <> _         = Changed
    _         <> Changed   = Changed
    Unchanged <> Unchanged = Unchanged

instance Monoid ChangeIndicator where
    mempty = Unchanged

-- | Return 'True' iff there was a change.
wasChanged :: ChangeIndicator -> Bool
wasChanged Changed   = True
wasChanged Unchanged = False

-- | Only apply a monadic action, if there has been a change.
whenChanged :: Monad m => ChangeIndicator -> m () -> m ()
whenChanged = when . wasChanged

-- | Apply a list of changes to the proof state.
applyChangeList :: [Reduction ()] -> Reduction ChangeIndicator
applyChangeList []      = return Unchanged
applyChangeList changes = sequence_ changes >> return Changed

-- | Execute a 'Reduction' as long as it results in changes. Indicate whether
-- at least one change was performed.
whileChanging :: Reduction ChangeIndicator -> Reduction ChangeIndicator
whileChanging reduction =
    go Unchanged
  where
    go indicator = do indicator' <- reduction
                      case indicator' of
                          Unchanged -> return indicator
                          Changed   -> go     indicator'

-- Accessing the proof context
------------------------------

-- | Retrieve the 'ProofContext'.
getProofContext :: Reduction ProofContext
getProofContext = ask

-- | Retrieve the 'MaudeHandle' from the 'ProofContext'.
getMaudeHandle :: Reduction MaudeHandle
getMaudeHandle = askM pcMaudeHandle

-- | Retrieve the verbose parameter from the 'ProofContext'.
getVerbose :: Reduction Bool
getVerbose = askM pcVerbose


-- Inserting (fresh) nodes into the constraint system
-----------------------------------------------------

-- | Insert a fresh rule node labelled with a fresh instance of one of the
-- rules and return one of the conclusions.
insertFreshNodeConc :: [RuleAC] -> Reduction (RuleACInst, NodeConc, LNFact)
insertFreshNodeConc rules = do
    (i, ru) <- insertFreshNode rules Nothing
    (v, fa) <- disjunctionOfList $ enumConcs ru
    return (ru, (i, v), fa)

-- | Insert a fresh rule node labelled with a fresh instance of one of the rules
-- and solve it's 'Fr', 'In', and 'KU' premises immediately.
-- If a parent node is given, updates the remaining rule applications.
insertFreshNode :: [RuleAC] -> Maybe RuleACInst -> Reduction (NodeId, RuleACInst)
insertFreshNode rules parent = do
    i <- freshLVar "vr" LSortNode
    (,) i <$> labelNodeId i rules parent

-- | Label a node-id with a fresh instance of one of the rules and
-- solve it's 'Fr', 'In', and 'KU' premises immediately.
-- If a parent node is given, updates the remaining rule applications.
--
-- PRE: Node must not yet be labelled with a rule.
labelNodeId :: NodeId -> [RuleAC] -> Maybe RuleACInst -> Reduction RuleACInst
labelNodeId = \i rules parent -> do
    (ru1, mrconstrs) <- importRule =<< disjunctionOfList rules
    let ru = case parent of
                Just pa | (getRuleName pa == getRuleName ru1) && (getRemainingRuleApplications pa > 1)
                    -> setRemainingRuleApplications ru1 ((getRemainingRuleApplications pa) - 1)
                _   -> ru1
    when (Unsafe.unsafePerformIO $
            maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_DBG_SOLVE_RULE_CONSTRAINTS") $ do
        let nSubsts = case mrconstrs of
                Just (Disj substs) -> length substs
                Nothing             -> 0
        Debug.Trace.traceM ("[HS_LABEL_NODE_ID] rule=" ++ getRuleName ru
            ++ " n_variant_substs=" ++ show nSubsts)
    solveRuleConstraints mrconstrs
    modM sNodes (M.insert i ru)
    exploitPrems i ru
    return ru
  where
    -- | Import a rule with all its variables renamed to fresh variables.
    importRule ru = someRuleACInst ru `evalBindT` noBindings

    mkISendRuleAC ann m = return $ Rule (IntrInfo (ISendRule))
                                    [kuFactAnn ann m] [inFact m] [kLogFact m] []


    mkFreshRuleAC m = Rule (ProtoInfo (ProtoRuleACInstInfo FreshRule mempty []))
                           [] [freshFact m] [] [m]

    exploitPrems i ru = do
        T.traceExecM ("exploitPrems rule=" ++ getRuleName ru)
        mapM_ (exploitPrem i ru) (enumPrems ru)

    exploitPrem i ru (v, fa) = case fa of
        -- CR-rule *DG2_2* specialized for *In* facts.
        Fact InFact ann [m] -> do
            T.traceExecM "exploitPrem InFact"
            j <- freshLVar "vf" LSortNode
            ruKnows <- mkISendRuleAC ann m
            modM sNodes (M.insert j ruKnows)
            modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i, v))
            exploitPrems j ruKnows

        -- CR-rule *DG2_2* specialized for *Fr* facts.
        Fact FreshFact _ [m] -> do
            T.traceExecM ("exploitPrem FreshFact isFresh=" ++ show (isFreshVar m))
            j <- freshLVar "vf" LSortNode
            -- TAM_HS_TRACE_VF_CREATE=1 mirror of Rust's TAM_RS_TRACE_VF_CREATE:
            -- log each vf-supplier creation so HS-vs-Rust counts can be
            -- compared to find the over-creation site.
            when (Unsafe.unsafePerformIO $
                    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_VF_CREATE") $
                Debug.Trace.traceM ("[HS_VF_CREATE] site=exploitPrem_FreshFact j=" ++ show j)
            modM sNodes (M.insert j (mkFreshRuleAC m))
            unless (isFreshVar m) $ do
                -- 'm' must be of sort fresh ==> enforce via unification
                n <- varTerm <$> freshLVar "n" LSortFresh
                T.traceExecM "FrNarrow"
                void (solveTermEqs SplitNow [Equal m n])
            modM sEdges (S.insert $ Edge (j, ConcIdx 0) (i,v))

          -- CR-rule *DG2_{2,u}*: solve a KU-premise by inserting the
          -- corresponding KU-actions before this node.
        _ | isKUFact fa -> do
              j <- freshLVar "vk" LSortNode
              insertLess (LessAtom j i Adversary)
              void (insertAction j fa)

          -- Store premise goal for later processing using CR-rule *DG2_2*
          | otherwise -> insertGoal (PremiseG (i,v) fa) (v `elem` breakers)
      where
        breakers = ruleInfo (get praciLoopBreakers) (const []) $ get rInfo ru

-- | Insert a chain constrain.
insertChain :: NodeConc -> NodePrem -> Reduction ()
insertChain c p = insertGoal (ChainG c p) False

-- | Insert an edge constraint. CR-rule *DG1_2* is enforced automatically,
-- i.e., the fact equalities are enforced.
insertEdges :: [(NodeConc, LNFact, LNFact, NodePrem)] -> Reduction ()
insertEdges = insertEdgesLabeled "default"

-- | Insert an edge constraint with a call-site label so [CONTRA-DUMP] traces
-- can be attributed to specific call sites (solvePremise / solveChain DIRECT /
-- solveChain EXTEND).
insertEdgesLabeled :: String -> [(NodeConc, LNFact, LNFact, NodePrem)] -> Reduction ()
insertEdgesLabeled siteLabel edges = do
    T.traceExecM ("insertEdges n=" ++ show (length edges))
    when T.flagContra $ Debug.Trace.traceM
      ("[INSERT_EDGES] enter site=" ++ siteLabel
       ++ " n=" ++ show (length edges)
       ++ " edges=" ++ show [(c,p) | (c,_,_,p) <- edges])
    void (solveFactEqsLabeled ("insertEdges:" ++ siteLabel) SplitNow [ Equal fa1 fa2 | (_, fa1, fa2, _) <- edges ])
    modM sEdges (\es -> foldr S.insert es [ Edge c p | (c,_,_,p) <- edges])

-- | Insert an 'Action' atom. Ensures that (almost all) trivial *KU* actions
-- are solved immediately using rule *S_{at,u,triv}*. We currently avoid
-- adding intermediate products. Indicates whether nodes other than the given
-- action have been added to the constraint system.
--
-- FIXME: Ensure that intermediate products are also solved before stating
-- that no rule is applicable.
insertAction :: NodeId -> LNFact -> Reduction ChangeIndicator
insertAction i fa@(Fact _ ann _) = do
    when (Unsafe.unsafePerformIO $
            maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_DBG_KU_INSERT") $ do
        case kFactView fa of
            Just (UpK, m) ->
                Debug.Trace.traceM ("[HS_KU_INSERT] i=" ++ show i
                    ++ " term=" ++ show m)
            _ -> return ()
    present <- (goal `M.member`) <$> getM sGoals
    isdiff <- getM sDiffSystem
    nodePresent <- (i `M.member`) <$> getM sNodes
    if present
      then do return Unchanged
      else do case kFactView fa of
                Just (UpK, viewTerm2 -> FPair m1 m2) -> do
                -- In the diff case, add pair rule instead of goal
                    if isdiff
                       then do
                          -- if the node is already present in the graph, do not insert it again. (This can be caused by substitutions applying and changing a goal.)
                          if not nodePresent
                             then do
                               modM sNodes (M.insert i (Rule (IntrInfo (ConstrRule $ BC.pack "_pair")) ([(kuFactAnn ann m1),(kuFactAnn ann m2)]) ([fa]) ([fa]) []))
                               insertGoal goal False
                               markGoalAsSolved "pair" goal
                               requiresKU m1 *> requiresKU m2 *> return Changed
                             else do
                               insertGoal goal False
                               markGoalAsSolved "exists" goal
                               return Changed
                       else do
                          insertGoal goal False
                          requiresKU m1 *> requiresKU m2 *> return Changed

                Just (UpK, viewTerm2 -> FInv m) -> do
                -- In the diff case, add inv rule instead of goal
                    if isdiff
                       then do
                          -- if the node is already present in the graph, do not insert it again. (This can be caused by substitutions applying and changing a goal.)
                          if not nodePresent
                             then do
                               modM sNodes (M.insert i (Rule (IntrInfo (ConstrRule $ BC.pack "_inv")) ([(kuFactAnn ann m)]) ([fa]) ([fa]) []))
                               insertGoal goal False
                               markGoalAsSolved "inv" goal
                               requiresKU m *> return Changed
                             else do
                               insertGoal goal False
                               markGoalAsSolved "exists" goal
                               return Changed
                       else do
                          insertGoal goal False
                          requiresKU m *> return Changed

                Just (UpK, viewTerm2 -> FMult ms) -> do
                -- In the diff case, add mult rule instead of goal
                    if isdiff
                       then do
                          -- if the node is already present in the graph, do not insert it again. (This can be caused by substitutions applying and changing a goal.)
                          if not nodePresent
                             then do
                               modM sNodes (M.insert i (Rule (IntrInfo (ConstrRule $ BC.pack "_mult")) (map (\x -> kuFactAnn ann x) ms) ([fa]) ([fa]) []))
                               insertGoal goal False
                               markGoalAsSolved "mult" goal
                               mapM_ requiresKU ms *> return Changed
                             else do
                               insertGoal goal False
                               markGoalAsSolved "exists" goal
                               return Changed

                       else do
                          insertGoal goal False
                          mapM_ requiresKU ms *> return Changed

                Just (UpK, viewTerm2 -> FUnion ms) -> do
                -- In the diff case, add union (?) rule instead of goal
                    if isdiff
                       then do
                          -- if the node is already present in the graph, do not insert it again. (This can be caused by substitutions applying and changing a goal.)
                          if not nodePresent
                             then do
                               modM sNodes (M.insert i (Rule (IntrInfo (ConstrRule $ BC.pack "_union")) (map (\x -> kuFactAnn ann x) ms) ([fa]) ([fa]) []))
                               insertGoal goal False
                               markGoalAsSolved "union" goal
                               mapM_ requiresKU ms *> return Changed
                             else do
                               insertGoal goal False
                               markGoalAsSolved "exists" goal
                               return Changed

                       else do
                          insertGoal goal False
                          mapM_ requiresKU ms *> return Changed

                _ -> do
                    insertGoal goal False
                    return Unchanged
  where
    goal = ActionG i fa
    -- Here we rely on the fact that the action is new. Otherwise, we might
    -- loop due to generating new KU-nodes that are merged immediately.
    requiresKU t = do
      j <- freshLVar "vk" LSortNode
      let faKU = kuFactAnn ann t
      insertLess (LessAtom j i Adversary)
      void (insertAction j faKU)

-- | Insert a 'Less' atom. @insertLess i j@ means that *i < j* is added.
insertLess :: LessAtom -> Reduction ()
insertLess la = do
  hsTraceInsertLess la
  modM sLessAtoms (S.insert la)

-- TAM_HS_TRACE_INSERT_LESS=1: trace every insertLess call.  Reusable
-- diagnostic for locating where specific LessAtoms (eg. InjectiveFacts)
-- originate during simplify — paired with Rust's identical hook for
-- root-causing less-atom divergences.
hsTraceInsertLess :: LessAtom -> Reduction ()
hsTraceInsertLess la
    | hsTraceInsertLessOn =
        trace ("[INSERT_LESS] " ++ show la) (return ())
    | otherwise = return ()

hsTraceInsertLessOn :: Bool
hsTraceInsertLessOn = Unsafe.unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_INSERT_LESS"
{-# NOINLINE hsTraceInsertLessOn #-}

-- | Insert a 'Subterm' atom. *x ⊏ y* is added to the SubtermStore
insertSubterm :: LNTerm -> LNTerm -> Reduction ()
insertSubterm x y = setM sSubtermStore . addSubterm (x, y) =<< getM sSubtermStore

-- | Insert the negation of a 'Subterm' atom. *¬ x ⊏ y* is added to the SubtermStore
insertNegSubterm :: LNTerm -> LNTerm -> Reduction()
insertNegSubterm x y = setM sSubtermStore . addNegSubterm (x, y) =<< getM sSubtermStore

-- | Insert a 'Last' atom and ensure their uniqueness.
insertLast :: NodeId -> Reduction ChangeIndicator
insertLast i = do
    lst <- getM sLastAtom
    case lst of
      Nothing -> setM sLastAtom (Just i) >> return Unchanged
      Just j  -> solveNodeIdEqs [Equal i j]

-- | Insert an atom. Returns 'Changed' if another part of the constraint
-- system than the set of actions was changed.
insertAtom :: LNAtom -> Reduction ()
insertAtom ato = case ato of
    EqE x y       -> void $ solveTermEqs SplitNow [Equal x y]
    Subterm x y   -> insertSubterm x y
    Action i fa   -> void $ insertAction (ltermNodeId' i) fa
    Less i j      -> insertLess (LessAtom (ltermNodeId' i) (ltermNodeId' j) Formula)
    Last i        -> void $ insertLast (ltermNodeId' i)
    Syntactic _   -> return ()

-- | Insert a 'Guarded' formula. Ensures that existentials, conjunctions, negated
-- last atoms, and negated less atoms, are immediately solved using the rules
-- *S_exists*, *S_and*, *S_not,last*, and *S_not,less*. Only the inserted
-- formula is marked as solved. Other intermediate formulas are not marked.
insertFormula :: LNGuarded -> Reduction ()
insertFormula = do
    insert True
  where
    insert mark fm = do
        formulas       <- getM sFormulas
        solvedFormulas <- getM sSolvedFormulas
        insert' mark formulas solvedFormulas fm

    insert' mark formulas solvedFormulas fm
      | fm `S.member` formulas       = return ()
      | fm `S.member` solvedFormulas = return ()
      | otherwise = case fm of
          GAto ato -> do
              markAsSolved
              insertAtom (bvarToLVar ato)

          -- CR-rule *S_∧*
          GConj fms -> do
              markAsSolved
              mapM_ (insert False) (getConj fms)

          -- Store for later applications of CR-rule *S_∨*
          GDisj disj -> do
              T.traceFormM "Disj" fm
              when (null (getDisj disj)) $ do
                  let dbg = Unsafe.unsafePerformIO $
                        maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_TRACE_GFALSE"
                  when dbg $ Debug.Trace.traceM $
                    "[HS_GFALSE] path=" ++ T.casePathString (Unsafe.unsafePerformIO T.getCasePath)
                    ++ " gfalse inserted"
              let dbgD = Unsafe.unsafePerformIO $
                    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_DBG_DISJ_INSERT"
              when dbgD $ Debug.Trace.traceM $
                  "[HS_DISJ_INSERT] n_alts=" ++ show (length $ getDisj disj) ++
                  " alts=" ++ show (getDisj disj)
              modM sFormulas (S.insert fm)
              insertGoal (DisjG disj) False

          -- CR-rule *S_∃*
          GGuarded Ex ss as gf -> do
              -- must always mark as solved, as we otherwise may repeatedly
              -- introduce fresh variables.
              modM sSolvedFormulas $ S.insert fm
              xs <- mapM (uncurry freshLVar) ss
              let body = gconj (map GAto as ++ [gf])
              insert False (substBound (zip [0..] (reverse xs)) body)

          -- CR-rule *S_{¬,⋖}*
          GGuarded All [] [Less i j] gf  | gf == gfalse -> do
              markAsSolved
              insert False (gdisj [GAto (EqE i j), GAto (Less j i)])

          -- negative Subterm
          GGuarded All [] [Subterm i j] gf  | gf == gfalse -> do
              markAsSolved
              insertNegSubterm (bTermToLTerm i) (bTermToLTerm j)

          -- CR-rule: FIXME add this rule to paper
          GGuarded All [] [EqE i@(bltermNodeId -> Just _)
                               j@(bltermNodeId -> Just _) ] gf
            | gf == gfalse -> do
                markAsSolved
                insert False (gdisj [GAto (Less i j), GAto (Less j i)])

          -- CR-rule *S_{¬,last}*
          GGuarded All [] [Last i]   gf  | gf == gfalse -> do
              markAsSolved
              lst <- getM sLastAtom
              j <- case lst of
                     Nothing  -> do j <- freshLVar "last" LSortNode
                                    void (insertLast j)
                                    return (varTerm (Free j))
                     Just j -> return (varTerm (Free j))
              insert False $ gdisj [ GAto (Less j i), GAto (Less i j) ]

          -- Guarded All quantification: store for saturation
          GGuarded All _ _ _ -> modM sFormulas (S.insert fm)
      where
        markAsSolved = when mark $ modM sSolvedFormulas $ S.insert fm

-- | 'True' iff the formula can be reduced by one of the rules implemented in
-- 'insertFormula'.
reducibleFormula :: LNGuarded -> Bool
reducibleFormula fm = case fm of
    GAto _                           -> True
    GConj _                          -> True
    GGuarded Ex _ _ _                -> True
    GGuarded All [] [Less _ _]    gf -> gf == gfalse
    GGuarded All [] [Subterm _ _] gf -> gf == gfalse
    GGuarded All [] [Last _]      gf -> gf == gfalse
    _                                -> False


-- Goal management
------------------

-- | Combine the status of two goals.
combineGoalStatus :: GoalStatus -> GoalStatus -> GoalStatus
combineGoalStatus (GoalStatus solved1 age1 loops1)
                  (GoalStatus solved2 age2 loops2) =
    GoalStatus (solved1 || solved2) (min age1 age2) (loops1 || loops2)

-- | TAM_HS_DBG_INSERT_GOAL=1 dumps every insertGoalStatus call's
-- assigned gsNr and goal.  Pair with Rust's TAM_RS_DBG_INSERT_GOAL
-- to lockstep-diff insertGoal sequences and find the divergent
-- insertion path between HS and RS.
dbgInsertGoalOn :: Bool
dbgInsertGoalOn = Unsafe.unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_DBG_INSERT_GOAL"
{-# NOINLINE dbgInsertGoalOn #-}

-- | Insert a goal and its status with a new age. Merge status if goal exists.
insertGoalStatus :: Goal -> GoalStatus -> Reduction ()
insertGoalStatus goal status = do
    age <- getM sNextGoalNr
    when dbgInsertGoalOn $ do
        ctxt <- ask
        let lemmaName = Unsafe.unsafePerformIO $
                CtlExc.try (evaluate (get pcLemmaName ctxt)) >>= \r ->
                    case (r :: Either CtlExc.SomeException String) of
                        Left _  -> return "<precompute>"
                        Right n -> return n
        let want = Unsafe.unsafePerformIO $
                SysEnv.lookupEnv "TAM_HS_DBG_LEMMA_FILTER"
        let emit = case want of
              Nothing -> True
              Just w  -> w == lemmaName
        when emit $
            trace ("[HS_INS_GOAL] lemma=" ++ lemmaName ++
                   " gsNr=" ++ show age ++
                   " solved=" ++ show (get gsSolved status) ++
                   " loops=" ++ show (get gsLoopBreaker status) ++
                   " goal=" ++ show goal) (return ())
    modM sGoals $ M'.insertWith combineGoalStatus goal (set gsNr age status)
    sNextGoalNr =: succ age

-- | Insert a 'Goal' and store its age.
insertGoal :: Goal -> Bool -> Reduction ()
insertGoal goal looping = insertGoalStatus goal (GoalStatus False 0 looping)

-- | Mark the given goal as solved.
markGoalAsSolved :: String -> Goal -> Reduction ()
markGoalAsSolved how goal =
    case goal of
      ActionG _ _     -> updateStatus
      PremiseG _ fa
        | isKDFact fa -> delete
        | otherwise   -> updateStatus
      ChainG _ _      -> delete
      SplitG _        -> updateStatus
      DisjG disj      -> modM sFormulas       (S.delete $ GDisj disj) >>
                         modM sSolvedFormulas (S.insert $ GDisj disj) >>
                         updateStatus
      SubtermG _      -> updateStatus
  where
    delete :: Reduction ()
    delete = modM sGoals $ M.delete goal

    updateStatus :: Reduction ()
    updateStatus = do
        mayStatus <- M.lookup goal <$> getM sGoals
        verbose <- getVerbose
        case mayStatus of
          Just status -> if (verbose) then trace (msg status) $
              modM sGoals $ M.insert goal $ set gsSolved True status else modM sGoals $ M.insert goal $ set gsSolved True status
          Nothing     -> trace ("markGoalAsSolved: inexistent constraint " ++ show goal) $ return ()

    msg status = render $ nest 2 $ fsep $
        [ text ("solved goal nr. "++ show (get gsNr status))
          <-> parens (text how) <> colon
        , nest 2 (prettyGoal goal) ]

removeSolvedSplitGoals :: Reduction ()
removeSolvedSplitGoals = do
    goals    <- getM sGoals
    existent <- splitExists <$> getM sEqStore
    sequence_ [ modM sGoals $ M.delete goal
              | goal@(SplitG i) <- M.keys goals, not (existent i) ]


-- Substitution
---------------

-- | Apply the current substitution of the equation store to the remainder of
-- the sequent.
substSystem :: Reduction ChangeIndicator
substSystem = do
    -- The equation-store substitution is applied to the whole system after
    -- every solving step and is idempotent, so it is frequently empty (e.g.
    -- right after a proof step renamed and reset it). Applying an empty
    -- substitution cannot change anything and maintains no invariants, so we
    -- skip the (otherwise O(system size)) traversal entirely.
    subst <- getM sSubst
    if nullSubst subst
      then return Unchanged
      else do
   	c1 <- T.tracePassPair "substSystem.substNodes" substNodes
    	T.tracePassPair "substSystem.substEdges" substEdges
    	T.tracePassPair "substSystem.substLastAtom" substLastAtom
    	T.tracePassPair "substSystem.substLessAtoms" substLessAtoms
    	T.tracePassPair "substSystem.substSubtermStore" substSubtermStore
    	T.tracePassPair "substSystem.substFormulas" substFormulas
    	T.tracePassPair "substSystem.substSolvedFormulas" substSolvedFormulas
    	T.tracePassPair "substSystem.substLemmas" substLemmas
    	c2 <- T.tracePassPair "substSystem.substGoals" substGoals
    	T.tracePassPair "substSystem.substNextGoalNr" substNextGoalNr
    	return (c1 <> c2)

-- no invariants to maintain here
substEdges, substLessAtoms, substSubtermStore, substLastAtom, substFormulas,
  substSolvedFormulas, substLemmas, substNextGoalNr :: Reduction ()

substEdges          = substPart sEdges
substLessAtoms      = substPart sLessAtoms
substSubtermStore   = substPart sSubtermStore
substLastAtom       = substPart sLastAtom
substFormulas       = substPart sFormulas
substSolvedFormulas = substPart sSolvedFormulas
substLemmas         = substPart sLemmas
substNextGoalNr     = return ()

-- | Apply the current substitution of the equation store to a part of the
-- sequent. This is an internal function.
substPart :: Apply LNSubst a => (System :-> a) -> Reduction ()
substPart l = do subst <- getM sSubst
                 modM l (apply subst)

-- | Apply the current substitution of the equation store the nodes of the
-- constraint system. Indicates whether additional equalities were added to
-- the equations store.
substNodes :: Reduction ChangeIndicator
substNodes =
    substNodeIds <* ((modM sNodes . M.map . apply) =<< getM sSubst)

-- | @setNodes nodes@ normalizes the @nodes@ such that node ids are unique and
-- then updates the @sNodes@ field of the proof state to the corresponding map.
-- Return @True@ iff new equalities have been added to the equation store.
setNodes :: [(NodeId, RuleACInst)] -> Reduction ChangeIndicator
setNodes nodes0 = do
    when T.flagSimplify $ Debug.Trace.traceM $
        "[SET_NODES] enter nodes0_len=" ++ show (length nodes0)
        ++ " groups=" ++ show (length groups)
        ++ " ruleEqs_len=" ++ show (length ruleEqs)
    sNodes =: M.fromList nodes
    if null ruleEqs then do
                         when T.flagSimplify $ Debug.Trace.traceM "[SET_NODES] exit no_eqs"
                         return Unchanged
                    else do
                         r <- solveRuleEqs SplitLater ruleEqs >> return Changed
                         when T.flagSimplify $ Debug.Trace.traceM "[SET_NODES] exit after_solveRuleEqs"
                         return r
  where
    -- merge nodes with equal node id
    groups            = groupSortOn fst nodes0
    (ruleEqs, nodes)  = first concat $ unzip $ map merge groups

    merge []            = unreachable "setNodes"
    merge (keep:remove) = (map (Equal (snd keep) . snd) remove, keep)

-- | Apply the current substitution of the equation store to the node ids and
-- ensure uniqueness of the labels, as required by rule *U_lbl*. Indicates
-- whether there where new equalities added to the equations store.
substNodeIds :: Reduction ChangeIndicator
substNodeIds =
    whileChanging $ do
        subst <- getM sSubst
        nodesRaw <- gets (M.toList . get sNodes)
        let nodes = map (first (apply subst)) nodesRaw
        when hsTraceSubstNodeIdsOn $ do
            let renames = [(i, i') | ((i, _), (i', _)) <- zip nodesRaw nodes, i /= i']
                idsBefore = map fst nodesRaw
                idsAfter  = map fst nodes
                collisions = filter (\g -> length g > 1) $
                                Data.List.groupBy (\a b -> fst a == fst b) $
                                Data.List.sortOn fst nodes
            Debug.Trace.traceM ("[HS_SUBST_NODE_IDS] ids_before=" ++ show idsBefore
                              ++ " ids_after=" ++ show idsAfter
                              ++ " renames=" ++ show renames
                              ++ " collision_groups=" ++ show (length collisions))
            when (not (null collisions)) $ do
              Debug.Trace.traceM ("[HS_SUBST_NODE_IDS] subst=" ++ show subst)
              mapM_ (\g -> Debug.Trace.traceM ("[HS_SUBST_NODE_IDS] collision_at=" ++ show (fst (head g))
                                            ++ " count=" ++ show (length g))) collisions
        setNodes nodes

-- | Substitute all goals. Keep the ones with the lower nr.
substGoals :: Reduction ChangeIndicator
substGoals = do
    subst <- getM sSubst
    goals <- M.toList <$> getM sGoals
    sGoals =: M.empty
    changes <- forM goals $ \(goal, status) -> case goal of
        -- Look out for KU-actions that might need to be solved again.
        ActionG i fa@(kFactView -> Just (UpK, m))
          | (isMsgVar m || isProduct m || isUnion m {--|| isXor m-}) && (apply subst m /= m) ->
              insertAction i (apply subst fa)
        _ -> do modM sGoals $
                  M'.insertWith combineGoalStatus (apply subst goal) status
                return Unchanged

    return (mconcat changes)


-- Conjoining two constraint systems
------------------------------------

-- | @conjoinSystem se@ conjoins the logical information in @se@ to the
-- constraint system. It assumes that the free variables in @se@ are shared
-- with the free variables in the proof state.
conjoinSystem :: System -> Reduction ()
conjoinSystem sys = do
    kind <- getM sSourceKind
    unless (kind == get sSourceKind sys) $
        error "conjoinSystem: source-kind mismatch"
    joinSets sSolvedFormulas
    joinSets sLemmas
    joinSets sEdges
    F.mapM_ insertLast                 $ get sLastAtom    sys
    F.mapM_ insertLess $ get sLessAtoms sys
    -- split-goals are not valid anymore
    mapM_   (uncurry insertGoalStatus) $ filter (not . isSplitGoal . fst) $ M.toList $ get sGoals sys
    F.mapM_ insertFormula $ get sFormulas sys
    -- update nodes
    _ <- (setNodes . (M.toList (get sNodes sys) ++) . M.toList) =<< getM sNodes
    -- conjoin equation store
    eqs <- getM sEqStore
    let (eqs',splitIds) = (mapAccumL addDisj eqs (map snd . getConj $ get sConjDisjEqs sys))
    setM sEqStore eqs'
    -- conjoin subterm store
    modM sSubtermStore (conjoinSubtermStores (get sSubtermStore sys))
    -- add split-goals for all disjunctions of sys
    mapM_  (`insertGoal` False) $ SplitG <$> splitIds
    void (solveSubstEqs SplitNow $ get sSubst sys)
    -- Propagate substitution changes. Ignore change indicator, as it is
    -- assumed to be 'Changed' by default.
    void substSystem
  where
    joinSets :: Ord a => (System :-> S.Set a) -> Reduction ()
    joinSets proj = modM proj (`S.union` get proj sys)

-- Unification via the equation store
-------------------------------------

-- | 'SplitStrategy' denotes if the equation store should be split into
-- multiple equation stores.
data SplitStrategy = SplitNow | SplitLater

-- The 'ChangeIndicator' indicates whether at least one non-trivial equality
-- was solved.

-- | @noContradictoryEqStore@ succeeds iff the equation store is not
-- contradictory.
noContradictoryEqStore :: Reduction ()
noContradictoryEqStore = do
    isfalse <- eqsIsFalse <$> getM sEqStore
    when (isfalse && T.flagContra) $ do
        sys <- gets id
        Debug.Trace.traceM $ "[CONTRA-DUMP] label=noContradictoryEqStore:eqsIsFalse"
          ++ " nodes=" ++ show (M.size (get sNodes sys))
          ++ " edges=" ++ show (S.size (get sEdges sys))
          ++ " formulas=" ++ show (S.size (get sFormulas sys))
          ++ " goals=" ++ show (M.size (get sGoals sys))
    T.contradictoryIfT "noContradictoryEqStore:eqsIsFalse" isfalse

-- | Add a list of term equalities to the equation store. And
--  split resulting disjunction of equations according
--  to given split strategy.
--
-- Note that updating the remaining parts of the constraint system with the
-- substitution has to be performed using a separate call to 'substSystem'.
solveTermEqs :: SplitStrategy -> [Equal LNTerm] -> Reduction ChangeIndicator
solveTermEqs splitStrat eqs0 = solveTermEqsLabeled "solveTermEqs" splitStrat eqs0

-- | Like solveTermEqs but tags downstream noContradictoryEqStore traces
-- with a call-site label so we can attribute contradictions to specific
-- upstream callers (solveSubstEqs, solveNodeIdEqs, solveFactEqs, etc.).
solveTermEqsLabeled :: String -> SplitStrategy -> [Equal LNTerm] -> Reduction ChangeIndicator
solveTermEqsLabeled siteLabel splitStrat eqs0 =
    case filter (not . evalEqual) eqs0 of
      []  -> do
          -- TAM_HS_DBG_SOLVE_TERM_EQS=1: tick zero-eq calls too so call
          -- counts can be compared against Rust's TAM_RS_DBG_SOLVE_TERM_EQS.
          if dbgSolveTermEqsOn
              then Debug.Trace.traceM ("[hs-ste-tick] zero-eqs site=" ++ siteLabel)
              else return ()
          return Unchanged
      eqs1 -> do
        T.traceExecM ("solveTermEqs n=" ++ show (length eqs1))
        when hsTraceSBindHere $ do
          let splitTag = case splitStrat of
                SplitNow -> "SplitNow"
                SplitLater -> "SplitLater"
          Debug.Trace.traceM ("[HS_STE_CALL] site=" ++ siteLabel ++
                              " split=" ++ splitTag ++ " eqs=" ++ show eqs1)
        -- TAM_HS_DBG_SOLVE_TERM_EQS=1: dump every solveTermEqs call's
        -- site label, split strategy, and the equations being solved.
        -- Pair with Rust's TAM_RS_DBG_SOLVE_TERM_EQS for HS↔Rust
        -- diffing of the solver flow (see
        -- [[project-apply-eq-store-divergence]]).
        if dbgSolveTermEqsOn
            then do
              let splitTag = case splitStrat of
                    SplitNow -> "SplitNow"
                    SplitLater -> "SplitLater"
              Debug.Trace.traceM ("[hs-ste] === call site=" ++ siteLabel ++
                            " split=" ++ splitTag ++ " n=" ++ show (length eqs1))
              mapM_ (\(i, Equal l r) ->
                Debug.Trace.traceM ("  eq[" ++ show (i :: Int) ++ "]: " ++ show l ++ " = " ++ show r))
                (zip [0..] eqs1)
            else return ()
        hnd <- getMaudeHandle
        se  <- gets id
        (eqs2, maySplitId) <- addEqsLabeled siteLabel hnd eqs1 =<< getM sEqStore
        setM sEqStore
            =<< simp hnd (substCreatesNonNormalTerms hnd se)
            =<< case (maySplitId, splitStrat) of
                  (Just splitId, SplitNow) ->
                      let arms = fromJustNote "solveTermEqs" $ performSplit eqs2 splitId
                          armN = length arms
                      in do
                          when (armN > 1 && Unsafe.unsafePerformIO
                                    (maybe False (== "1") <$>
                                     SysEnv.lookupEnv "TAM_HS_DBG_STE_MULTI")) $
                              Debug.Trace.traceM ("[HS_STE_MULTI] arms=" ++ show armN
                                  ++ " site=" ++ siteLabel
                                  ++ " n_eqs=" ++ show (length eqs1))
                          disjunctionOfList arms
                  (Just splitId, SplitLater) -> do
                      insertGoal (SplitG splitId) False
                      return eqs2
                  _                        -> return eqs2
        noContradictoryEqStoreLabeled siteLabel
        return Changed

-- | Add a list of equalities in substitution form to the equation store
solveSubstEqs :: SplitStrategy -> LNSubst -> Reduction ChangeIndicator
solveSubstEqs split subst =
    solveTermEqsLabeled "solveSubstEqs" split [Equal (varTerm v) t | (v, t) <- substToList subst]

-- | Add a list of node equalities to the equation store.
solveNodeIdEqs :: [Equal NodeId] -> Reduction ChangeIndicator
solveNodeIdEqs = solveTermEqsLabeled "solveNodeIdEqs" SplitNow . map (fmap varTerm)

-- | Add a list of fact equalities to the equation store, if possible.
solveFactEqs :: SplitStrategy -> [Equal LNFact] -> Reduction ChangeIndicator
solveFactEqs split eqs = solveFactEqsLabeled "solveFactEqs.default" split eqs

-- | Add a list of rule equalities to the equation store, if possible.
solveRuleEqs :: SplitStrategy -> [Equal RuleACInst] -> Reduction ChangeIndicator
solveRuleEqs split eqs = do
    T.contradictoryIfT "solveRuleEqs:ruleInfoMismatch"
        (not $ all evalEqual $ map (fmap (get rInfo)) eqs)
    solveListEqs (solveFactEqsLabeled "solveRuleEqs" split) $
        map (fmap (get rConcs)) eqs ++ map (fmap (get rPrems)) eqs
        ++ map (fmap (get rActs)) eqs

solveFactEqsLabeled :: String -> SplitStrategy -> [Equal LNFact] -> Reduction ChangeIndicator
solveFactEqsLabeled siteLabel split eqs = do
    T.contradictoryIfT "solveFactEqs:tagMismatch"
        (not $ all evalEqual $ map (fmap factTag) eqs)
    solveListEqs (solveTermEqsLabeled siteLabel split) $ map (fmap factTerms) eqs

-- | Solve a number of equalities between lists interpreted as free terms
-- using the given solver for solving the entailed per-element equalities.
solveListEqs :: ([Equal a] -> Reduction b) -> [(Equal [a])] -> Reduction b
solveListEqs solver eqs = do
    T.contradictoryIfT "solveListEqs:lengthMismatch"
        (not $ all evalEqual $ map (fmap length) eqs)
    solver $ concatMap flatten eqs
  where
    flatten (Equal l r) = zipWith Equal l r

-- | Solve the constraints associated with a rule.
solveRuleConstraints :: Maybe RuleACConstrs -> Reduction ()
solveRuleConstraints (Just eqConstr) = do
    hnd <- getMaudeHandle
    when (Unsafe.unsafePerformIO $
            maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_DBG_SOLVE_RULE_CONSTRAINTS") $ do
        let Disj substs = eqConstr
        Debug.Trace.traceM ("[HS_SOLVE_RULE_CONSTRAINTS] n_substs=" ++ show (length substs))
    (eqs, splitId) <- addRuleVariants eqConstr <$> getM sEqStore
    insertGoal (SplitG splitId) False
    -- do not use expensive substCreatesNonNormalTerms here
    setM sEqStore =<< simp hnd (const (const False)) eqs
    noContradictoryEqStoreLabeled "solveRuleConstraints"
solveRuleConstraints Nothing = return ()

-- | Like noContradictoryEqStore but tags the [CONTRA-DUMP] trace with
-- the calling site label so we can attribute contradictions to specific
-- HS code paths.
noContradictoryEqStoreLabeled :: String -> Reduction ()
noContradictoryEqStoreLabeled siteLabel = do
    isfalse <- eqsIsFalse <$> getM sEqStore
    when (isfalse && T.flagContra) $ do
        sys <- gets id
        Debug.Trace.traceM $ "[CONTRA-DUMP] label=noContradictoryEqStore:eqsIsFalse"
          ++ " site=" ++ siteLabel
          ++ " nodes=" ++ show (M.size (get sNodes sys))
          ++ " edges=" ++ show (S.size (get sEdges sys))
          ++ " formulas=" ++ show (S.size (get sFormulas sys))
          ++ " goals=" ++ show (M.size (get sGoals sys))
    T.contradictoryIfT ("noContradictoryEqStore:eqsIsFalse:" ++ siteLabel) isfalse
