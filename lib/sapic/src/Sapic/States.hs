-- |
-- Copyright   : (c) 2019 Charlie Jacomme and Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--

module Sapic.States
  ( annotatePureStates
  , hasBoundUnboundStates
  ) where

import Sapic.Annotation

import Theory
import Theory.Sapic

import Data.Set qualified as S
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import Data.List qualified as L
import Control.Monad.Fresh

-- Returns all states identifiers that are completely bound by names, when there is no states with a free identifier

isBound :: S.Set LVar -> SapicTerm -> Bool
isBound boundNames t = S.fromList (frees $ toLNTerm t) `S.isSubsetOf` boundNames

hasBoundUnboundStates ::  LProcess (ProcessAnnotation LVar) -> (Bool, Bool)
hasBoundUnboundStates p = (bounds /= S.empty, unbounds /= S.empty)
  where (bounds, unbounds) = getAllStates p S.empty

getAllStates ::  LProcess (ProcessAnnotation LVar) ->  S.Set LVar-> (S.Set SapicTerm, S.Set SapicTerm)
getAllStates (ProcessAction (Insert t _) _ p) boundNames | isBound boundNames t = (S.insert t boundStates, freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Insert t _) _ p) boundNames  = (boundStates, S.insert t freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Lock t) _ p) boundNames | isBound boundNames t = (S.insert t boundStates, freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Lock t) _ p) boundNames  = (boundStates, S.insert t freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Unlock t) _ p) boundNames | isBound boundNames t = (S.insert t boundStates, freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames
getAllStates (ProcessAction (Unlock t ) _ p) boundNames  = (boundStates, S.insert t freeStates)
  where (boundStates,freeStates) = getAllStates p boundNames


getAllStates (ProcessAction (Delete t) _ p) boundNames
  | isBound boundNames t = (S.insert t boundStates, freeStates)
  | otherwise = (boundStates, S.insert t freeStates)
  where (boundStates, freeStates) = getAllStates p boundNames

getAllStates (ProcessAction (New (SapicLVar v _)) _ p) boundNames = getAllStates p (v `S.insert` boundNames)
getAllStates (ProcessAction _ _ p) boundNames = getAllStates p boundNames
getAllStates (ProcessNull _) _ = (S.empty, S.empty)

getAllStates (ProcessComb  (Lookup t _)  _ pl pr) boundNames | isBound boundNames t  =
  (t `S.insert` boundStatesL `S.union` boundStatesR, freeStatesL `S.union` freeStatesR)
  where (boundStatesL,freeStatesL) = getAllStates pl boundNames
        (boundStatesR,freeStatesR) = getAllStates pr boundNames
getAllStates (ProcessComb  (Lookup t _)  _ pl pr) boundNames  =
  (boundStatesL `S.union` boundStatesR, t `S.insert`  freeStatesL `S.union` freeStatesR)
  where (boundStatesL,freeStatesL) = getAllStates pl boundNames
        (boundStatesR,freeStatesR) = getAllStates pr boundNames


getAllStates (ProcessComb _ _ pl pr) boundNames =
    (boundStatesL `S.union` boundStatesR, freeStatesL `S.union` freeStatesR)
  where (boundStatesL,freeStatesL) = getAllStates pl boundNames
        (boundStatesR,freeStatesR) = getAllStates pr boundNames



-- State channels declaration
-- We first go once into the process, to add where need the channel identifiers for each required state.

type StateMap = M.Map SapicTerm (AnVar LVar)

stateChannelName :: String
stateChannelName = "StateChannel"

addStatesChannels ::  LProcess (ProcessAnnotation LVar) -> LProcess (ProcessAnnotation LVar)
addStatesChannels p = evalFresh (declareStateChannel p (S.toList allBoundStates) S.empty M.empty) initStateChan
 where
   allBoundStates =  fst $ getAllStates p S.empty
   initState = avoidPreciseVars . map (\(SapicLVar lvar _) -> lvar) $ S.toList $ varsProc p
   initStateChan = fromMaybe 0 (M.lookup stateChannelName initState)

-- Descends into a process. Whenever all the names of a state term are declared, we declare a name corresponding to this state term, that will be used as the corresponding channel name.
declareStateChannel ::  MonadFresh m => LProcess (ProcessAnnotation LVar) -> [SapicTerm] -> S.Set SapicLVar -> StateMap -> m (LProcess (ProcessAnnotation LVar))
declareStateChannel p toDeclare boundNames stateMap =
  let (declarables, undeclarables) =  L.partition (\v -> S.fromList (freesSapicTerm v) `S.isSubsetOf` boundNames) toDeclare in
  if null declarables then  do
    case p of
      ProcessNull _ -> return p
      ProcessComb a an pl pr -> do
        pl' <- declareStateChannel pl toDeclare boundNames stateMap
        pr' <- declareStateChannel pr toDeclare boundNames stateMap
        case a of
          Lookup t _ -> return $ ProcessComb a an{  stateChannel = M.lookup t stateMap} pl' pr'
          _ -> return $ ProcessComb a an pl' pr'
      ProcessAction (New var) an pr -> do
        pr' <-  declareStateChannel pr toDeclare (var `S.insert` boundNames) stateMap
        return $ ProcessAction (New var) an pr'

      ProcessAction act an pr -> do
        pr' <- declareStateChannel pr toDeclare boundNames stateMap
        case act of
          Insert t _   -> return $ ProcessAction act an{ stateChannel = M.lookup t stateMap} pr'
          Lock t  -> return $ ProcessAction act an{ stateChannel = M.lookup t stateMap} pr'
          Unlock t  -> return $ ProcessAction act an{ stateChannel = M.lookup t stateMap} pr'
          _  -> return $ ProcessAction act an pr'
  else do
    (newvars, newMap) <- newStates p declarables [] stateMap
    p' <- declareStateChannel p undeclarables boundNames newMap
    return $ addNews p' newvars
      where addNews pr [] = pr
            addNews pr ((var, term):d) = ProcessAction (New (SapicLVar var (Just "channel"))) mempty{ isStateChannel = Just term } (addNews pr d)

newStates :: MonadFresh m =>  LProcess (ProcessAnnotation LVar) -> [SapicTerm] -> [(LVar, SapicTerm)]
  -> StateMap -> m ([(LVar, SapicTerm)], StateMap)
newStates _ [] declared stateMap = return (declared, stateMap)
newStates p (v:declarables) declared stateMap = do
    newvar <-  freshLVar stateChannelName LSortMsg
--    let  newslvar = SapicLVar newvar (Just "channel")
    let newMap =  M.insert v (AnVar newvar) stateMap
    newStates p declarables ((newvar, v):declared) newMap



-- We now have a process with defined states channels. We want to optimize on pure states, that is
-- a state channel such that, 1) there is a single insert outside of a lock (this is the state initialisation); 2) every occurence of the state channel is either lock t; lookup t or insert t; unlock t.

-- A pure cell has one initial value, followed by locked read/write sections.
-- Outside that fragment the ordinary translation retains overwrite, deletion,
-- and lookup-failure semantics through restrictions.
data CellPhase = InitializerAllowed | InitializerForbidden | Ready | Locked
  deriving (Eq)

isPureState :: LProcess (ProcessAnnotation LVar) -> SapicTerm -> Bool
isPureState p target = check InitializerAllowed p
  where
    check phase proc = case proc of
      ProcessAction (Insert t _) _ rest
        | t == target, phase == InitializerAllowed -> check Ready rest
      ProcessAction (Lock t) _ (ProcessComb (Lookup t' _) _ body (ProcessNull _))
        | t == target, t' == target, phase == Ready -> check Locked body
      ProcessAction (Insert t _) _ (ProcessAction (Unlock t') _ rest)
        | t == target, t' == target, phase == Locked -> check Ready rest
      _ | accessesTarget proc -> False
      -- Replication/parallel prohibit initialization and cannot fork a held
      -- lock. A fresh cell inside replication is checked at its declaration.
      ProcessAction Rep _ rest -> phase /= Locked && check (withoutInit phase) rest
      ProcessComb Parallel _ left right ->
        phase /= Locked && check (withoutInit phase) left && check (withoutInit phase) right
      ProcessAction _ _ rest -> check phase rest
      ProcessComb _ _ left right -> check phase left && check phase right
      -- Terminating while holding the cell also leaves the original lock held.
      ProcessNull _ -> True
    withoutInit InitializerAllowed = InitializerForbidden
    withoutInit phase = phase
    accessesTarget proc = case proc of
      ProcessAction (Insert t _) _ _ -> t == target
      ProcessAction (Lock t) _ _ -> t == target
      ProcessAction (Unlock t) _ _ -> t == target
      ProcessAction (Delete t) _ _ -> t == target
      ProcessComb (Lookup t _) _ _ _ -> t == target
      _ -> False

annotatePureStates :: LProcess (ProcessAnnotation LVar)  -> LProcess (ProcessAnnotation LVar)
annotatePureStates p
  -- A variable state key may alias an otherwise pure cell.
  | not (S.null freeStates) = addStatesChannels p
  | S.null boundStates = p
  | otherwise = annotateEachPureStates (addStatesChannels p) S.empty
  where (boundStates, freeStates) = getAllStates p S.empty


-- | Annotate every access to cells with a supported access pattern.
annotateEachPureStates :: LProcess (ProcessAnnotation LVar) -> S.Set SapicTerm -> LProcess (ProcessAnnotation LVar)
annotateEachPureStates (ProcessNull an) _ = ProcessNull an
annotateEachPureStates (ProcessComb comb an pl pr ) pureStates
  | Lookup t _ <- comb =
      if t `S.member` pureStates then
            ProcessComb comb an{pureState=True} pl' pr'
      else
            ProcessComb comb an pl' pr'
  | otherwise = ProcessComb comb an pl' pr'
            where
              pl' = annotateEachPureStates pl pureStates
              pr' = annotateEachPureStates pr pureStates
annotateEachPureStates (ProcessAction ac an p) pureStates
  | New _ <- ac, Just cid <- an.isStateChannel =
      if isolatedCell cid && isPureState p cid then
        ProcessAction ac an{pureState=True, isStateChannel = Just cid} (annotateEachPureStates p (cid `S.insert` pureStates))
      else
        ProcessAction ac an p'
  | Unlock t <- ac =
      if t `S.member` pureStates then
        ProcessAction ac an{pureState=True} p'
      else
        ProcessAction ac an p'
  | Lock t <- ac =
      if t `S.member` pureStates then
        ProcessAction ac an{pureState=True} p'
      else
        ProcessAction ac an p'
  | Insert t _ <- ac =
      if t `S.member` pureStates then
        ProcessAction ac an{pureState=True} p'
      else
        ProcessAction ac an p'
  | otherwise = ProcessAction ac an p'
  where
    p' = annotateEachPureStates p pureStates
    -- Syntactic comparisons suffice for a fresh-name key only if no other
    -- state key contains that name (and might reduce to it).
    isolatedCell t = case viewTerm t of
      Lit (Var v) -> all (\other -> other == t ||
                         toLVar v `notElem` frees (toLNTerm other))
                        (S.toList $ uncurry S.union $ getAllStates p S.empty)
      _ -> False
