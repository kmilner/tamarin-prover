-- |
-- Copyright   : (c) 2019 Charlie Jacomme <charlie.jacomme@lsv.fr>
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Compute annotations for let destructors

module Sapic.LetDestructors
  ( translateLetDestr
  ) where

import           Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import           Data.List.NonEmpty (NonEmpty(..))

import           Sapic.Annotation
import           Sapic.Exceptions

import           Theory
import           Theory.Sapic

import           Term.SubtermRule

import           Control.Monad.Catch
import           Control.Monad.Fresh (MonadFresh)

-- | Extract proper-subterm destructors in left-to-right, innermost-first
-- order. The resulting plan stays on the original let: neither continuation
-- is copied, and root destructors are inverted against the source pattern.
splitTerm :: MonadFresh m => Bool -> SapicTerm -> m (SapicTerm, [(SapicTerm, SapicTerm)])
splitTerm extract t = do
  (term, build) <- split extract t
  return (term, build [])
  where
    -- Difference-list composition preserves postorder without copying each
    -- descendant prefix. mapM still allocates fresh variables left to right.
    split takeResult term = case viewTerm term of
      Lit _ -> return (term, id)
      FApp fs args -> do
        parts <- mapM (split True) args
        let rhs = fApp fs (map fst parts)
            bindings = foldr ((.) . snd) id parts
        case fs of
          NoEq (_, (_, _, Destructor, _)) | takeResult -> do
            v <- freshLVar "destructor" LSortMsg
            let result = varTerm (SapicLVar v Nothing)
            return (result, bindings . ((result, rhs) :))
          _ -> return (rhs, bindings)

-- Unsupported results remain indexed so only use of that symbol is rejected.
type DestructorEquations = M.Map FunSym (Either () [([LNTerm], LVar)])

mapProc :: (MonadThrow m, MonadFresh m) => DestructorEquations -> AnnotatedProcess -> m AnnotatedProcess
mapProc _ (ProcessNull ann) = return $ ProcessNull ann
mapProc rules (ProcessAction ac ann p') =
  ProcessAction ac ann <$> mapProc rules p'
mapProc rules (ProcessComb c@(Let lhs rhs mv) ann pl pr) = do
  (rhs', bindings) <- splitTerm False rhs
  plan <- stages (bindings ++ [(lhs, rhs')])
  case plan of
    -- No defining equation means evaluation necessarily fails. Do not visit
    -- unreachable later stages or the success continuation (which may itself
    -- contain an unsupported destructor).
    Nothing -> mapProc rules pr
    Just _ | null bindings, not (isDestructor rhs),
             LIT (Var svar) <- lhs, not (svar `S.member` mv) -> do
      res <- applyM (substFromList [(v, rhs) | v <- untypedVariants svar]) pl
      mapProc rules res
    Just steps -> do
      npl <- mapProc rules pl
      npr <- mapProc rules pr
      return $ ProcessComb c (ann {letPlan = steps, elseBranch = hasElse}) npl npr
  where
    hasElse = case pr of ProcessNull _ -> False; _ -> True
    isDestructor t = case viewTerm t of
      FApp (NoEq (_, (_, _, Destructor, _))) _ -> True
      _ -> False
    untypedVariants svar@(SapicLVar v (Just _)) = [svar, SapicLVar v Nothing]
    untypedVariants svar = [svar]
    stages [] = return $ Just []
    stages ((patternTerm, term):rest) = do
      let result = toLNTerm patternTerm
          bound = S.fromList $ frees result
      step <- case viewTerm (toLNTerm term) of
        FApp fs@(NoEq (_, (_, _, Destructor, _))) args ->
          case M.findWithDefault (Right []) fs rules of
            Left () -> throwM (NotImplementedError
              "SAPIC destructor equations with non-variable right-hand sides"
              :: SapicException AnnotatedProcess)
            Right [] -> return Nothing
            Right (equation:equations) ->
              let patternFor (leftterms, outvar) =
                    apply (substFromList [(outvar, result)]) (toPairs leftterms)
              in return $ Just $ LetStage (toPairs args)
                   (patternFor equation :| map patternFor equations) bound
        _ -> return $ Just $ LetStage (toLNTerm term) (result :| []) bound
      case step of
        Nothing -> return Nothing
        Just st -> fmap (st :) <$> stages rest
    -- List is reducible, so use constructor pairs for multi-argument matching.
    toPairs [] = fAppOne
    toPairs [s] = s
    toPairs (s:ss) = fAppPair (s, toPairs ss)
mapProc rules (ProcessComb c ann pl pr) =
  ProcessComb c ann <$> mapProc rules pl <*> mapProc rules pr

-- Index once, preserving equation order and the used-symbol validation rule.
indexEquations :: [LNTerm] -> Set CtxtStRule -> DestructorEquations
indexEquations avoidTerms = M.map (fmap (`renameAvoiding` avoidTerms))
                         . M.fromListWith (flip combine) . concatMap entry . S.toList
  where
    entry rule = case ctxtStRuleToRRule rule of
      lhs `RRule` rhs -> case viewTerm lhs of
        FApp fs args -> [(fs, case viewTerm rhs of
          Lit (Var v) -> Right [(args, v)]
          _ -> Left ())]
        _ -> []
    combine (Right xs) (Right ys) = Right (xs ++ ys)
    combine _ _ = Left ()

translateLetDestr :: MonadThrow m => Set CtxtStRule -> AnnotatedProcess -> m AnnotatedProcess
translateLetDestr rules p = evalFreshTAvoiding (mapProc indexed p) avoidVars
  where
    sourceVars = [varTerm v :: LNTerm | SapicLVar v _ <- S.toList $ varsProc p]
    indexed = indexEquations sourceVars rules
    -- Equation variables and internal temporaries occupy the same untyped
    -- namespace. Allocate temporaries after reserving the freshened equations.
    avoidVars = sourceVars ++
      [t | Right equations <- M.elems indexed, (args, v) <- equations,
           t <- varTerm v : args]
