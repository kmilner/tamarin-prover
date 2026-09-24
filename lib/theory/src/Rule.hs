{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Rule (
    module Rule
    ,module Items.RuleItem
)where

import Items.RuleItem

import Prelude                             hiding (id, (.))

import Control.Category

import qualified Extension.Data.Label                as L

import Theory.Model
import Theory.Proof
import Theory.Tools.RuleVariants

import Term.Macro
import Theory.Constraint.Solver.Sources (IntegerParameters)
import Data.Maybe (maybeToList)
import Data.List (nub)
import qualified Data.Map.Strict as M
import Control.Monad (foldM, guard)
import Control.Monad.Reader (runReader)

-- | Get an OpenProtoRule's name
getOpenProtoRuleName :: OpenProtoRule -> String
getOpenProtoRuleName (OpenProtoRule ruE _) = getRuleName ruE

-- | Add the diff label to an OpenProtoRule
addProtoDiffLabel :: OpenProtoRule -> String -> OpenProtoRule
addProtoDiffLabel (OpenProtoRule ruE ruAC) label = OpenProtoRule (addDiffLabel ruE label) (fmap ((flip addDiffLabel) label) ruAC)

-- | Closing appends one parent-owned label. Remove that final occurrence when
-- reopening, retaining any identically named actions supplied by the user.
removeGeneratedDiffLabel :: String -> Rule i -> Rule i
removeGeneratedDiffLabel label = L.modify rActs (reverse . removeFirst . reverse)
  where
    marker = protoFact Linear label []
    removeFirst [] = []
    removeFirst (fact:rest)
      | fact == marker = rest
      | otherwise = fact : removeFirst rest

-- Relation between open and closed rule sets
---------------------------------------------

-- | All intruder rules of a set of classified rules.
intruderRules :: ClassifiedRules -> [IntrRuleAC]
intruderRules rules = do
    Rule (IntrInfo i) ps cs as nvs <- joinAllRules rules
    return $ Rule i ps cs as nvs

-- | Open a rule cache. Variants and precomputed case distinctions are dropped.
openRuleCache :: ClosedRuleCache -> OpenRuleCache
openRuleCache = intruderRules . L.get crcRules

-- | Open a protocol rule; i.e., drop variants and proof annotations.
openProtoRule :: ClosedProtoRule -> OpenProtoRule
openProtoRule r = OpenProtoRule ruleE ruleAC
  where
    ruleE   = L.get cprRuleE r
    ruleAC' = L.get cprRuleAC r
    ruleAC  = if equalUpToTerms ruleAC' ruleE
               then []
               else [ruleAC']

-- | Unfold rule variants, i.e., return one ClosedProtoRule for each
-- variant
unfoldRuleVariants :: ClosedProtoRule -> [ClosedProtoRule]
unfoldRuleVariants (ClosedProtoRule ruE ruAC@(Rule ruACInfoOld ps cs as nvs))
   | isTrivialProtoVariantAC ruAC ruE = [ClosedProtoRule ruE ruAC]
   -- Supplied or previously unfolded members already have their own names.
   -- Re-unfolding their identity substitution must not append another suffix.
   | L.get pracVariants ruACInfoOld == Disj [emptySubstVFresh]
   , ruleName ruAC /= ruleName ruE = [ClosedProtoRule ruE ruAC]
   | otherwise = map toClosedProtoRule variants
        where
          ruACInfo i = ProtoRuleACInfo (rName i (L.get pracName ruACInfoOld)) rAttributes (Disj [emptySubstVFresh]) loopBreakers
          rAttributes = L.get pracAttributes ruACInfoOld
          loopBreakers = L.get pracLoopBreakers ruACInfoOld
          rName i oldName = case oldName of
            FreshRule -> FreshRule
            StandRule s -> StandRule $ s ++ "___VARIANT_" ++ show i

          toClosedProtoRule (i, (ps', cs', as', nvs'))
            = ClosedProtoRule ruE (Rule (ruACInfo i) ps' cs' as' nvs')
          variants = zip [1::Int ..] $ map (\x -> apply x (ps, cs, as, nvs)) $ substs (L.get pracVariants ruACInfoOld)
          substs (Disj s) = map (`freshToFreeAvoiding` ruAC) s

-- | Close a protocol rule; i.e., compute AC variant and source assertion
-- soundness sequent, if required.
closeProtoRule :: MaudeHandle -> [LNMacro] -> OpenProtoRule -> [ClosedProtoRule]
-- if there are no macros, we do not call applyMacroInRule to make sure that new vars are not overwritten (important for diff mode)
closeProtoRule hnd []     (OpenProtoRule ruE [])   = ClosedProtoRule ruE <$> maybeToList (variantsProtoRule hnd ruE)
closeProtoRule hnd macros (OpenProtoRule ruE [])   = ClosedProtoRule ruE <$> maybeToList (variantsProtoRule hnd (applyMacroInRule macros ruE))
closeProtoRule _   macros (OpenProtoRule ruE ruAC) =
    map (ClosedProtoRule ruE . applyMacroInRulePreservingNewVars macros) ruAC


-- | Recover a diff member's positional new-variable vector from its canonical
-- variant. Hidden parent slots can change the fresh indices used by unfolding,
-- so accept a bijective syntactic renaming of an explicit member as well.
-- Added actions are retained, and ambiguous alignments are rejected. This is
-- deliberately separate from trace-mode manual-variant validation.
diffVariantNewVars :: ProtoRuleAC -> ProtoRuleAC -> Maybe [LNTerm]
diffVariantNewVars supplied canonical
  -- Exact names preserve deliberate references to hidden parent variables in
  -- added actions, including annotations on an already compiled member.
  | equalUpToAddedActions supplied canonical && substitutions supplied == substitutions canonical =
      Just (L.get rNewVars canonical)
  | ruleName supplied /= ruleName canonical
    || substitutions supplied /= Disj [emptySubstVFresh]
    || substitutions canonical /= Disj [emptySubstVFresh] = Nothing
  | otherwise = do
      premises <- matchFacts M.empty (L.get rPrems supplied) (L.get rPrems canonical)
      initial <- matchFacts premises (L.get rConcs supplied) (L.get rConcs canonical)
      case take 2 $ nub [transport renaming | renaming <-
               matchActions initial (L.get rActs supplied) (L.get rActs canonical)] of
        [vector] -> Just vector
        _ -> Nothing
  where
    substitutions = L.get (pracVariants . rInfo)
    matchFacts env actual expected = do
      guard (length actual == length expected)
      foldM matchFactVariables env (zip actual expected)
    matchFactVariables env (Fact tag ann ts, Fact tag' ann' ps) = do
      guard (tag == tag' && ann == ann' && length ts == length ps)
      let actual = freesList ts
          expected = freesList ps
      guard (length actual == length expected)
      mapping <- foldM matchVariable env (zip actual expected)
      -- Term's Functor preserves the exact constructor order, including AC
      -- arguments. Substitution/mapFrees would normalize them and could admit
      -- an AC permutation that the syntactic matcher deliberately rejects.
      guard (map (fmap (fmap (mapping M.!))) ps == ts)
      pure mapping
    matchVariable env (target, source) = do
      guard (lvarSort target == lvarSort source)
      case M.lookup source env of
        Just previous -> guard (previous == target) >> pure env
        Nothing -> do
          guard (target `notElem` M.elems env)
          pure (M.insert source target env)
    matchActions env _ [] = [env]
    matchActions _ [] _ = []
    matchActions env (a:as) expected@(p:ps) =
      [result | next <- maybeToList (matchFactVariables env (a,p)),
                result <- matchActions next as ps]
      ++ matchActions env as expected
    transport env = apply (substFromList [(v,varTerm w) | (v,w) <- M.toList complete] :: LNSubst)
                          (L.get rNewVars canonical)
      where
        -- An invisible canonical variable must not capture an extra action's
        -- variable (or another transported slot) in the supplied member.
        complete = foldl addHidden env (frees (L.get rNewVars canonical))
        suppliedFacts = (L.get rPrems supplied, L.get rConcs supplied, L.get rActs supplied)
        addHidden mapping v
          | M.member v mapping = mapping
          | otherwise = M.insert v fresh mapping
          where
            fresh | v `notElem` frees suppliedFacts && v `notElem` M.elems mapping = v
                  | otherwise = renameAvoiding v (suppliedFacts, canonical, M.elems mapping)

-- | Prepare a supplied diff family with one shared match matrix. Coverage and
-- unique positional alignment and added-action checks use the same matches.
-- Invalid input retains its members for the usual wellformedness diagnostics.
prepareDiffRule :: MaudeHandle -> OpenProtoRule
                -> (OpenProtoRule, [(ProtoRuleAC, [LNFact])], Bool)
prepareDiffRule hnd (OpenProtoRule ruE supplied) =
    (OpenProtoRule ruE aligned, inheritedActions, null supplied || complete)
  where
    automatic = closeProtoRule hnd [] (OpenProtoRule ruE [])
    compact = map (L.get cprRuleAC) automatic
    unfolded = map (L.get cprRuleAC) (concatMap unfoldRuleVariants automatic)
    candidates = nub (compact ++ unfolded)
    matches = [[(c, vector) | c <- candidates, Just vector <- [diffVariantNewVars p c]]
              | p <- supplied]
    -- Keep the existing action alignment, but only for accepted candidates.
    -- Closing does not need this lazy result; validation consumes it once.
    inheritedActions =
      [ (member, inherited)
      | (member, accepted) <- zip aligned matches, (canonical, _) <- accepted
      , Just inherited <- [alignRuleUpToRenaming member canonical `runReader` hnd] ]
    vectors = map (nub . map snd) matches
    aligned = zipWith align supplied vectors
    align p [vector] = L.set rNewVars vector p
    align p _ = p
    unique [_] = True
    unique _ = False
    covered c = any (any ((== c) . fst)) matches
    -- A matching compact member represents its whole unfolded family.
    complete = all unique vectors &&
      (all covered compact || all covered unfolded)


-- | Returns true if the REFINED sources contain open chains.
containsPartialDeconstructions :: ClosedRuleCache    -- ^ Cached rules and case distinctions.
                     -> Bool               -- ^ Result
containsPartialDeconstructions (ClosedRuleCache _ _ cases _) =
      sum (map (sum . unsolvedChainConstraints) cases) /= 0

-- | Add an action to a closed Proto Rule.
--   Note that we only add the action to the variants modulo AC, not the initial rule.
addActionClosedProtoRule :: ClosedProtoRule -> LNFact -> ClosedProtoRule
addActionClosedProtoRule (ClosedProtoRule e ac) f
   = ClosedProtoRule e (addAction ac f)
