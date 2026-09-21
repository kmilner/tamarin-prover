{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}

module Prover (
    module Prover
    , mkSystem
) where

import           Prelude                             hiding (id, (.))

import qualified Data.Map                            as M
import           Data.Functor.Identity (Identity(..))
import           Data.Maybe
import qualified Data.Set                            as S

import           Control.Basics
import           Control.Category
import           Control.Monad.Reader
import qualified Control.Monad.State                 as MS
import           Control.Parallel.Strategies

import           Extension.Data.Label                hiding (get)
import qualified Extension.Data.Label                as L
-- import qualified Data.Label.Total


import           Theory.Model
import           Theory.Proof
import           Theory.Text.Pretty
import           Theory.Tools.AbstractInterpretation
import           Theory.Tools.LoopBreakers
import           Theory.Tools.RuleVariants           (variantsProtoRule)
import           Lemma
import           PreparedDiffTheory
import           ClosedTheory
import           TheoryObject
import           OpenTheory

import           CloseRule

import           Theory.Constraint.Solver.Sources     as Sources (IntegerParameters(..))

-- | Close a theory by closing its associated rule set and checking the proof
-- skeletons and caching AC variants as well as precomputed case distinctions.
--
-- This function initializes the relation to the Maude process with the
-- correct signature. This is the right place to do that because in a closed
-- theory the signature may not change any longer.
closeTheory :: FilePath         -- ^ Path to the Maude executable.
            -> OpenTranslatedTheory
            -> Bool             -- ^ Try to auto-generate sources lemmas
            -> IO ClosedTheory
closeTheory maudePath thy0 autosources = do
    sig <- toSignatureWithMaude maudePath $ L.get thySignature thy0
    return $ closeTheoryWithMaude sig thy0 autosources True



-- | Close a theory by closing its associated rule set and checking the proof
-- skeletons and caching AC variants as well as precomputed case distinctions.
--
-- This function initializes the relation to the Maude process with the
-- correct signature. This is the right place to do that because in a closed
-- theory the signature may not change any longer.
closeDiffTheory :: FilePath         -- ^ Path to the Maude executable.
            -> OpenDiffTheory
            -> Bool
            -> IO ClosedDiffTheory
closeDiffTheory maudePath thy0 autoSources = do
    sig <- toSignatureWithMaude maudePath $ L.get diffThySignature thy0
    return $ closeDiffTheoryWithMaude sig thy0 autoSources

-- | Close a diff theory given a maude signature. This signature must be valid for
-- the given theory.
closeDiffTheoryWithMaude :: SignatureWithMaude -> OpenDiffTheory -> Bool -> ClosedDiffTheory
closeDiffTheoryWithMaude sig thy0 = closePreparedDiffTheory (prepareDiffTheory sig thy0)

-- | Close using the exact preparation consumed by wellformedness checking.
closePreparedDiffTheory :: PreparedDiffTheory -> Bool -> ClosedDiffTheory
closePreparedDiffTheory prepared autoSources =
  if autoSources && (containsPartialDeconstructions (cacheLeft items) || containsPartialDeconstructions (cacheRight items))
    then
      proveDiffTheory (const True) checkProofM checkDiffProof
        (DiffTheory (L.get diffThyName thy0) (L.get diffThyInFile thy0) h t sig (cacheLeft items') (cacheRight items') (diffCacheLeft items') (diffCacheRight items') items' (L.get diffThyOptions thy0) (_diffThyIsSapic thy0))
    else
      proveDiffTheory (const True) checkProofM checkDiffProof
        (DiffTheory (L.get diffThyName thy0) (L.get diffThyInFile thy0) h t sig (cacheLeft items) (cacheRight items) (diffCacheLeft items) (diffCacheRight items) items (L.get diffThyOptions thy0) (_diffThyIsSapic thy0))

  where
    thy0 = preparedDiffTheory prepared
    sig = preparedDiffSignature prepared
    parameters = Sources.IntegerParameters (L.get (openChainsLimit . diffThyOptions) thy0) (L.get (saturationLimit . diffThyOptions) thy0) True
    h              = L.get diffThyHeuristic thy0
    t              = L.get diffThyTactic thy0
    diffCacheLeft  its = closeRuleCache parameters restrictionsLeft  (typAsms LHS its) S.empty sig (leftClosedRules its)  (L.get diffThyDiffCacheLeft  thy0) (L.get (verboseOption . diffThyOptions) thy0) True (L.get diffThyIsSapic thy0)
    diffCacheRight its = closeRuleCache parameters restrictionsRight (typAsms RHS its) S.empty sig (rightClosedRules its) (L.get diffThyDiffCacheRight thy0) (L.get (verboseOption . diffThyOptions) thy0) True (L.get diffThyIsSapic thy0)
    cacheLeft  its = closeRuleCache parameters restrictionsLeft  (typAsms LHS its) S.empty sig (leftClosedRules its)  (L.get diffThyCacheLeft  thy0) (L.get (verboseOption . diffThyOptions) thy0) False (L.get diffThyIsSapic thy0)
    cacheRight its = closeRuleCache parameters restrictionsRight (typAsms RHS its) S.empty sig (rightClosedRules its) (L.get diffThyCacheRight thy0) (L.get (verboseOption . diffThyOptions) thy0) False (L.get diffThyIsSapic thy0)

    checkProofM = checkAndExtendProver (sorryProver Nothing)
    checkDiffProof = checkAndExtendDiffProver (sorryDiffProver Nothing)
    -- Maude / Signature handle
    hnd = L.get sigmMaudeHandle sig

    theoryItems = preparedDiffItems prepared
    -- Close all theory items: in parallel (especially useful for variants)
    --
    -- NOTE that 'rdeepseq' is OK here, as the proof has not yet been checked
    -- and therefore no constraint systems will be unnecessarily cached.
    items = (`runReader` hnd) $ addSolvingLoopBreakers
       ((closeDiffTheoryItem <$> theoryItems) `using` parList rdeepseq)

    closeDiffTheoryItem :: DiffTheoryItem ClosedDiffRule ClosedRuleFamily DiffProofSkeleton ProofSkeleton -> DiffTheoryItem ClosedDiffRule ClosedRuleFamily IncrementalDiffProof IncrementalProof
    closeDiffTheoryItem = foldDiffTheoryItem
      DiffRuleItem
      EitherRuleItem
      (DiffLemmaItem . fmap skeletonToIncrementalDiffProof)
      (\(s, l) -> EitherLemmaItem
          (s, fmap skeletonToIncrementalProof $ applyMacroInLemma (diffTheoryMacros thy0) l))
      (\(s, r) -> EitherRestrictionItem
          (s, applyMacroInRestriction (diffTheoryMacros thy0) r))
      DiffMacroItem
      DiffTextItem
      DiffConfigBlockItem

    -- Name of the auto-generated lemma
    lemmaName = "AUTO_typing"

    itemsModAC = unfoldRules items

    unfoldRules = map $ runIdentity . traverseDiffRuleMembers
      (\_ e ac -> pure $ map (L.get cprRuleAC) (unfoldRuleVariants (ClosedProtoRule e ac)))

    items' = addAutoSourcesLemmaDiff hnd lemmaName (cacheLeft itemsModAC) (cacheRight itemsModAC) itemsModAC

    -- extract source restrictions and lemmas
    restrictionsLeft  = do EitherRestrictionItem (LHS, rstr) <- items
                           return $ formulaToGuarded_ $ L.get rstrFormula rstr
    restrictionsRight = do EitherRestrictionItem (RHS, rstr) <- items
                           return $ formulaToGuarded_ $ L.get rstrFormula rstr
    typAsms side its = do
      EitherLemmaItem (lemmaSide, lem) <- its
      guard (side == lemmaSide)
      guard (isSourceLemma lem)
      return $ formulaToGuarded_ $ L.get lFormula lem

    leftClosedRules = concatMap (diffItemSideRules LHS)
    rightClosedRules = concatMap (diffItemSideRules RHS)

    -- Loop-breaker analysis still sees the same side/rule pairs, but writes
    -- its annotations back into owned members rather than detached items.
    addSolvingLoopBreakers its = do
      let rules = [(side,ru) | item <- its, side <- [LHS,RHS], ru <- diffItemSideRules side item]
      (annotated, _, _) <- useAutoLoopBreakersAC
        (enumPrems . L.get cprRuleAC . snd)
        (enumConcs . L.get cprRuleAC . snd)
        (getDisj . L.get (pracVariants . rInfo . cprRuleAC) . snd)
        (\bs (side,ru) -> (side, L.set (pracLoopBreakers . rInfo . cprRuleAC) bs ru)) rules
      let updated = M.fromList $ zip rules (map (L.get cprRuleAC . snd) annotated)
      pure $ map (runIdentity . traverseDiffRuleMembers
        (\side e ac -> pure [updated M.! (side, ClosedProtoRule e ac)])) its

-- | Prove both the assertion soundness as well as all lemmas of the theory. If
-- the prover fails on a lemma, then its proof remains unchanged.
proveDiffTheory :: (forall l. (HasLemmaName l, HasLemmaAttributes l) => l -> Bool)       -- ^ Lemma selector.
                   -> Prover
                   -> DiffProver
                   -> ClosedDiffTheory
                   -> ClosedDiffTheory
proveDiffTheory selector prover diffprover thy =
    modify diffThyItems ((`MS.evalState` []) . mapM prove) thy
  where
    prove item = case item of
      EitherLemmaItem (s, l0) -> do l <- MS.gets (\x -> EitherLemmaItem (s, (proveLemma s l0 x)))
                                    MS.modify (l :)
                                    return l
      DiffLemmaItem l0        -> do l' <- MS.gets (\x -> DiffLemmaItem (proveDiffLemma l0 x))
                                    MS.modify (l' :)
                                    return l'
      _                       -> do return item

    proveLemma s lem preItems
      | selector lem = modify lProof add lem
      | otherwise    = lem
      where
        ctxt    = getProofContextDiff s lem thy
        sys     = mkSystemDiff s ctxt (diffTheoryRestrictions thy) preItems $ L.get lFormula lem
        add prf = fromMaybe prf $ runProver prover ctxt 0 sys prf

    proveDiffLemma lem preItems
      | selector lem = modify lDiffProof add lem
      | otherwise        = lem
      where
        ctxt    = getDiffProofContext lem thy
        sys     = mkDiffSystem ctxt (diffTheoryRestrictions thy) preItems
        add prf = fromMaybe prf $ runDiffProver diffprover ctxt 0 sys prf


-- | Construct a constraint system for verifying the given formula.
mkSystemDiff :: Side -> ProofContext -> [(Side, Restriction)] -> [DiffTheoryItem r r2 p p2]
         -> LNFormula -> System
mkSystemDiff s ctxt restrictions previousItems =
    -- Note that it is OK to add reusable lemmas directly to the system, as
    -- they do not change the considered set of traces. This is the key
    -- difference between lemmas and restrictions.
    addLemmasLocal
  . formulaToSystem (map (formulaToGuarded_ . L.get rstrFormula) restrictions')
                    (L.get pcSourceKind ctxt)
                    (L.get pcTraceQuantifier ctxt) False
  where
    restrictions' = foldr (\(s', a) l -> if s == s' then l ++ [a] else l) [] restrictions
    addLemmasLocal sys =
        insertLemmas (gatherReusableLemmas $ L.get sSourceKind sys) sys

    gatherReusableLemmas kind = do
        EitherLemmaItem (s'', lem) <- previousItems
        guard $    lemmaSourceKind lem <= kind && s==s''
                && ReuseLemma `elem` L.get lAttributes lem
                && AllTraces == L.get lTraceQuantifier lem
                && L.get lName lem `notElem` L.get pcHiddenLemmas ctxt
                && "ALL" `notElem` L.get pcHiddenLemmas ctxt
        return $ formulaToGuarded_ $ L.get lFormula lem

-- | Construct a diff constraint system.
mkDiffSystem :: DiffProofContext -> [(Side, Restriction)] -> [DiffTheoryItem r r2 p p2]
        -> DiffSystem
mkDiffSystem _ _ _ = emptyDiffSystem


-- Partial evaluation / abstract interpretation
-----------------------------------------------

-- | Export disposition for one original rule family.
data PartialEvaluationFamilyPlan
    = KeepOriginal
    | EmitRefinements [ProtoRuleE]

-- | Apply partial evaluation.
applyPartialEvaluation :: EvaluationStyle -> Bool -> ClosedTheory -> ClosedTheory
applyPartialEvaluation evalStyle autosources thy0 =
    closeTheoryWithMaude sig
      (removeTranslationItems (L.modify thyItems replaceProtoRules (openTheory thy0)))
      autosources True
  where
    sig          = L.get thySignature thy0
    originals = getProtoRuleEs thy0
    familyIds = M.fromList $ zip originals [0 :: Int ..]
    familyId ru = familyIds M.! ru
    -- Keep ownership separate from names: a generated variant name can also
    -- be the name of an independent E-rule. All imported variants belong to
    -- the same original E-rule, and this ID survives refinement and renaming.
    -- Parser/SAPIC insertion checks E-name uniqueness, but programmatic
    -- addRules/closeTheoryWithMaude callers need not, so names cannot be IDs.
    rules =
      [ fmap (\info -> (familyId (L.get cprRuleE ru), info))
          (compiledRule variant)
      | ru <- theoryRules thy0, variant <- unfoldRuleVariants ru ]
    originalRuleCount = length originals
    (st', rules') = (`runReader` L.get sigmMaudeHandle sig) $
                    partialEvaluation evalStyle rules

    -- A compiled AC variant is not necessarily an equivalent E-rule: exporting
    -- it as one can introduce further variants on reload, with the wrong added
    -- actions. Keep the original family if any refinement would change under
    -- E-variant computation. Restoring the complete family preserves its added
    -- actions and keeps manual-variant completeness checks applicable.
    -- Prepend each refinement, then restore family order once. Appending to
    -- the growing bucket would repeatedly copy its prefix.
    refinements = M.map reverse $ M.fromListWith (++)
      [ (fst (L.get rInfo ru), [fmap snd ru])
      | ru <- rules' ]
    -- Include pruned families explicitly, so deletion is never inferred from
    -- a missing lookup. All original rules have an entry, including duplicates.
    familyPlans = M.fromList
      [ (familyId ru, planFamily (M.findWithDefault [] (familyId ru) refinements))
      | ru <- originals ]
    planFamily rs
      | any (not . exportable) rs = KeepOriginal
      | otherwise = EmitRefinements rs
    exportable ru = case variantsProtoRule (L.get sigmMaudeHandle sig) ru of
      Just ac -> eqModuloFreshnessNoAC ac (compiledRuleAC ru)
      Nothing -> False

    -- Refinement can split one rule into several rules with the same name.
    -- Allocate distinct export names before closing the theory, so proofs and
    -- printed rules use the same names. Reserve even names of removed rules.
    namedFamilyPlans = MS.evalState (traverse nameFamily familyPlans)
      (retainedNames, reservedNames)
    nameFamily (EmitRefinements rs) = EmitRefinements <$> mapM nameRefinement rs
    nameFamily plan = return plan
    retainedNames = S.fromList
      [ getRuleName ru | ru <- originals,
                         KeepOriginal <- [familyPlans M.! familyId ru] ]
    reservedNames = S.fromList $ map getRuleName originals ++
      map (getRuleName . fmap snd) rules
    nameRefinement ru = do
      (used, reserved) <- MS.get
      let originalName = getRuleName ru
          name = if originalName `S.notMember` used then originalName else
            head [ candidate | i <- [1 :: Integer ..],
                   let candidate = originalName ++ "_PE_" ++ show i,
                   candidate `S.notMember` reserved ]
          renamed = if name == originalName then ru else
            L.set (preName . rInfo) (StandRule name) ru
      MS.put (S.insert name used, S.insert name reserved)
      return renamed

    replaceRule (RuleItem ru) = case namedFamilyPlans M.! owner of
      KeepOriginal -> [RuleItem ru]
      EmitRefinements rs -> map (RuleItem . openCompiledRule) rs
      where
        owner = familyId (L.get oprRuleE ru)
    replaceRule item = [item]

    replaceProtoRules [] = []
    replaceProtoRules (item:items)
      | isRuleItem item  =
          [ TextItem ("text", render ppAbsState)
          ] ++ concatMap replaceRule (item:items)
      | otherwise        = item : replaceProtoRules items

    retainedCount = length [() | KeepOriginal <- M.elems familyPlans]

    ppAbsState =
      (text $ " the abstract state after partial evaluation"
              ++ " contains " ++ show (S.size st') ++ " facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList st') $--$
      (text $ "This abstract state results in " ++ show (sum [length rs | EmitRefinements rs <- M.elems familyPlans]) ++
              " refined multiset rewriting rules.\n" ++
              (if retainedCount == 0 then "" else
                "Kept " ++ show retainedCount ++
                " original rule families to preserve their variants on export.\n") ++
              "Note that the original number of multiset rewriting rules was "
              ++ show originalRuleCount ++ ".\n\n")

-- | Analyze reachability for diagnostics. Diff correspondence requires complete
-- equation-variant families, so reachable refinements must not replace them.
applyPartialEvaluationDiff :: EvaluationStyle -> Bool -> ClosedDiffTheory -> ClosedDiffTheory
applyPartialEvaluationDiff evalStyle _autoSources thy0 =
    L.modify diffThyItems (DiffTextItem ("text", render ppAbsState) :) thy0
  where
    sig            = L.get diffThySignature thy0
    -- Group diagnostic refinements by their original family name: generated
    -- variant numbers are side-local and would prevent deduplication here.
    -- These renamed rules are never consumed by diff proof search.
    rules s        = concatMap familyVariants (diffTheorySideRules s thy0)
    familyVariants cru =
      map (L.set (preName . rInfo) (L.get (preName . rInfo . cprRuleE) cru)
           . removeGeneratedDiffLabel ("DiffProto" ++ getRuleName (L.get cprRuleE cru)))
          (map compiledRule (unfoldRuleVariants cru))
    originalRuleCount s = length (getProtoRuleEsDiff s thy0)
    (stL', rulesL') = (`runReader` L.get sigmMaudeHandle sig) $
                      partialEvaluation evalStyle (rules LHS)
    (stR', rulesR') = (`runReader` L.get sigmMaudeHandle sig) $
                      partialEvaluation evalStyle (rules RHS)

    ppAbsState =
      (text $ " the abstract state after partial evaluation"
              ++ " contains " ++ show (S.size stL') ++ " left facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList stL') $--$
      (text $ "Partial evaluation proposed " ++ show (length rulesL') ++
              " left refined multiset rewriting rules.\n" ++
              "Note that the original number of multiset rewriting rules was "
              ++ show (originalRuleCount LHS) ++ ".\n\n") $--$
      (text $ " the abstract state after partial evaluation"
              ++ " contains " ++ show (S.size stR') ++ " right facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList stR') $--$
      (text $ "Partial evaluation proposed " ++ show (length rulesR') ++
              " right refined multiset rewriting rules.\n" ++
              "Note that the original number of multiset rewriting rules was "
              ++ show (originalRuleCount RHS) ++ ".\n\n" ++
              "Diff partial evaluation is analysis-only; original equation-variant " ++
              "families are retained.\n")

-- Partial evaluation only needs unification modulo AC when it starts from the
-- already computed E-variants. Representing each compiled variant as an E-rule
-- lets us reinstall its refined AC rule without recomputing or losing imported
-- variants. Embedded restrictions are already separate theory items here; an
-- empty local list avoids inferring monotonicity from a restriction whose
-- variables were renamed while its E-variant was computed.
compiledRule :: ClosedProtoRule -> ProtoRuleE
compiledRule cru = case L.get cprRuleAC cru of
  Rule info prems concs acts newVars ->
    Rule (ProtoRuleEInfo
            (L.get pracName info)
            (L.get pracAttributes info)
            [])
         prems concs acts newVars

openCompiledRule :: ProtoRuleE -> OpenProtoRule
openCompiledRule ruE = OpenProtoRule ruE [compiledRuleAC ruE]

compiledRuleAC :: ProtoRuleE -> ProtoRuleAC
compiledRuleAC (Rule eInfo prems concs acts newVars) =
    Rule acInfo prems concs acts newVars
  where
    acInfo = ProtoRuleACInfo
               (L.get preName eInfo)
               (L.get preAttributes eInfo)
               (Disj [emptySubstVFresh])
               []


-- | Open a theory by dropping the closed world assumption and values whose
-- soundness depends on it.
openTheory :: ClosedTheory -> OpenTheory
openTheory  (Theory n f h t sig c items opts sapic) = openTranslatedTheory(
    Theory n f h t (toSignaturePure sig) (openRuleCache c)
    -- We merge duplicate rules if they were split into variants
      (mergeOpenProtoRules $ map (mapTheoryItem openProtoRule incrementalToSkeletonProof) items)
      opts sapic)

-- | Open a theory by dropping the closed world assumption and values whose
-- soundness depends on it.
openDiffTheory :: ClosedDiffTheory -> OpenDiffTheory
openDiffTheory = openDiffTheoryWith openDiffRuleFamily

-- | Reopen for text export, encoding complete explicit families where the
-- original E-rule alone would lose compiled behavior or annotations.
exportDiffTheory :: ClosedDiffTheory -> OpenDiffTheory
exportDiffTheory thy = openDiffTheoryWith
    (exportDiffRuleFamily (L.get (sigmMaudeHandle . diffThySignature) thy)) thy

openDiffTheoryWith :: (ClosedRuleFamily -> OpenProtoRule) -> ClosedDiffTheory -> OpenDiffTheory
openDiffTheoryWith reopen (DiffTheory n f h t sig c1 c2 c3 c4 items opts sapic) =
    DiffTheory n f h t (toSignaturePure sig) (openRuleCache c1) (openRuleCache c2) (openRuleCache c3) (openRuleCache c4)
      (map (mapDiffTheoryItem id id (\(DiffLemma s a p) -> (DiffLemma s a (incrementalToSkeletonDiffProof p))) (\(x, Lemma a p m b c c' d e) -> (x, Lemma a p m b c c' d (incrementalToSkeletonProof e))))
           (map (mapDiffTheoryItem (openClosedDiffRule reopen) (fmap reopen) id id) items))
      opts sapic

------------------------------------------------------------------------------
-- References to lemmas
------------------------------------------------------------------------------

-- | Lemmas are referenced by their name.
type LemmaRef = String

-- | Resolve a path in a theory.
lookupLemmaProof :: LemmaRef -> ClosedTheory -> Maybe IncrementalProof
lookupLemmaProof name thy = L.get lProof <$> lookupLemma name thy


-- | Resolve a path in a diff theory.
lookupLemmaProofDiff :: Side -> LemmaRef -> ClosedDiffTheory -> Maybe IncrementalProof
lookupLemmaProofDiff s name thy = L.get lProof <$> lookupLemmaDiff s name thy


-- | Resolve a path in a diff theory.
lookupDiffLemmaProof :: LemmaRef -> ClosedDiffTheory -> Maybe IncrementalDiffProof
lookupDiffLemmaProof name thy = L.get lDiffProof <$> lookupDiffLemma name thy


-- | Modify the proof at the given lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyLemmaProof :: Prover -> LemmaRef -> ClosedTheory -> Maybe ClosedTheory
modifyLemmaProof prover name thy =
    modA thyItems changeItems thy
  where
    findLemma (LemmaItem lem) = name == L.get lName lem
    findLemma _               = False

    change preItems (LemmaItem lem) = do
         let ctxt = getProofContext lem thy
             sys  = mkSystem ctxt (theoryRestrictions thy) preItems $ L.get lFormula lem
         lem' <- modA lProof (runProver prover ctxt 0 sys) lem
         return $ LemmaItem lem'
    change _ _ = error "LemmaProof: change: impossible"

    changeItems items = case break findLemma items of
        (pre, i:post) -> do
             i' <- change pre i
             return $ pre ++ i':post
        (_, []) -> Nothing


-- | Modify the proof at the given lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyLemmaProofDiff :: Side -> Prover -> LemmaRef -> ClosedDiffTheory -> Maybe ClosedDiffTheory
modifyLemmaProofDiff s prover name thy =
    modA diffThyItems (changeItems s) thy
  where
    findLemma s'' (EitherLemmaItem (s''', lem)) = (name == L.get lName lem) && (s''' == s'')
    findLemma _ _                               = False

    change s'' preItems (EitherLemmaItem (s''', lem)) = if s''==s'''
        then
          do
            let ctxt = getProofContextDiff s'' lem thy
                sys  = mkSystemDiff s'' ctxt (diffTheoryRestrictions thy) preItems $ L.get lFormula lem
            lem' <- modA lProof (runProver prover ctxt 0 sys) lem
            return $ EitherLemmaItem (s''', lem')
        else
          error "LemmaProof: change: impossible"
    change _ _ _ = error "LemmaProof: change: impossible"

    changeItems s' items = case break (findLemma s') items of
        (pre, i:post) -> do
             i' <- change s' pre i
             return $ pre ++ i':post
        (_, []) -> Nothing


-- | Modify the proof at the given diff lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyDiffLemmaProof :: DiffProver -> LemmaRef -> ClosedDiffTheory -> Maybe ClosedDiffTheory
modifyDiffLemmaProof prover name thy = -- error $ show $ -- name ++ show thy
     modA diffThyItems changeItems thy
  where
    findLemma (DiffLemmaItem lem) = (name == L.get lDiffName lem)
    findLemma  _                  = False

    change preItems (DiffLemmaItem lem) =
          do
            -- I don't get why we need this here, but anyway the empty system does not seem to be a problem.
            let ctxt = getDiffProofContext lem thy
                sys  = mkDiffSystem ctxt (diffTheoryRestrictions thy) preItems
            lem' <- modA lDiffProof (runDiffProver prover ctxt 0 sys) lem
            return $ DiffLemmaItem lem'
    change _ _ = error "DiffLemmaProof: change: impossible"

    changeItems items = case break findLemma items of
        (pre, i:post) -> do
             i' <- change pre i
             return $ pre ++ i':post
        (_, []) -> Nothing
