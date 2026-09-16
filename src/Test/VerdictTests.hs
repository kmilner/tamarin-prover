-- Focused invariants at boundaries that can change proof verdicts.
module Test.VerdictTests (tests) where

import Data.List (isInfixOf, sort)
import Data.Maybe (fromJust)
import qualified Control.Category as C
import Control.Monad.Reader (runReader)
import Lemma
import Logic.Connectives (Disj(..))
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Extension.Data.Label as L
import Test.HUnit

import ClosedTheory
import Prover
import OpenTheory (prettyOpenDiffTheory, addIntrRuleLabels, getLeftProtoRule, getRightProtoRule,
                   addIntrRuleACsDiffBoth, addIntrRuleACsDiffBothDiff, addProtoRuleLabel, addDefaultDiffLemma)
import Rule
import Theory.Model
import Theory.Constraint.System
import Theory.Constraint.Solver.ProofMethod (execDiffProofMethod, DiffProofMethod(DiffRuleEquivalence))
import Theory.Text.Parser
import Theory.Text.Pretty (render)
import Theory.Tools.AbstractInterpretation (EvaluationStyle(Silent))
import Theory.Tools.IntruderRules (subtermConstructorRules, specialIntruderRules, destructionRulesNoEq)
import Theory.Tools.Wellformedness (checkWellformednessDiff, prettyWfErrorReport)
import TheoryObject

-- Exercise the real mirror enumerator, including Maude AC unification and
-- graph-wide consistency. Two connected consumers make four independent
-- assignments, distinguishable by their action arguments.
tests :: FilePath -> IO Test
tests maudePath = TestList <$> sequence
    [ mirrorTests maudePath
    , explicitVariantMirrorTests maudePath
    , roundTripTests maudePath
    , diffFamilyLifecycleTests maudePath
    , emptyDiffFamilyTests maudePath
    , autoSourceFamilyTests maudePath
    , pure diffVariableAlignmentTests
    , assumptionTests maudePath
    , conditionalRestrictionTests maudePath
    , alternativeConditionalRestrictionTests maudePath
    , jointConditionalRestrictionTests maudePath
    , specializedMirrorTests maudePath
    , mixedRestrictionFilterTests maudePath
    , diffRestrictionLocalityTests maudePath
    , diffRestrictionPreservationTests maudePath
    , partialEvaluationDiffTests maudePath
    ]

mirrorTests :: FilePath -> IO Test
mirrorTests maudePath = do
    let parsed = parseOpenDiffTheoryString [] $ unlines
          [ "theory MirrorUnifiers begin"
          , "builtins: multiset"
          , "rule Produce: [] --> [ F('a' ++ 'b') ]"
          , "rule Consume: [ F(x ++ y) ] --[ Choice(x,y) ]-> [ G('c' ++ 'd') ]"
          , "rule Finish: [ G(z ++ w) ] --[ Final(z,w) ]-> []"
          , "diffLemma Observational_equivalence:"
          , "end"
          ]
    open <- either (fail . show) pure parsed
    thy <- closeDiffTheory maudePath open False
    let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
        instances = map (fst . (`someRuleACInstAvoiding` ([] :: [LVar]))
                             . fmap ProtoInfo . L.get cprRuleAC) (leftTheoryRules thy)
        node i = LVar "n" LSortNode (fromIntegral (i :: Int))
        ground ru = apply (substFromList
            [(v, pubTerm value) | v <- frees ru,
              Just value <- [lookup (lvarName v) [("x","a"),("y","b"),("z","c"),("w","d")]]]) ru
        system count = L.set sNodes (M.fromList (zip (map node [0..]) (map ground (take count instances))))
                     $ L.set sEdges (S.fromList [Edge (node i, ConcIdx 0) (node (i+1), PremIdx 0) | i <- [0..count-2]])
                     $ emptySystem RawSource True
        choices sys = [factTerms fa | ru <- M.elems (L.get sNodes sys), fa <- L.get rActs ru,
                                     factTag fa `elem` [ProtoFact Linear "Choice" 2, ProtoFact Linear "Final" 2]]
        check count expected side = TestCase $ do
            let mirrors = getMirrorDG ctxt side (system count)
            assertEqual "one mirror per global unifier" (length expected) (length mirrors)
            assertEqual "all asymmetric action assignments survive"
                (S.fromList (map (map (map pubTerm)) expected)) (S.fromList (map choices mirrors))
            assertBool "each mirror satisfies every edge" (all isCorrectDG mirrors)
    pure $ TestLabel "Mirror alternative unifiers" $ TestList
        [check 2 [[["a","b"]],[["b","a"]]] side | side <- [LHS,RHS]]
        `appendTests` TestList
        [check 3 [[a,b] | a <- [["a","b"],["b","a"]], b <- [["c","d"],["d","c"]]] side | side <- [LHS,RHS]]
  where
    appendTests a b = TestList [a,b]

explicitVariantMirrorTests :: FilePath -> IO Test
explicitVariantMirrorTests maudePath = do
    cases <- sequence [makeCase swapped auto | swapped <- [False, True], auto <- [False, True]]
    pure $ TestLabel "Explicit variant mirror families" $ TestList cases
  where
    makeCase swapped auto = do
      let decryption side =
            [ side ++ " rule Dec: [In(x), In(k)] --> [Out(sdec(x,k))]"
            , "variants rule (modulo AC) Dec___VARIANT_1: [In(x.2), In(k.1)] --[Generic(x.2)]-> [Out(sdec(x.2,k.1))],"
            , "rule (modulo AC) Dec___VARIANT_2: [In(senc(z.2,k.1)), In(k.1)] --[Cancelled(z.2)]-> [Out(z.2)]"
            ]
          identity side =
            [ side ++ " rule Dec: [In(x), In(k)] --> [Out(x)]"
            , "variants rule (modulo AC) Dec: [In(x), In(k)] --[Echoed(x)]-> [Out(x)]"
            ]
          (left, right) = if swapped then (identity, decryption) else (decryption, identity)
          output = if swapped then "diff(x,sdec(x,k))" else "diff(sdec(x,k),x)"
      open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines $
        [ "theory ExplicitMirrors begin", "builtins: symmetric-encryption"
        , "rule Dec: [In(x), In(k)] --> [Out(" ++ output ++ ")]"
        ] ++ left "left" ++ right "right" ++
        [ "rule Decoy: [In(x)] --[Unrelated(x)]-> [Out(x)]", "diffLemma D:", "end" ]
      thy <- closeDiffTheory maudePath open auto
      let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
          family side = filter ((== "Dec") . getRuleName) $
            L.get (crProtocol C.. pcRules) (eitherProofContext ctxt side)
          node = LVar "n" LSortNode 0
          mirrored side ru =
            let inst = fst $ someRuleACInstAvoiding ru ([] :: [LVar])
                sys = L.set sNodes (M.singleton node inst) $ emptySystem RawSource True
            in map ((M.! node) . L.get sNodes) (getMirrorDG ctxt side sys)
          actions = sort . map factTag . L.get rActs
          decryptionSide = if swapped then RHS else LHS
      pure $ TestCase $ do
        assertEqual "left family size" (if swapped then 1 else 2) (length (family LHS))
        assertEqual "right family size" (if swapped then 2 else 1) (length (family RHS))
        assertEqual "exported variant names remain distinct"
          ["Dec___VARIANT_1", "Dec___VARIANT_2"]
          (sort [getRuleName (L.get cprRuleAC r) | r <- diffTheorySideRules decryptionSide thy,
                 getRuleName (L.get cprRuleE r) == "Dec"])
        mapM_ (\side -> mapM_ (\ru ->
          assertEqual "every opposite variant, with its own actions"
            (sort (map actions (family (opposite side))))
            (sort (map actions (mirrored side ru)))) (family side)) [LHS, RHS]

roundTripTests :: FilePath -> IO Test
roundTripTests maudePath = do
    let models =
          [ ["rule Emit: [] --[ A(diff('a','b')) ]-> [Out('hello')]"]
          , [ "builtins: symmetric-encryption"
            , "macros: m(x) = x"
            , "rule Dec: [ Fr(~n), In(x), In(k) ] --[ A(m(~n)) ]-> [ Out(sdec(x,k)), Out(diff(m(~n),k)) ]"
            , "lemma source [left,sources]: \"All n #i. A(n)@i ==> T\""
            , "restriction right_only [right]: \"All n #i. A(n)@i ==> T\""
            ]
          , [ "rule Emit: [] --[ A(diff('a','b')) ]-> []"
            , "left rule Emit: [] --[ A('a') ]-> []"
            , "right rule Emit: [] --[ A('b') ]-> []"
            ]
          , [ "builtins: symmetric-encryption"
            , "rule Dec: [ In(x), In(k) ] --> [ Out(sdec(x,k)) ]"
            , "left rule Dec: [ In(x), In(k) ] --> [ Out(sdec(x,k)) ]"
            , "variants rule (modulo AC) Dec1: [ In(x), In(k) ] --> [ Out(sdec(x,k)) ],"
            , "rule (modulo AC) Dec2: [ In(senc(z,k)), In(k) ] --> [ Out(z) ]"
            , "right rule Dec: [ In(x), In(k) ] --> [ Out(sdec(x,k)) ]"
            , "variants rule (modulo AC) Dec1: [ In(x), In(k) ] --> [ Out(sdec(x,k)) ],"
            , "rule (modulo AC) Dec2: [ In(senc(z,k)), In(k) ] --> [ Out(z) ]"
            ]
          , [ "builtins: multiset"
            , "rule Produce: [] --> [ F('a' ++ 'b') ]"
            , "rule Consume: [ F(x ++ y) ] --[ A(x,y,$p) ]-> []"
            ]
          ]
    cases <- sequence [makeCase model auto | model <- models, auto <- [False,True]]
    pure $ TestLabel "Diff theory close/open/close" $ TestList cases
  where
    makeCase model auto = do
        open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $
            unlines (["theory RoundTrip begin"] ++ model ++ ["diffLemma D:","end"])
        first <- closeDiffTheory maudePath open auto
        let reclose t = closeDiffTheoryWithMaude (L.get diffThySignature t) (openDiffTheory t) auto
            second = reclose first
            third = reclose second
            rules t = (sort (leftTheoryRules t), sort (rightTheoryRules t))
            caches t = [L.get label t | label <- [diffThyCacheLeft,diffThyCacheRight,diffThyDiffCacheLeft,diffThyDiffCacheRight]]
            nonRules t = [item | item <- L.get diffThyItems (openDiffTheory t),
                                case item of
                                  EitherRuleItem _ -> False
                                  DiffRuleItem _ -> False
                                  _ -> True]
        pure $ TestCase $ mapM_ (\t -> do
            assertEqual "side rules, variants and new variables" (rules first) (rules t)
            assertEqual "lemmas, restrictions and proof skeletons" (nonRules first) (nonRules t)
            assertEqual "all four rule/source caches" (caches first) (caches t)) [second,third]

diffFamilyLifecycleTests :: FilePath -> IO Test
diffFamilyLifecycleTests maudePath = do
    -- Each shape crosses all three boundaries once. Explicit members exercise
    -- annotations and alignment; one-sided declarations and a real cycle have
    -- their own cases. Actual auto-source generation is tested separately.
    cases <- sequence
      [ makeCase shape cyclic leftExplicit rightExplicit False
      | (shape, cyclic, leftExplicit, rightExplicit) <-
          [(shape, False, explicit, explicit)
          | shape <- ["trivial", "normalized", "multiple", "asymmetric-public",
                      "asymmetric-multiple", "asymmetric-indexed", "asymmetric-local"]
          , explicit <- [False, True]] ++
          [("multiple", True, True, True),
           ("asymmetric-multiple", False, True, False),
           ("asymmetric-multiple", False, False, True)] ++
          [(shape, False, False, False) | shape <- ["empty", "left-empty", "right-empty"]] ]
    pure $ TestLabel "Diff family lifecycle" $ TestList cases
  where
    makeCase :: String -> Bool -> Bool -> Bool -> Bool -> IO Test
    makeCase shape cyclic leftExplicit rightExplicit auto = do
      let inputs = case shape of
            "multiple" -> ["In(x)", "In(k)"]
            "asymmetric-multiple" -> ["In(x)", "In(k)"]
            "asymmetric-indexed" -> ["In(x)", "In(k)"]
            "asymmetric-local" -> ["In(x)", "In(k)"]
            "empty" -> ["Fr(~n)", "In(~n)"]
            "left-empty" -> ["Fr(~n)", "In(diff(~n,'known'))"]
            "right-empty" -> ["Fr(~n)", "In(diff('known',~n))"]
            _ -> []
          state = ["State('s')" | cyclic]
          output = case shape of
            "trivial" -> "'a'"
            "normalized" -> "sdec(senc('a','k'),'k')"
            "multiple" -> "sdec(x,k)"
            "asymmetric-public" -> "diff($x,<$x,$y>)"
            "asymmetric-multiple" -> "<sdec(x,k),diff($p,$q)>"
            "asymmetric-indexed" -> "<sdec(x,k),diff(<$p,$p.1,$p.2>,$q)>"
            "asymmetric-local" -> "<sdec(x,k),diff(<$p,$p.1,$p.2>,$q)>"
            _ -> "'a'"
          commaList = foldr1 (\a b -> a ++ "," ++ b)
          list xs = "[" ++ (if null xs then "" else commaList xs) ++ "]"
          source = unlines
            [ "theory FamilyLifecycle begin", "builtins: symmetric-encryption"
            , "rule Init: [] --> [State('s')]"
            , "rule R[color=#123456]: " ++ list (inputs ++ state)
                ++ " --[Seen($p)]-> " ++ list (["Out(" ++ output ++ ")"] ++ state)
            , "diffLemma D:", "end" ]
      parsed <- either (fail . show) pure (parseOpenDiffTheoryString [] source)
      computed <- closeDiffTheory maudePath parsed False
      let sig = L.get diffThySignature computed
          hnd = L.get sigmMaudeHandle sig
          side explicit ruE = OpenProtoRule ruE $
            if explicit then map (\ru -> addAction (addAction
                        (addAction (L.set (pracAttributes C.. rInfo) mempty ru) (protoFact Linear "Extra" []))
                        (protoFact Linear "DiffProtoR___VARIANT_1" [])) (protoFact Linear "DiffProtoR" []))
                                   (map (L.get cprRuleAC) $ concatMap unfoldRuleVariants $
                                      closeProtoRule hnd [] (OpenProtoRule (local ruE) []))
                        else []
          local ruE | shape == "asymmetric-local" = L.set rNewVars
                        (newVariables (L.get rPrems ruE) (L.get rConcs ruE ++ L.get rActs ruE)) ruE
                    | otherwise = ruE
          declare (DiffRuleItem (DiffProtoRule ruE _))
            | getRuleName ruE == "R", leftExplicit || rightExplicit =
            DiffRuleItem (DiffProtoRule ruE
              (Just (side leftExplicit (getLeftRule ruE), side rightExplicit (getRightRule ruE))))
          declare item = item
          input = L.modify diffThyItems (map declare) parsed
          first = closeDiffTheoryWithMaude sig input auto
          rules t = (sort (leftTheoryRules t), sort (rightTheoryRules t))
          caches t = [L.get label t | label <-
            [diffThyCacheLeft,diffThyCacheRight,diffThyDiffCacheLeft,diffThyDiffCacheRight]]
          check t = do
            assertEqual "complete families, metadata and new-variable vectors" (rules first) (rules t)
            assertEqual "all four rule/source caches" (caches first) (caches t)
          reclose t = closeDiffTheoryWithMaude sig (openDiffTheory t) auto
          reload printer t = do
            open <- either (assertFailure . show) pure $
              parseOpenDiffTheoryString [] (render (printer t))
            let warnings = checkWellformednessDiff open sig
            assertBool (render (prettyWfErrorReport warnings)) (null warnings)
            pure $ closeDiffTheoryWithMaude sig open auto
      pure $ TestLabel (show (shape, cyclic, leftExplicit, rightExplicit, auto)) $ TestCase $ do
        let warnings = checkWellformednessDiff input sig
        assertBool (render (prettyWfErrorReport warnings)) (null warnings)
        mapM_ (\s -> assertEqual "empty family only on the expected sides"
          (shape == "empty" || (shape == "left-empty" && s == LHS)
                            || (shape == "right-empty" && s == RHS))
          (null [r | r <- diffTheorySideRules s first,
                     getRuleName (L.get cprRuleE r) == "R"])) [LHS, RHS]
        assertBool "canonical opening has no duplicate side items" $
          null [() | EitherRuleItem _ <- L.get diffThyItems (openDiffTheory first)]
        check (reclose first)
        let repeated = cyclic || shape `elem` ["asymmetric-indexed", "asymmetric-local"]
        if repeated then check (reclose (reclose first)) else pure ()
        printed <- reload prettyClosedDiffTheory first
        check printed
        if repeated then reload prettyClosedDiffTheory printed >>= check else pure ()
        saved <- reload (prettyOpenDiffTheory . exportDiffTheory) first
        check saved
        if repeated then reload (prettyOpenDiffTheory . exportDiffTheory) saved >>= check else pure ()

emptyDiffFamilyTests :: FilePath -> IO Test
emptyDiffFamilyTests maudePath = TestList <$> mapM makeCase
    [("diff(~n,'known')", [RHS]), ("diff('known',~n)", [LHS]), ("~n", [])]
  where
    makeCase (input, liveSides) = do
      open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines
        [ "theory EmptyFamily begin"
        , "rule Emit: [Fr(~n), In(" ++ input ++ ")] --> [Out(~n)]"
        , "diffLemma D:", "end" ]
      thy <- closeDiffTheory maudePath open False
      let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
          cases = fromJust (execDiffProofMethod ctxt DiffRuleEquivalence emptyDiffSystem)
          node = LVar "n" LSortNode 0
      pure $ TestLabel ("Empty diff family: " ++ input) $ TestCase $ do
        assertEqual "case enumeration includes either live parent"
          (not (null liveSides)) (M.member "Rule_Emit" cases)
        mapM_ (\side -> mapM_ (\ru -> do
          let inst = fst $ someRuleACInstAvoiding (fmap ProtoInfo (L.get cprRuleAC ru)) ([] :: [LVar])
              sys = L.set sNodes (M.singleton node inst) $ emptySystem RawSource True
          assertEqual "no mirror graph" [] (getMirrorDG ctxt side sys))
          (diffTheorySideRules side thy)) liveSides

autoSourceFamilyTests :: FilePath -> IO Test
autoSourceFamilyTests maudePath = do
    input <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines
      [ "theory AutoSourceFamilies begin", "builtins: asymmetric-encryption"
      , "rule Keys: [Fr(~k)] --> [!Key($A,~k), !Pub($A,pk(~k)), Out(pk(~k))]"
      , "rule Send: [Fr(~n), !Pub($B,p)] --> [Out(aenc(<~n,'tag'>,p)), Out(diff($x,<$x,$y>))]"
      , "rule Forward: [!Key($A,k), !Pub($B,p), In(aenc(<x,'tag'>,pk(k)))] --[Seen(x)]-> [Out(aenc(x,p))]"
      , "diffLemma D:", "end" ]
    sig <- toSignatureWithMaude maudePath (L.get diffThySignature input)
    let hnd = L.get sigmMaudeHandle sig
        msig = _sigMaudeInfo (L.get diffThySignature input)
        deduction diff = subtermConstructorRules diff hnd msig ++ specialIntruderRules diff
                      ++ runReader (destructionRulesNoEq diff (noEqFunSyms msig)) hnd
        withDeduction = addIntrRuleLabels . addIntrRuleACsDiffBoth (deduction False)
                                         . addIntrRuleACsDiffBothDiff (deduction True)
        first = closeDiffTheoryWithMaude sig (withDeduction input) True
        rules t = (sort (leftTheoryRules t), sort (rightTheoryRules t))
        sources t = [(s, L.get lName l, L.get lFormula l)
                    | (s, l) <- diffTheoryLemmas t, isSourceLemma l]
        check t = do
          assertEqual "generated actions and all rule metadata" (rules first) (rules t)
          assertEqual "generated source lemmas" (sources first) (sources t)
        reload t = do
          parsed <- either (assertFailure . show) pure $ parseOpenDiffTheoryString [] $
            render (prettyClosedDiffTheory t)
          let warnings = checkWellformednessDiff parsed sig
          assertBool (render (prettyWfErrorReport warnings)) (null warnings)
          pure $ closeDiffTheoryWithMaude sig (withDeduction parsed) True
    pure $ TestLabel "Generated source family round trip" $ TestCase $ do
      assertBool "real generated source actions" ("AUTO_IN_" `isInfixOf` show (rules first))
      assertEqual "one source lemma on each side" 2 (length (sources first))
      check (closeDiffTheoryWithMaude sig (openDiffTheory first) True)
      second <- reload first
      check second
      reload second >>= check

diffVariableAlignmentTests :: Test
diffVariableAlignmentTests = TestLabel "Diff variable alignment" $ TestList
    [ TestCase $ case diffVariantNewVars annotated canonical of
        Just [visible,hidden] -> do
          assertEqual "visible slot follows its original action" (p 4) visible
          assertBool "hidden slot cannot capture any supplied variable" (hidden `notElem` map varTerm (frees annotated))
          assertBool "hidden and visible slots stay distinct" (hidden /= visible)
          assertEqual "reopening preserves transported hidden slots"
            (Just [visible,hidden])
            (diffVariantNewVars (L.set rNewVars [visible,hidden] annotated) canonical)
        result -> assertFailure ("expected two aligned slots, got " ++ show result)
    , TestCase $ assertEqual "exact names retain intentional hidden-variable annotations"
        (Just [p 1,p 2]) (diffVariantNewVars exactAnnotation canonical)
    , TestCase $ assertEqual "duplicate original labels retain their order"
        (Just [p 4]) (diffVariantNewVars duplicates ordered)
    , TestCase $ assertEqual "reordering original labels is not an added action"
        Nothing (diffVariantNewVars reversed ordered)
    , TestCase $ assertEqual "ambiguous action-only slot is rejected"
        Nothing (diffVariantNewVars ambiguous canonical)
    , TestCase $ assertEqual "distinct variables cannot be merged"
        Nothing (diffVariantNewVars merged canonical)
    , TestCase $ assertEqual "different constants cannot be renamed"
        Nothing (matchTerms [fAppPair (p 3, pubTerm "b")] [fAppPair (p 0, pubTerm "a")])
    , TestCase $ assertEqual "repeated variables retain equality"
        Nothing (matchTerms [p 3,p 4] [p 0,p 0])
    , TestCase $ assertEqual "variable sorts cannot change"
        Nothing (matchTerms [varTerm (LVar "x" LSortMsg 3)] [p 0])
    , TestCase $ assertEqual "AC arguments allow syntactic renaming"
        (Just []) (matchTerms [fAppUnion (p 3,p 4)] [fAppUnion (p 0,p 1)])
    , TestCase $ assertEqual "AC reordering cannot evade a fixed correspondence"
        Nothing (matchTerms [p 4,p 3,fAppUnion (p 3,p 4)] [p 0,p 1,fAppUnion (p 0,p 1)])
    , TestCase $ assertEqual "premises cannot become conclusions"
        Nothing (diffVariantNewVars moved direction)
    ]
  where
    p i = varTerm (LVar "p" LSortPub i)
    fact name ts = protoFact Linear name ts
    rule ps cs acts nvs = Rule (ProtoRuleACInfo (StandRule "R") mempty (Disj [emptySubstVFresh]) []) ps cs acts nvs
    matchTerms actual expected = diffVariantNewVars
      (rule [fact "F" actual] [] [] []) (rule [fact "F" expected] [] [] [])
    canonical = rule [fact "F" [p 0]] [] [fact "A" [p 1]] [p 1,p 2]
    annotated = rule [fact "F" [p 3]] [] [fact "Extra" [p 2],fact "A" [p 4]] []
    exactAnnotation = rule [fact "F" [p 0]] [] [fact "Extra" [p 2],fact "A" [p 1]] [p 1,p 2]
    ambiguous = rule [fact "F" [p 3]] [] [fact "A" [p 4],fact "A" [p 5]] []
    merged = rule [fact "F" [p 3]] [] [fact "A" [p 3]] []
    ordered = rule [fact "F" [p 0,p 1]] [] [fact "A" [p 0],fact "A" [p 1]] [p 1]
    duplicates = rule [fact "F" [p 3,p 4]] []
      [fact "Extra" [],fact "A" [p 3],fact "A" [p 3],fact "A" [p 4]] []
    reversed = rule [fact "F" [p 3,p 4]] [] [fact "A" [p 4],fact "A" [p 3]] []
    direction = rule [fact "F" [p 0]] [] [] []
    moved = rule [] [fact "F" [p 3]] [] []

assumptionTests :: FilePath -> IO Test
assumptionTests maudePath = do
    open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines
      [ "theory AssumptionScope begin"
      , "rule Emit: [] --[ A() ]-> []"
      , "lemma assumed [left,reuse,diff_reuse]: \"All #i. A()@i ==> F\""
      , "lemma assumed [right,reuse,diff_reuse]: \"All #i. A()@i ==> T\""
      , "lemma hidden [left,hide_lemma=assumed]: \"All #i. A()@i ==> F\""
      , "lemma all_hidden [left,hide_lemma=ALL]: \"All #i. A()@i ==> F\""
      , "lemma visible [left]: \"All #i. A()@i ==> F\""
      , "diffLemma Hidden [hide_lemma=assumed]:"
      , "diffLemma AllHidden [hide_lemma=ALL]:"
      , "diffLemma Visible:"
      , "end"
      ]
    thy <- closeDiffTheory maudePath open False
    let previous = [item | item@(EitherLemmaItem (_,lem)) <- L.get diffThyItems thy,
                           L.get lName lem == "assumed"]
        assumptions name items =
          let lem = fromJust (lookupLemmaDiff LHS name thy)
              ctxt = getProofContextDiff LHS lem thy
          in L.get sLemmas $ mkSystemDiff LHS ctxt [] items (L.get lFormula lem)
        diffAssumptions name = L.get dpcReuseLemmas $
          getDiffProofContext (fromJust (lookupDiffLemma name thy)) thy
        leftFormula = formulaToGuarded_ $ L.get lFormula $ fromJust (lookupLemmaDiff LHS "assumed" thy)
    pure $ TestLabel "Reusable assumption scope" $ TestList
      [ TestCase $ assertEqual "named hidden side lemma" S.empty (assumptions "hidden" previous)
      , TestCase $ assertEqual "all hidden side lemmas" S.empty (assumptions "all_hidden" previous)
      , TestCase $ assertEqual "visible reuse is side-specific" (S.singleton leftFormula) (assumptions "visible" previous)
      , TestCase $ assertEqual "later lemmas are not supplied to ordinary reuse" S.empty (assumptions "visible" [])
      , TestCase $ assertEqual "named hidden diff lemma" [] (diffAssumptions "Hidden")
      , TestCase $ assertEqual "all hidden diff lemmas" [] (diffAssumptions "AllHidden")
      , TestCase $ assertEqual "visible diff reuse retains both sides" [LHS,RHS] (map fst (diffAssumptions "Visible"))
      ]

conditionalRestrictionTests :: FilePath -> IO Test
conditionalRestrictionTests maudePath = do
    let cases =
          [ ("constant guard, symbolic action", "All #i. A('a')@i ==> F", [Nothing], True, TTrue)
          , ("constant guard, permitted action", "All #i. A('a')@i ==> F", [Just "b"], True, TTrue)
          , ("constant guard, forbidden mirror action", "All #i. A('a')@i ==> F", [Just "a"], False, TFalse)
          , ("unconditional mirror violation", "All x #i. A(x)@i ==> F", [Nothing], False, TFalse)
          , ("original also forbids the ground action", "All #i. A('a')@i ==> F", [Just "a"], True, TTrue)
          , ("original also forbids the symbolic action", "All x #i. A(x)@i ==> F", [Nothing], True, TTrue)
          , ("nested conditional violation", "All x #i. A(x)@i ==> (All #j. A('a')@j ==> F)", [Nothing], True, TTrue)
          ]
    tests' <- sequence [makeCase label formula values shared expected solved
                      | (label,formula,values,shared,expected) <- cases, solved <- [False,True]]
    pure $ TestLabel "Conditional restriction instances" $ TestList tests'
  where
    makeCase label formula values shared expected solved = do
        open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines
          [ "theory ConditionalRestrictions begin"
          , "rule R: [] --[ A($x) ]-> []"
          , "restriction Check" ++ (if shared then "" else " [right]") ++ ": \"" ++ formula ++ "\""
          , "diffLemma D:", "end"
          ]
        thy <- closeDiffTheory maudePath open False
        let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
            rule = fst $ someRuleACInstAvoiding (fmap ProtoInfo (L.get cprRuleAC (head (leftTheoryRules thy)))) ([] :: [LVar])
            atNode i value = (LVar "n" LSortNode i,
                apply (substFromList [(v, maybe (varTerm (LVar "x" LSortPub (100+i))) pubTerm value) | v <- frees rule]) rule)
            sys = L.set sNodes (M.fromList (zipWith atNode [0..] values)) $ emptySystem RawSource True
            original = L.set dsSide (Just LHS) $ L.set dsSystem (Just sys) emptyDiffSystem
            mirrors = getMirrorDG ctxt LHS sys
        pure $ TestCase $ assertEqual (label ++ "; solved=" ++ show solved) expected
          (fst (evaluateRestrictions ctxt original mirrors solved))

alternativeConditionalRestrictionTests :: FilePath -> IO Test
alternativeConditionalRestrictionTests maudePath = do
    let avoidChosen = "All x y p #i. Choice(x,y,p)@i ==> not(x=p)"
        cases =
          [ ("incompatible failures", "b", avoidChosen, Nothing, Nothing, TTrue)
          , ("shared conditional failure", "b", "All x y p #i. Choice(x,y,p)@i ==> not(p='a')", Nothing, Nothing, TFalse)
          , ("conditional and unconditional failures", "b", "All x y p #i. Choice(x,y,p)@i ==> not(x='b') & not(x=p)", Nothing, Nothing, TFalse)
          , ("all alternatives unconditionally fail", "b", "All x y p #i. Choice(x,y,p)@i ==> F", Nothing, Nothing, TFalse)
          , ("one alternative always succeeds", "b", "All x y p #i. Choice(x,y,p)@i ==> x='b'", Nothing, Nothing, TTrue)
          , ("success alongside conditional failure", "b", "All x y p #i. Choice(x,y,p)@i ==> x='b' | not(x=p)", Nothing, Nothing, TTrue)
          , ("first ground assignment", "b", avoidChosen, Nothing, Just "a", TTrue)
          , ("second ground assignment", "b", avoidChosen, Nothing, Just "b", TTrue)
          , ("both alternatives succeed", "b", avoidChosen, Nothing, Just "c", TTrue)
          , ("both fail at the same ground assignment", "b", "All x y p #i. Choice(x,y,p)@i ==> not(p='a')", Nothing, Just "a", TFalse)
          , ("original excludes both failures", "b", avoidChosen,
              Just "All x y p #i. Choice(x,y,p)@i ==> not(p='a') & not(p='b')", Nothing, TTrue)
          , ("single alternative conditional failure", "a", avoidChosen, Nothing, Nothing, TFalse)
          ]
    tests' <- sequence [makeCase side testCase | side <- [LHS,RHS], testCase <- cases]
    pure $ TestLabel "Conditional failures across mirror alternatives" $ TestList tests'
  where
    makeCase side (label, second, formula, originalFormula, publicValue, expected) = do
        let sideName LHS = "left"
            sideName RHS = "right"
        open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines $
          [ "theory AlternativeConditionalRestrictions begin"
          , "builtins: multiset"
          , "rule Produce: [] --> [F('a' ++ '" ++ second ++ "')]"
          , "rule Consume: [F(x ++ y)] --[Choice(x,y,$p)]-> [Out($p)]"
          , "restriction Mirror [" ++ sideName (opposite side) ++ "]: \"" ++ formula ++ "\""
          ] ++
          [ "restriction Original [" ++ sideName side ++ "]: \"" ++ f ++ "\""
          | Just f <- [originalFormula] ] ++ ["diffLemma D:", "end"]
        thy <- closeDiffTheory maudePath open False
        let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
            node i = LVar "n" LSortNode i
            ground ru = apply (substFromList
              [(v, pubTerm value) | v <- frees ru,
                Just value <- [lookup (lvarName v)
                  ([("x","a"),("y",second)] ++ [("p",p) | Just p <- [publicValue]])]]) ru
            rules = map (ground . fst . (`someRuleACInstAvoiding` ([] :: [LVar]))
                         . fmap ProtoInfo . L.get cprRuleAC) (diffTheorySideRules side thy)
            sys = L.set sNodes (M.fromList (zip (map node [0..]) rules))
                $ L.set sEdges (S.singleton (Edge (node 0, ConcIdx 0) (node 1, PremIdx 0)))
                $ emptySystem RawSource True
            original = L.set dsSide (Just side) $ L.set dsSystem (Just sys) emptyDiffSystem
            mirrors = getMirrorDG ctxt side sys
        pure $ TestCase $ do
            assertEqual "all mirror alternatives enumerated" (if second == "a" then 1 else 2) (length mirrors)
            assertBool "mirror edges are consistent" (all isCorrectDG mirrors)
            mapM_ (\alternatives -> assertEqual (label ++ "; side=" ++ show side) expected
              (fst (evaluateRestrictions ctxt original alternatives True))) [mirrors, reverse mirrors]

jointConditionalRestrictionTests :: FilePath -> IO Test
jointConditionalRestrictionTests maudePath = do
    let distinctConditions = "(x='a' | not(q='b')) & (x='b' | not(p='a'))"
        cases =
          [ ("conditions constrain different variables", distinctConditions, Nothing, TFalse)
          , ("original forbids only the joint assignment", distinctConditions, Just "not(p='a' & q='b')", TTrue)
          , ("original equates the two variables", distinctConditions, Just "p=q", TTrue)
          , ("original admits the joint assignment", distinctConditions, Just "q='b'", TFalse)
          , ("later failure case overlaps", "not(p=x) & not(p='c')", Nothing, TFalse)
          , ("original excludes the only overlap", "not(p=x) & not(p='c')", Just "not(p='c')", TTrue)
          , ("unresolved existential condition", "Ex #j. Choice(x,y,p,q)@j & i<j", Nothing, TUnknown)
          , ("definite failure alongside unresolved condition", "not(p='a') & (Ex #j. Choice(x,y,p,q)@j & i<j)", Nothing, TFalse)
          ]
    tests' <- sequence [makeCase side testCase | side <- [LHS,RHS], testCase <- cases]
    pure $ TestLabel "Joint conditional mirror failures" $ TestList tests'
  where
    makeCase side (label, consequence, originalConsequence, expected) = do
        let sideName LHS = "left"
            sideName RHS = "right"
            restriction name s f = "restriction " ++ name ++ " [" ++ sideName s ++
              "]: \"All x y p q #i. Choice(x,y,p,q)@i ==> " ++ f ++ "\""
        open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines $
          [ "theory JointConditions begin"
          , "builtins: multiset"
          , "rule Produce: [] --> [F('a' ++ 'b')]"
          , "rule Consume: [F(x ++ y)] --[Choice(x,y,$p,$q)]-> [Out(<$p,$q>)]"
          , restriction "Mirror" (opposite side) consequence
          ] ++ [restriction "Original" side f | Just f <- [originalConsequence]] ++
          ["diffLemma D:", "end"]
        thy <- closeDiffTheory maudePath open False
        let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
            node i = LVar "n" LSortNode i
            ground ru = apply (substFromList
              [(v, pubTerm value) | v <- frees ru,
                Just value <- [lookup (lvarName v) [("x","a"),("y","b")]]]) ru
            rules = map (ground . fst . (`someRuleACInstAvoiding` ([] :: [LVar]))
                         . fmap ProtoInfo . L.get cprRuleAC) (diffTheorySideRules side thy)
            sys = L.set sNodes (M.fromList (zip (map node [0..]) rules))
                $ L.set sEdges (S.singleton (Edge (node 0, ConcIdx 0) (node 1, PremIdx 0)))
                $ emptySystem RawSource True
            original = L.set dsSide (Just side) $ L.set dsSystem (Just sys) emptyDiffSystem
            mirrors = getMirrorDG ctxt side sys
        pure $ TestCase $ do
            assertEqual "two mirror alternatives" 2 (length mirrors)
            mapM_ (\alternatives -> do
              let (actual, witnesses) = evaluateRestrictions ctxt original alternatives True
              assertEqual (label ++ "; side=" ++ show side) expected actual
              if actual == TFalse then do
                assertEqual "one jointly specialized witness per mirror" 2 (length witnesses)
                let outputs m = [factTerms fa | ru <- M.elems (L.get sNodes m), fa <- L.get rConcs ru, factTag fa == OutFact]
                assertEqual "witnesses share the original public assignment"
                  (outputs (head witnesses)) (outputs (last witnesses))
              else pure ()) [mirrors, reverse mirrors]

specializedMirrorTests :: FilePath -> IO Test
specializedMirrorTests maudePath = do
    -- A ground variant becomes available only after p='a'. Its added actions
    -- differ from the generic variant, as imported refinements can do.
    open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines
      [ "theory SpecializedMirrors begin"
      , "rule R: [] --[A($p)]-> []"
      , "restriction Check [right]: \"All p #i. Bad(p)@i ==> not(p='a')\""
      , "diffLemma D:", "end"
      ]
    thy <- closeDiffTheory maudePath open False
    let originalRule = fst $ someRuleACInstAvoiding
          (fmap ProtoInfo (L.get cprRuleAC (head (leftTheoryRules thy)))) ([] :: [LVar])
        sys = L.set sNodes (M.singleton (LVar "n" LSortNode 0) originalRule)
              $ emptySystem RawSource True
        original = L.set dsSide (Just LHS) $ L.set dsSystem (Just sys) emptyDiffSystem
        base :: RuleAC
        base = fmap ProtoInfo $ L.get cprRuleAC $ head $ rightTheoryRules thy
        ground = substFromList [(v,pubTerm "a") | v <- frees (L.get rNewVars base)]
        variants = [addAction base (protoFact Linear "Bad" (L.get rNewVars base)),
                    L.modify rActs (apply ground) $ L.modify rNewVars (apply ground) base]
        ctxt = L.set (crProtocol C.. pcRules C.. dpcPCRight) variants
               $ getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
        mirrors = getMirrorDG ctxt LHS sys
        specialized = apply (substFromList
          [(v,pubTerm "a") | v <- frees sys, lvarSort v == LSortPub]) sys
        newMirrorCase = TestCase $ do
          assertEqual "one initially applicable variant" 1 (length mirrors)
          assertEqual "specialization enables a second variant" 2 (length (getMirrorDG ctxt LHS specialized))
          assertEqual "newly enabled mirror prevents an attack" TTrue
            (fst (evaluateRestrictions ctxt original mirrors True))
    locals <- mapM localCase [(side, testCase) | side <- [LHS, RHS], testCase <- localConditions]
    pure $ TestLabel "Specialized and mirror-local variables" $ TestList (newMirrorCase:locals)
  where
    -- Bounded nested guards exercise composed local images and original
    -- assignments at multiple depths, on both sides of the diff context.
    localConditions =
      [ ("local grounding", "not(x='a')", TUnknown)
      , ("original grounding", "not(p='a')", TFalse)
      , ("nested local grounding", "All y q #j. A(y,q)@j ==> not(y='a')", TUnknown)
      , ("nested original grounding", "All y q #j. A(y,q)@j ==> not(q='a')", TFalse)
      , ("nested local aliases original", "All y q #j. A(y,q)@j ==> not(y=q)", TUnknown)
      , ("nested guard retains local image", "All #j. A('a',p)@j ==> F", TUnknown)
      ] ++ [("nested depth " ++ show depth ++ ": " ++ label,
              foldr (\_ body -> "All y q #j. A(y,q)@j ==> (" ++ body ++ ")")
                condition [1..depth], expected)
             | depth <- [2..4 :: Int]
             , (label, condition, expected) <-
                 [("ground local", "not(x='a')", TUnknown),
                  ("ground original", "not(p='a')", TFalse),
                  ("alias local", "not(x=p)", TUnknown)]]
    localCase (side, (label, consequence, expected)) = do
      open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines
        [ "theory LocalMirrorVariables begin"
        , "rule R: [In(x)] --[A(x,$p)]-> [Out($p)]"
        , "restriction Check [" ++ (if side == LHS then "right" else "left") ++ "]: \"All x p #i. A(x,p)@i ==> (" ++ consequence ++ ")\""
        , "diffLemma D:", "end"
        ]
      thy <- closeDiffTheory maudePath open False
      let rule = fst $ someRuleACInstAvoiding
            (fmap ProtoInfo (L.get cprRuleAC (head (diffTheorySideRules side thy)))) ([] :: [LVar])
          sys = L.set sNodes (M.singleton (LVar "n" LSortNode 0) rule) $ emptySystem RawSource True
          ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
          original = L.set dsSide (Just side) $ L.set dsSystem (Just sys) emptyDiffSystem
          mirrors = getMirrorDG ctxt side sys
          alpha :: System -> System
          alpha mirror = apply (substFromList
            [(v, varTerm (v { lvarIdx = lvarIdx v + 1000 }) :: LNTerm)
             | v <- frees mirror, v `notElem` frees sys]) mirror
      pure $ TestCase $ do
        assertEqual "one symbolic mirror" 1 (length mirrors)
        assertBool "mirror has a local variable" $ not $ S.null $
          S.fromList (frees (head mirrors)) `S.difference` S.fromList (frees sys)
        mapM_ (\alternatives -> assertEqual label expected
          (fst (evaluateRestrictions ctxt original alternatives True)))
          [mirrors, map alpha mirrors]

mixedRestrictionFilterTests :: FilePath -> IO Test
mixedRestrictionFilterTests maudePath = do
    open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines
      [ "theory MixedRestrictionFilter begin"
      , "rule R: [] --[ A('b') ]-> []"
      , "restriction Conjunction [right]: \"('a'='b') & (All #i. A('a')@i ==> F)\""
      , "restriction Disjunction [right]: \"(('a'='b') & (All #i. A('a')@i ==> F)) | ('c'='d')\""
      , "diffLemma D:", "end"
      ]
    thy <- closeDiffTheory maudePath open False
    let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
        rightCtxt = eitherProofContext ctxt RHS
        restrictions = concat [forms | (side, forms) <- L.get dpcRestrictions ctxt,
                                       side == RHS]
        ru = fst $ someRuleACInstAvoiding
             (fmap ProtoInfo (L.get cprRuleAC (head (rightTheoryRules thy))))
             ([] :: [LVar])
        sys = L.set sNodes (M.singleton (LVar "n" LSortNode 0) ru)
              $ emptySystem RawSource True
    pure $ TestLabel "Mixed restriction filtering" $ TestCase $
      assertEqual "action-free Boolean cases keep their complete restrictions"
        restrictions (filterRestrictions rightCtxt sys restrictions)

diffRestrictionLocalityTests :: FilePath -> IO Test
diffRestrictionLocalityTests maudePath = do
    open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines
      [ "theory DiffRestrictionLocality begin"
      , "rule R: [] --[ A('a'), B('b') ]-> []"
      , "restriction Local [right]: \"All x #i. A(x)@i ==> x='a'\""
      , "restriction SameNode [right]: \"All #i. A('a')@i & B('b')@i ==> F\""
      , "restriction Conjoined [right]: \"(All #i. A('a')@i ==> F) & (All #j. B('b')@j ==> F)\""
      , "restriction TwoNodes [right]: \"All x #i #j. A(x)@i & A(x)@j ==> #i=#j\""
      , "restriction Causal [right]: \"All x #i. A(x)@i ==> Ex #j. B(x)@j & #j<#i\""
      , "restriction Choice [right]: \"(All #i. A('a')@i ==> F) | (All #j. B('b')@j ==> F)\""
      , "diffLemma D:", "end"
      ]
    thy <- closeDiffTheory maudePath open False
    let restriction name = formulaToGuarded_ $ L.get rstrFormula $ head
          [r | r <- diffTheorySideRestrictions RHS thy, L.get rstrName r == name]
        expected = [("Local",True), ("SameNode",True), ("Conjoined",True),
                    ("TwoNodes",False), ("Causal",False), ("Choice",False)]
        notice = render (prettyDiffRestrictionLimit thy)
    pure $ TestLabel "Diff restriction locality" $ TestList $
      [TestCase $ do
         assertEqual name local (isDiffLocalRestriction (restriction name))
         assertEqual ("notice names only non-local restrictions: " ++ name)
           (not local) (("RHS: " ++ name) `isInfixOf` notice)
      | (name, local) <- expected]

diffRestrictionPreservationTests :: FilePath -> IO Test
diffRestrictionPreservationTests maudePath = do
    cases <- sequence [check name rules restrictions expected | (name, rules, restrictions, expected) <- models]
    pure $ TestLabel "Diff restriction preservation" $ TestList cases
  where
    once event = "All x #i #j. " ++ event ++ "(x)@i & " ++ event ++ "(x)@j ==> #i=#j"
    seed = "rule Seed: [Fr(~k)] --[ Start(~k), Setup() ]-> [ State(~k), !Tag(~k) ]"
    step = "rule Step: [State(k), !Tag(k)] --[ End(k) ]-> [ State(k), Out('ok') ]"
    shared f = ["restriction R: \"" ++ f ++ "\""]
    models =
      [ ("shared marker", [seed, step],
          shared "All #i #j. Setup()@i & Setup()@j ==> #i=#j", True)
      , ("fresh identifier through recursive state", [seed, step], shared (once "End"), True)
      , ("causal existential", [seed, step],
          shared "All k #i. End(k)@i ==> Ex #j. Start(k)@j & #j<#i", True)
      , ("whole disjunction", [seed, step],
          shared "(All #i. Setup()@i ==> F) | (All k #j. End(k)@j ==> F)", True)
      , ("ground arguments", ["rule R: [] --[ A('a') ]-> []"], shared (once "A"), True)
      , ("new public argument", ["rule R: [] --[ A($p) ]-> []"], shared (once "A"), True)
      , ("one-sided marker", [seed, step],
          ["restriction R [right]: \"All #i #j. Setup()@i & Setup()@j ==> #i=#j\""], False)
      , ("identical syntax with attacker input", ["rule R: [In(x)] --[ A(x) ]-> []"], shared (once "A"), False)
      , ("changed ground argument", ["rule R: [] --[ A(diff('a','b')) ]-> []"], shared (once "A"), False)
      , ("changed state propagates", ["rule Seed: [] --> [ F(diff('a','b')) ]",
          "rule Move: [F(x)] --> [G(x)]", "rule R: [G(x)] --[ A(x) ]-> []"], shared (once "A"), False)
      , ("constructor inversion is not assumed", ["functions: f/1", "rule Seed: [Fr(~k)] --> [F(f(~k))]",
          "rule R: [F(f(x))] --[ A(x) ]-> []"], shared (once "A"), False)
      , ("explicit sides omit an action", ["rule R: [] --[ A('a') ]-> []",
          "left rule R: [] --[ A('a') ]-> []", "right rule R: [] --> []"], shared (once "A"), False)
      , ("compiled variants carry different arguments", ["builtins: symmetric-encryption",
          "rule R: [In(x), In(k)] --[ A(sdec(x,k)) ]-> []"], shared (once "A"), False)
      , ("intruder knowledge is not certified", ["rule R: [Fr(~k)] --[ A(~k) ]-> [Out(~k)]"],
          shared "All k #i #j. A(k)@i & KU(k)@j ==> #i<#j", False)
      ] ++
      [ ("empty producer " ++ input ++ " " ++ output ++ " " ++ formula,
          [seed, "rule Observe: [" ++ premise ++ "] --[End(k)]-> []", "rule Dead: [Fr(~n), In(" ++ input ++ ")] --[" ++ actions ++ "]-> [" ++ output ++ "]"],
          shared formula, expected)
      | input <- ["diff(~n,'known')", "diff('known',~n)", "~n"]
      , (actions, output, formula, independent) <-
          [("Dead()", "Out('bad')", once "End", True),
           ("Dead()", "Out('bad')", "All k #i. End(k)@i ==> Ex #j. Start(k)@j & #j<#i", True),
           ("End(~n)", "Out('bad')", once "End", False),
           ("Dead()", "State(~n)", once "End", False),
           ("Dead()", "!Tag(~n)", once "End", False)]
      , let premise = if output == "!Tag(~n)" then "!Tag(k)" else "State(k)"
      , let expected = independent || input == "~n"
      ]
    check name rules restrictions expected = do
      open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines $
        ["theory RestrictionPreservation begin"] ++ rules ++ restrictions ++ ["diffLemma D:", "end"]
      thy <- closeDiffTheory maudePath open False
      let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
          forms side = map (formulaToGuarded_ . L.get rstrFormula) (diffTheorySideRestrictions side thy)
          supported = all (isDiffRestrictionSupported (L.get dpcPreservedActions ctxt) (forms LHS)) (forms RHS)
      pure $ TestLabel name $ TestCase $ do
        assertEqual "restriction certificate" expected supported
        assertEqual "notice agrees with proof applicability" (not expected)
          ("RHS: R" `isInfixOf` render (prettyDiffRestrictionLimit thy))

partialEvaluationDiffTests :: FilePath -> IO Test
partialEvaluationDiffTests maudePath = do
    let models =
          [ ["builtins: symmetric-encryption",
             "rule Dec: [In(x),In(k)] --> [Out(diff(sdec(x,k),x))]"]
          , ["rule SeedA: [] --> [State('a')]",
             "rule SeedB: [] --> [State('b')]",
             "rule Use: [State(x)] --[Used(x)]-> [Out(x)]"]
          , ["rule Seed: [] --> [State(diff('a','b'))]",
             "rule Use: [State('a')] --> [Out('ok')]"]
          ]
    cases <- sequence [makeCase model auto | model <- models, auto <- [False, True]]
    pure $ TestLabel "Diff partial evaluation families" $ TestList cases
  where
    makeCase model auto = do
        open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $
            unlines (["theory PartialEvaluation begin"] ++ model ++ ["diffLemma D:", "end"])
        original <- closeDiffTheory maudePath open auto
        let refined = applyPartialEvaluationDiff Silent auto original
            reopened = closeDiffTheoryWithMaude (L.get diffThySignature refined)
                         (openDiffTheory refined) auto
            rules t = (sort (leftTheoryRules t), sort (rightTheoryRules t))
            names side t = S.fromList
              [getRuleName (L.get cprRuleE r) | r <- diffTheorySideRules side t]
        pure $ TestCase $ do
            assertEqual "analysis preserves complete compiled families" (rules original) (rules refined)
            mapM_ (\cache -> assertEqual "analysis preserves cached sources"
              (L.get cache original) (L.get cache refined))
              [diffThyCacheLeft,diffThyCacheRight,diffThyDiffCacheLeft,diffThyDiffCacheRight]
            assertEqual "analysis preserves all existing items and proofs"
              (L.get diffThyItems original) (tail (L.get diffThyItems refined))
            mapM_ (\side -> assertEqual "original family identities"
              (names side original) (names side refined)) [LHS, RHS]
            assertEqual "unchanged compiled families survive reopening" (rules refined) (rules reopened)
            printed <- either (assertFailure . show) pure $
              parseOpenDiffTheoryString [] (render (prettyClosedDiffTheory refined))
            let warnings = checkWellformednessDiff printed (L.get diffThySignature refined)
            assertBool (render (prettyWfErrorReport warnings)) (null warnings)
            reparsed <- closeDiffTheory maudePath printed auto
            -- Compare compiled behavior, including all action annotations,
            -- across export and reload.
            mapM_ (\side -> do
              let before = map (L.get cprRuleAC) (diffTheorySideRules side refined)
                  after = map (L.get cprRuleAC) (diffTheorySideRules side reparsed)
                  covered xs ys = all (\x -> any (eqModuloFreshnessNoAC x) ys) xs
              assertEqual "printed variant count" (length before) (length after)
              assertBool "unchanged compiled families survive printing and parsing up to renaming"
                (covered before after && covered after before)) [LHS, RHS]
