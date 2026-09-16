-- Focused invariants at boundaries that can change proof verdicts.
module Test.VerdictTests (tests) where

import Data.List (isInfixOf, sort)
import Data.Maybe (fromJust)
import Lemma
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Extension.Data.Label as L
import Test.HUnit

import ClosedTheory
import Prover
import Rule
import Theory.Model
import Theory.Constraint.System
import Theory.Text.Parser
import Theory.Text.Pretty (render)
import TheoryObject

-- Exercise the real mirror enumerator, including Maude AC unification and
-- graph-wide consistency. Two connected consumers make four independent
-- assignments, distinguishable by their action arguments.
tests :: FilePath -> IO Test
tests maudePath = TestList <$> sequence
    [ mirrorTests maudePath
    , roundTripTests maudePath
    , assumptionTests maudePath
    , conditionalRestrictionTests maudePath
    , mixedRestrictionFilterTests maudePath
    , diffRestrictionLocalityTests maudePath
    , diffRestrictionPreservationTests maudePath
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

-- Closing an already compiled side must preserve its complete variant family,
-- new-variable vectors, source assumptions, restrictions and proof skeletons.
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
                                case item of EitherRuleItem _ -> False; _ -> True]
        pure $ TestCase $ mapM_ (\t -> do
            assertEqual "side rules, variants and new variables" (rules first) (rules t)
            assertEqual "lemmas, restrictions and proof skeletons" (nonRules first) (nonRules t)
            assertEqual "all four rule/source caches" (caches first) (caches t)) [second,third]

-- Check eligibility before proof search, including same-named opposite-side
-- assumptions, declaration order for ordinary reuse, and both hide forms.
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
          [ ("constant guard, symbolic action", "All #i. A('a')@i ==> F", [Nothing], TTrue)
          , ("constant guard, permitted action", "All #i. A('a')@i ==> F", [Just "b"], TTrue)
          , ("constant guard, forbidden action", "All #i. A('a')@i ==> F", [Just "a"], TFalse)
          , ("unconditional symbolic violation", "All x #i. A(x)@i ==> F", [Nothing], TFalse)
          , ("nested conditional violation", "All x #i. A(x)@i ==> (All #j. A('a')@j ==> F)", [Nothing], TTrue)
          ]
    tests' <- sequence [makeCase label formula values expected solved
                      | (label,formula,values,expected) <- cases, solved <- [False,True]]
    pure $ TestLabel "Conditional restriction instances" $ TestList tests'
  where
    makeCase label formula values expected solved = do
        open <- either (fail . show) pure $ parseOpenDiffTheoryString [] $ unlines
          [ "theory ConditionalRestrictions begin"
          , "rule R: [In(x)] --[ A(x) ]-> []"
          , "restriction Check: \"" ++ formula ++ "\""
          , "diffLemma D:", "end"
          ]
        thy <- closeDiffTheory maudePath open False
        let ctxt = getDiffProofContext (head (diffTheoryDiffLemmas thy)) thy
            rule = fst $ someRuleACInstAvoiding (fmap ProtoInfo (L.get cprRuleAC (head (leftTheoryRules thy)))) ([] :: [LVar])
            atNode i value = (LVar "n" LSortNode i,
                apply (substFromList [(v, maybe (varTerm (LVar "x" LSortMsg (100+i))) pubTerm value) | v <- frees rule]) rule)
            sys = L.set sNodes (M.fromList (zipWith atNode [0..] values)) $ emptySystem RawSource True
            original = L.set dsSide (Just LHS) $ L.set dsSystem (Just sys) emptyDiffSystem
        pure $ TestCase $ assertEqual (label ++ "; solved=" ++ show solved) expected
          (fst (evaluateRestrictions ctxt original [sys] solved))

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

-- Multi-event restrictions transfer only when all of their observations do.
-- In particular, identical action syntax with independently chosen inputs
-- does not establish preservation of the action arguments.
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
