-- Focused invariants at boundaries that can change proof verdicts.
module Test.VerdictTests (tests) where

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
import TheoryObject

-- Exercise the real mirror enumerator, including Maude AC unification and
-- graph-wide consistency. Two connected consumers make four independent
-- assignments, distinguishable by their action arguments.
tests :: FilePath -> IO Test
tests maudePath = do
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
