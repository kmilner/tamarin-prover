-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Computate an under-approximation to the set of invariant
-- terms for each fact, and then generate invariants and
-- conclusions for rules to allow solving for the source of
-- those terms directly.

module Theory.Tools.InvariantFacts (

  -- * Computing and adding invariant term facts.
  addRuleInvariants
  ) where

import           Extension.Prelude   (sortednub)
-- import           Debug.Trace
-- import           Control.Applicative
import           Control.Monad.Fresh
import           Data.Label
import           Data.List
import           Data.Maybe
import qualified Data.Map            as M

import           Theory.Model



--addRuleInvariants :: [ProtoRuleAC] -> [ProtoRuleAC]
--addRuleInvariants rules =
--    constructInvariants $ (\ru -> set rInvars (directInvariants ru) ru) <$> rules
--  where
--    directInvariants ru = (\f -> protoToInvFact f Nothing) <$> (nub $ intersect (get rPrems ru) (get rConcs ru))

-- | Compute an under-approximation of possible invariant terms of existing
-- facts in a rule. When there are multiple instances of the same fact tag,
-- in the premises and conclusions, we assume we should compare the terms
-- of the ith occurance in the premise with the ith occurance in the conclusion.
addRuleInvariants :: [ProtoRuleAC] -> [ProtoRuleAC]
addRuleInvariants rules =
    map (addInvars invariantFactTerms) rules
  where
    -- Given a mapping of FactTags to invariant positions and a protocol rule,
    -- find the occurrences of those tags in the premise and conclusions of the
    -- rule and pair them with the appropriate invariant positions. For each
    -- pair, create a new invariant fact with the conclusion and invariant
    -- positions and put them all into the rule's invariants and conclusions.
    addInvars :: M.Map FactTag [Int] -> ProtoRuleAC -> ProtoRuleAC
    addInvars invars ru =
        set rConcs (get rConcs ru ++ newConcs)
            $ set rPrems (get rPrems ru ++ newPrems) ru
      where
        newPrems = convertFact Persist <$> matched
        newConcs = convertFact Persist <$> new

        (matched, new) = partition
            (\fa -> length (prems (factTag fa) ru) > concCount fa ru) $ invConcs ru
        invConcs r = filter (\fa -> factTag fa `M.member` invars) $ get rConcs r
        --This is a terrible hack, I'm sorry
        concCount fa r = fromJust $ elemIndex fa $ concs (factTag fa) r

        convertFact :: Lifetime -> LNFact -> LNFact
        convertFact s fa = invariantFact s (factTagName $ factTag fa) $ 
            (getFactTerms fa !!) <$> M.findWithDefault (error "Map missing invariant") (factTag fa) invars

    invariantFactTerms = M.fromList $ do
        tag <- candidates
        return (tag, sameTermIndices tag)
      where
        sameTermIndices :: FactTag -> [Int]
        sameTermIndices tag = foldr1 intersect $ do
            ru <- rules
            guard $ not $ null (prems tag ru) || null (concs tag ru)
            elemIndices True <$> zipWith (zipWith (==))
                (getFactTerms <$> prems tag ru) (getFactTerms <$> concs tag ru)

    prems tag ru = filter ((tag ==) . factTag) $ get rPrems ru
    concs tag ru = filter ((tag ==) . factTag) $ get rConcs ru

    -- We only worry about constructing invariant out of protofact tags that
    -- actually occur in the premise and conclusion of some rule
    candidates = sortednub $ do
        ru  <- rules
        tag <- factTag <$> filter isProtoFact (get rConcs ru)
        guard $    (factTagMultiplicity tag == Linear)
                && (tag `elem` (factTag <$> get rPrems ru))
        return tag
