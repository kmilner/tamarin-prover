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
--  addRuleInvariants
    invariantFactTerms
  ) where

import           Extension.Prelude   (sortednub)
import           Control.Monad.Fresh
import           Data.Label
import           Data.List
--import           Data.Maybe
import qualified Data.Map            as M

import           Theory.Model

-- | Compute an under-approximation of possible invariant terms of existing
-- facts in a rule. When there are multiple instances of the same fact tag,
-- in the premises and conclusions, we assume we should compare the terms
-- of the ith occurance in the premise with the ith occurance in the conclusion.
addInvariantsToRules :: [ProtoRuleAC] -> M.Map FactTag [Int] -> [ProtoRuleAC]
addInvariantsToRules rules invarM = map addInvarAnnotations rules
  where
    -- Given a mapping of FactTags to invariant positions and a protocol rule,
    -- find the occurrences of those tags in the premise and conclusions of the
    -- rule and pair them with the appropriate invariant positions. For each
    -- pair, create a new invariant fact with the conclusion and invariant
    -- positions and put them all into the rule's invariants and conclusions.
    addInvarAnnotations :: ProtoRuleAC -> ProtoRuleAC
    addInvarAnnotations (Rule i ps cs as) = (Rule newinfo ps cs as)
      where
        newinfo   = set pracFactInvariants (mapLookup ps, mapLookup cs) i
        mapLookup = map (\fa -> M.lookup (factTag fa) invarM)
{-
 ---        set rConcs (get rConcs ru ++ newConcs)
 -        set rPrems (get rPrems ru ++ newPrems) ru
 -      where
 -        newPrems = (convertFact Persist <$> persists) ++ (convertFact Remove <$> removed)
 ---        newConcs = convertFact Create <$> created
 -
 -        -- By only examining facts with invariants, and from the assumption that the i-th
 -        -- occurance in the premises matches up to the i-th occurance in the conclusions,
 -        -- we can pick out the removed/new/matched instances by counting alone
 -        -- TODO: Partition this in a less gross way
 -        (persists, created) = partition
 -            (\fa -> length (prems (factTag fa) ru) > concCount fa) $ invarsOf $ get rConcs ru
 -        removed             = filter
 -            (\fa -> length (concs (factTag fa) ru) <= premCount fa) $ invarsOf $ get rPrems ru
 -
 -        invarsOf     = filter (\fa -> factTag fa `M.member` invarM)
 -        concCount fa = fromJust $ elemIndex fa $ concs (factTag fa) ru
 -        premCount fa = fromJust $ elemIndex fa $ prems (factTag fa) ru
 -
 -        convertFact s fa = invariantFact s (factTagName $ factTag fa) $ (getFactTerms fa !!)
 -            <$> M.findWithDefault (error $ "Invalid invariant lookup: " ++ show (factTag fa))
 -                    (factTag fa) invarM
 -}

invariantFactTerms :: [ProtoRuleE] -> M.Map FactTag [Int]
invariantFactTerms rules = M.fromList $ do
    tag <- candidates
    guard $ not $ null $ sameTermIndices tag
    return (tag, sameTermIndices tag)
  where
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
