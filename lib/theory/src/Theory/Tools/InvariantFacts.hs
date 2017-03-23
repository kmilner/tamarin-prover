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
    addInvariantsToRules
  , invariantFactTerms
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
addInvariantsToRules :: M.Map FactTag [Bool] -> [ProtoRuleAC] -> [ProtoRuleAC]
addInvariantsToRules invarM rules = map addInvarAnnotations rules
  where
    -- Given a mapping of FactTags to invariant positions and a protocol rule,
    -- find the occurrences of those tags in the premise and conclusions of the
    -- rule and pair them with the appropriate invariant positions. For each
    -- pair, create a new invariant fact with the conclusion and invariant
    -- positions and put them all into the rule's invariants and conclusions.
    addInvarAnnotations :: ProtoRuleAC -> ProtoRuleAC
    addInvarAnnotations (Rule i ps cs as) = (Rule i ps' cs' as)
      where
        ps' = map setInvars ps
        cs' = map setInvars cs
        setInvars (Fact tag@(ProtoFact m s i) ts) = 
            Fact (ProtoFact m s (M.findWithDefault i tag invarM)) ts
        setInvars fa = fa

invariantFactTerms :: [ProtoRuleE] -> M.Map FactTag [Bool]
invariantFactTerms rules = M.fromList $ do
    tag <- candidates
    guard $ not $ null $ sameTermIndices tag
    return (tag, sameTermIndices tag)
  where
    sameTermIndices tag = foldl1' (zipWith (&&)) $ do
        ru <- rules
        guard $ not $ null (prems tag ru) || null (concs tag ru)
        zipWith (zipWith (==))
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
