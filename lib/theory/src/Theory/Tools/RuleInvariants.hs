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

module Theory.Tools.RuleInvariants (

  -- * Computing and adding invariant term facts.
  addRuleInvariants
  ) where

import           Extension.Prelude   (sortednub)
import           Debug.Trace
-- import           Control.Applicative
import           Control.Monad.Fresh
import           Data.Label
import           Data.List
import qualified Data.Map            as M
import           Safe                (headMay)

import           Theory.Model



addRuleInvariants :: [ProtoRuleAC] -> [ProtoRuleAC]
addRuleInvariants rules =
    constructInvariants $ (\ru -> set rInvars (directInvariants ru) ru) <$> rules
  where
    directInvariants ru = nub $ intersect (get rPrems ru) (get rConcs ru)

-- | Compute an under-approximation of possible invariant terms of existing
-- facts in a rule. When there are multiple instances of the same fact tag,
-- in the premises and conclusions, we assume we should compare the terms
-- of the ith occurance in the premise with the ith occurance in the conclusion.
constructInvariants :: [ProtoRuleAC] -> [ProtoRuleAC]
constructInvariants rules =
--    map (addInvarsandConcs $ invariantFactTerms rules) rules
    trace (show $ invariantFactTerms rules) rules
  where
--    addInvarsandConcs :: M.Map FactTag [Int] -> ProtoRuleAC -> ProtoRuleAC
--    addInvarsandConcs invars ru =

    invariantFactTerms :: [ProtoRuleAC] -> M.Map FactTag [Int]
    invariantFactTerms rules = M.fromList $ do
        tag <- candidates
        return (tag, sameTermIndices tag rules)
      where
        sameTermIndices :: FactTag -> [ProtoRuleAC] -> [Int]
        sameTermIndices tag rules = foldr1 intersect $ do
            ru <- rules
            guard $ not $ null (prems tag ru) || null (concs tag ru)
            elemIndices True <$> zipWith (zipWith (==))
                (getFactTerms <$> prems tag ru) (getFactTerms <$> concs tag ru)

    prems tag ru = filter ((tag ==) . factTag) $ get rPrems ru
    concs tag ru = filter ((tag ==) . factTag) $ get rConcs ru

    -- We only worry about constructing invariant out of fact tags that
    -- actually occur in the premise and conclusion of some rule without
    -- being being directly invariant
    candidates = sortednub $ do
        ru  <- rules
        tag <- factTag <$> get rConcs ru
        guard $    (factTagMultiplicity tag == Linear)
                && (tag `notElem` (factTag <$> get rInvars ru))
                && (tag `elem` (factTag <$> get rPrems ru))
        return tag
