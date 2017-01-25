{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE FlexibleContexts   #-}

-- |
-- Copyright   : (c) 2012 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Computate an under-approximation to the set of all facts with unique
-- instances, i.e., fact whose instances never occur more than once in a
-- state. We use this information to reason about protocols that exploit
-- exclusivity of linear facts.
module Theory.Tools.InjectiveFacts (
      InjectiveFacts
    , InjectiveFactInfo(..)

    -- ** Constructing all instances
    , findInjectiveFacts

    -- ** Pretty printing
    , prettyInjFacts
) where

import           Control.DeepSeq
import           Extension.Prelude   (sortednub)
import           Data.DeriveTH
import           Data.Binary

-- import           Control.Applicative
import           Control.Monad.Fresh
import qualified Extension.Data.Label          as L
import qualified Data.Set            as S
import qualified Data.Map            as M

import           Theory.Model
import           Theory.Text.Pretty

type InjectiveFacts = M.Map FactTag InjectiveFactInfo

data InjectiveFactInfo = InjectiveFactInfo
    { _ifiConstructionRules  :: S.Set ProtoRuleAC
    , _ifiDestructionRules   :: S.Set ProtoRuleAC
    , _ifiFreshTermIndex     :: Int
    }
    deriving( Eq, Ord, Show)

$(L.mkLabels [''InjectiveFactInfo])

-- | Compute a simple under-approximation to the set of facts with injective
-- instances. A fact-tag is has injective instances, if there is no state of
-- the protocol with more than one instance with the same term as a ith
-- argument of the fact-tag.
--
-- We compute the under-approximation by checking that
-- (1) the fact-tag is linear,
-- (2) every introduction of such a fact-tag is protected by a Fr-fact of some
--     ith term, and
-- (3) every rule has at most one copy of this fact-tag in the conlcusion and
--     the ith term arguments agree.
--
-- We exclude facts that are not copied in a rule, as they are already handled
-- properly by the naive backwards reasoning.
findInjectiveFacts :: [ProtoRuleAC] -> InjectiveFacts
findInjectiveFacts rules = M.fromList $ do
    (tag, i)       <- candidates
    guard $ not $ any (counterexample (tag, i)) rules
    return (tag, InjectiveFactInfo 
                    { _ifiConstructionRules =  S.fromList $ constructions (tag, i)
                    , _ifiDestructionRules  =  S.fromList $ destructions (tag, i)
                    , _ifiFreshTermIndex    =  i
                    })
  where
    concTags r          = factTag <$> L.get rConcs r
    premTags r          = factTag <$> L.get rPrems r
    ithTerm i fact      = factTerms fact !! i
    tagsInConcs tag ru  = filter ((tag ==) . factTag) (L.get rConcs ru)

    candidates = sortednub $ do
        ru      <- rules
        fact    <- L.get rConcs ru
        let tag  = factTag fact
        guard $ (factTagMultiplicity tag == Linear) && (tag `elem` premTags ru)
        i       <- [0..(factArity fact) - 1]
        return (tag, i)

    -- Returns the ith terms of facts with the matching tag
    ithFactTerms (tag, i) fs = map (ithTerm i) $ filter ((tag ==) . factTag) fs

    -- All rules where the fact is only in conclusions once, and the ith term
    -- was generated fresh
    constructions (tag, i) = filter
        (\r -> (length (tagsInConcs tag r) == 1) && (all (freshConc r) (tagsInConcs tag r))) rules
      where
        freshConc ru faConc  = freshFact (ithTerm i faConc) `elem` (L.get rPrems ru)

    -- All rules where the fact and its ith term argument is a premise but isn't in conclusions
    destructions (tag, i) = filter
        (\r -> any (not . inConcs r) (ithFactTerms (tag, i) (L.get rPrems r))) rules
      where
        inConcs ru term = elem term $ ithFactTerms (tag, i) (L.get rConcs ru)

    -- A rule is a counterexample to injectivity if the fact is in the conclusions
    -- multiple times, or if it is in the conclusion without a corresponding premise
    -- or fresh term, or if the ith term is not a fresh term in every construction
    counterexample (tag, i) r  = length (tagsInConcs tag r) > 1
        || (not (elem r $ constructions (tag, i))
            && any unmatched (tagsInConcs tag r))
        || length (constructions (tag, i))  == 0 -- this requires every injective fact to have at least one construction rule
      where
        unmatched faConc = not $ (`any` L.get rPrems r) $ \faPrem ->
            factTag faPrem == tag && ithTerm i faConc == ithTerm i faPrem

-- Pretty-Printing
--------------------
prettyInjFacts :: (HighlightDocument d) => InjectiveFacts -> d
prettyInjFacts injs = vsep $ map ppInjFact $ M.toList injs
  where
    ppInjFact (f,l) = (fsep [keyword (text $ showFactTagArity f),
                             text (" with fresh term at index " ++ show (L.get ifiFreshTermIndex l))])
                        $-$ (fsep [text "Constructed by:", vcat (ppRuleNames $ constructs l)])
                        $-$ (destr (ppRuleNames $  destructs l))
      
    destr []        = text "(Not destructed)"
    destr  s        = fsep [text "Destructed by:",  vcat s]

    ppRuleNames s   = map prettyRuleName $ S.toList s

    constructs info = L.get ifiConstructionRules info
    destructs info  = L.get ifiDestructionRules info

-- derived instances
--------------------

$( derive makeBinary ''InjectiveFactInfo)
$( derive makeNFData ''InjectiveFactInfo)
