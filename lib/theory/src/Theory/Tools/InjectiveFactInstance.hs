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
module Theory.Tools.InjectiveFactInstance (

      InjectiveFactInstance(..)

    -- ** Constructing all instances
    , processInjectiveFacts

    -- ** Get all tags from a set
    , injectiveFactTags

    -- ** Pretty printing
    , prettyInjFact
) where

import           Control.DeepSeq
import           Extension.Prelude   (sortednub)
import           Data.DeriveTH
import           Data.Binary

-- import           Control.Applicative
import           Control.Monad.Fresh
import qualified Data.Label          as L
import qualified Data.Set            as S
import           Safe                (headMay)

import           Theory.Model
import           Theory.Text.Pretty
import           Text.PrettyPrint.Html


data InjectiveFactInstance = InjectiveFactInstance
    { injectiveFactTag   :: FactTag
    , creationRules      :: S.Set ProtoRuleE
    , destructionRules   :: S.Set ProtoRuleE
    }
    deriving( Eq, Ord, Show)

-- | Compute a simple under-approximation to the set of facts with injective
-- instances. A fact-tag is has injective instances, if there is no state of
-- the protocol with more than one instance with the same term as a first
-- argument of the fact-tag.
--
-- We compute the under-approximation by checking that
-- (1) the fact-tag is linear,
-- (2) every introduction of such a fact-tag is protected by a Fr-fact of the
--     first term, and
-- (3) every rule has at most one copy of this fact-tag in the conclusion and
--     the first term arguments agree.
--
-- We exclude facts that are not copied in a rule, as they are already handled
-- properly by the naive backwards reasoning.
processInjectiveFacts :: [ProtoRuleE] -> S.Set InjectiveFactInstance
processInjectiveFacts rules = S.fromList $ do
    tag         <- candidates
    guard (all (guardedSingletonCopy tag) rules)
    return InjectiveFactInstance {
          injectiveFactTag  = tag
        , creationRules     = (S.fromList $ constructions tag)
        , destructionRules  = (S.fromList $ destructions tag) }
  where
    candidates = sortednub $ do
        ru  <- rules
        tag <- factTag <$> L.get rConcs ru
        guard $    (factTagMultiplicity tag == Linear)
                && (tag `elem` (factTag <$> L.get rPrems ru))
        return tag

    constructions tag = filter (guardedCreation tag) rules

    guardedCreation tag ru =
        length copies == 1 && all guardedConc copies
      where
        copies              = filter ((tag ==) . factTag) (L.get rConcs ru)
        guardedConc faConc  = case (headMay . factTerms) faConc of
            Nothing     -> False
            Just tConc  -> freshFact tConc `elem` (L.get rPrems ru)

    destructions :: FactTag -> [ProtoRuleE]
    destructions tag = filter
        (\r -> (any ((tag ==) . factTag) (L.get rPrems r))
                && (not $ any ((tag ==) . factTag)  (L.get rConcs r))) rules

    guardedSingletonCopy tag ru =
        length copies <= 1 && all guardedCopy copies
      where
        prems              = L.get rPrems ru
        copies             = filter ((tag ==) . factTag) (L.get rConcs ru)
        firstTerm          = headMay . factTerms

        -- True if there is a first term and a premise guarding it
        guardedCopy faConc = case firstTerm faConc of
            Nothing    -> False
            Just tConc -> freshFact tConc `elem` prems || guardedInPrems tConc

        -- True if there is a premise with the same tag and first term
        guardedInPrems tConc = (`any` prems) $ \faPrem ->
            factTag faPrem == tag && maybe False (tConc ==) (firstTerm faPrem)



injectiveFactTags :: S.Set InjectiveFactInstance -> S.Set FactTag
injectiveFactTags injfacts = foldr (\x -> S.insert (injectiveFactTag x)) S.empty injfacts

-- Pretty-Printing
--------------------

prettyInjFact :: (HighlightDocument d) => InjectiveFactInstance -> d
prettyInjFact x = (fsep [keyword (text $ showFactTagArity $ injectiveFactTag x)])
                  $-$ (fsep [text "Constructed by:", vcat (ppRuleNames $ creationRules x)])
                  $-$ (destr (ppRuleNames $ destructionRules x))
        where
            destr [] = text "(Not destructed)"
            destr  s = fsep [text "Destructed by:",  vcat s]

            ppRuleNames s = map prettyRuleName $ S.toList s


-- derived instances
--------------------

$( derive makeBinary ''InjectiveFactInstance)
$( derive makeNFData ''InjectiveFactInstance)
