{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Items.RuleItem (
    module Items.RuleItem
) where

import GHC.Generics
import Control.DeepSeq
import Data.Binary

import           Prelude                             hiding (id, (.))


import qualified Data.Set                            as S

import           Control.Category
import           Extension.Data.Label                hiding (get)
import qualified Extension.Data.Label                as L

import           Theory.Model
import           Theory.Proof
import           Theory.Tools.InjectiveFactInstances

------------------------------------------------------------------------------
-- Commented sets of rewriting rules
------------------------------------------------------------------------------

-- | A protocol rewriting rule modulo E together with its possible assertion
-- soundness proof.
-- Optionally, the variant(s) modulo AC can be present if they were loaded
-- or contain additional actions.
data OpenProtoRule = OpenProtoRule
       { _oprRuleE  :: ProtoRuleE             -- original rule modulo E
       , _oprRuleAC :: [ProtoRuleAC]          -- variant(s) modulo AC
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A diff protocol rewriting rule modulo E
-- Optionally, the left and right rules can be present if they were loaded
-- or contain additional actions.
data DiffProtoRule = DiffProtoRule
       { _dprRule       :: ProtoRuleE         -- original rule with diff
       , _dprLeftRight  :: Maybe (OpenProtoRule, OpenProtoRule)
                                              -- left and right instances
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A closed proto rule lists its original rule modulo E, the corresponding
-- variant(s) modulo AC, and if required the assertion soundness proof.
-- When using auto-sources, all non-trivial variants of a ClosedProtoRule are
-- split up into multiple ClosedProtoRules. Auto-sources also only adds
-- actions only to closed rules. Opening such rules keeps the AC rules s.t.
-- they can be exported.
data ClosedProtoRule = ClosedProtoRule
       { _cprRuleE         :: ProtoRuleE      -- original rule modulo E
       , _cprRuleAC        :: ProtoRuleAC     -- variant(s) modulo AC
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

-- | A compiled family owns its E-rule even when compilation removes every
-- variant. Unlike an OpenProtoRule, an empty member list means no executions.
data ClosedRuleFamily = ClosedRuleFamily ProtoRuleE [ProtoRuleAC]
       deriving (Eq, Ord, Show, Generic, NFData, Binary)

-- | The two compiled sides belong to this parent throughout closing, source
-- annotation and reopening. Member names are not used to recover ownership.
data ClosedDiffRule = ClosedDiffRule ProtoRuleE ClosedRuleFamily ClosedRuleFamily
       deriving (Eq, Ord, Show, Generic, NFData, Binary)

closedFamilyRules :: ClosedRuleFamily -> [ClosedProtoRule]
closedFamilyRules (ClosedRuleFamily parent members) = map (ClosedProtoRule parent) members

closedDiffSide :: Side -> ClosedDiffRule -> ClosedRuleFamily
closedDiffSide LHS (ClosedDiffRule _ left _) = left
closedDiffSide RHS (ClosedDiffRule _ _ right) = right

closedDiffParent :: ClosedDiffRule -> ProtoRuleE
closedDiffParent (ClosedDiffRule parent _ _) = parent

-- | Transform members in place, retaining their parent and positional slots.
traverseClosedFamily :: Applicative f
    => (ProtoRuleE -> ProtoRuleAC -> f [ProtoRuleAC])
    -> ClosedRuleFamily -> f ClosedRuleFamily
traverseClosedFamily f (ClosedRuleFamily parent members) =
    ClosedRuleFamily parent . concat <$> traverse (f parent) members

traverseClosedDiffRule :: Applicative f
    => (Side -> ProtoRuleE -> ProtoRuleAC -> f [ProtoRuleAC])
    -> ClosedDiffRule -> f ClosedDiffRule
traverseClosedDiffRule f (ClosedDiffRule parent left right) =
    ClosedDiffRule parent <$> traverseClosedFamily (f LHS) left
                         <*> traverseClosedFamily (f RHS) right

type OpenRuleCache = [IntrRuleAC]

data ClosedRuleCache = ClosedRuleCache
       { _crcRules               :: ClassifiedRules
       , _crcRawSources          :: [Source]
       , _crcRefinedSources      :: [Source]
       , _crcInjectiveFactInsts  :: S.Set (FactTag, [[MonotonicBehaviour]])
       }
       deriving( Eq, Ord, Show, Generic, NFData, Binary )

$(mkLabels [''OpenProtoRule, ''DiffProtoRule, ''ClosedProtoRule, ''ClosedRuleCache])

instance HasRuleName OpenProtoRule where
    ruleName = ruleName . L.get oprRuleE

instance HasRuleName DiffProtoRule where
    ruleName = ruleName . L.get dprRule

instance HasRuleName ClosedProtoRule where
    ruleName = ruleName . L.get cprRuleAC
