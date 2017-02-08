{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Rewriting rules representing protocol execution and intruder deduction. Once
-- modulo the full Diffie-Hellman equational theory and once modulo AC.
module Theory.Model.Rule (
  -- * General Rules
    Rule(..)
  , PremIdx(..)
  , ConcIdx(..)

  -- ** Accessors
  , rInfo
  , rPrems
  , rConcs
  , rActs
  , rInvars
  , rPrem
  , rConc
  , rInvar
  , lookupPrem
  , lookupConc
  , lookupInvar
  , enumPrems
  , enumConcs
  , enumInvars

  -- ** Genereal protocol and intruder rules
  , RuleInfo(..)
  , ruleInfo

  -- * Protocol Rule Information
  , ProtoRuleName(..)
  , ProtoRuleACInfo(..)
  , pracName
  , pracVariants
  , pracLoopBreakers
  , ProtoRuleACInstInfo(..)
  , praciName
  , praciLoopBreakers
  , RuleACConstrs

  -- * Intruder Rule Information
  , IntrRuleACInfo(..)

  -- * Concrete Rules
  , ProtoRuleE
  , ProtoRuleAC
  , IntrRuleAC
  , RuleAC
  , RuleACInst

  -- ** Queries
  , HasRuleName(..)
  , isIntruderRule
  , isDestrRule
  , isIEqualityRule
  , isConstrRule
  , isPubConstrRule
  , isFreshRule
  , isIRecvRule
  , isISendRule
  , isCoerceRule
  , isProtocolRule
  , isConstantRule
  , isSubtermRule
  , containsNewVars
  , getRuleName
  , getRuleNameDiff
  , getRemainingRuleApplications
  , setRemainingRuleApplications
  , nfRule
  , normRule
  , isTrivialProtoVariantAC
  , getNewVariables
  , getSubstitutionsFixingNewVars

  -- ** Conversion
  , ruleACToIntrRuleAC
  , ruleACIntrToRuleAC
  , ruleACIntrToRuleACInst
  , getLeftRule
  , getRightRule

  -- ** Construction
  , someRuleACInst
  , someRuleACInstAvoiding
  , someRuleACInstAvoidingFixing
  , someRuleACInstFixing
  , addDiffLabel
  , removeDiffLabel
  , multRuleInstance
  , unionRuleInstance

  -- ** Unification
  , unifyRuleACInstEqs
  , unifiableRuleACInsts

  -- * Pretty-Printing
  , reservedRuleNames
  , showRuleCaseName
  , prettyProtoRuleName
  , prettyRuleName
  , prettyProtoRuleE
  , prettyProtoRuleAC
  , prettyIntrRuleAC
  , prettyIntrRuleACInfo
  , prettyRuleAC
  , prettyLoopBreakers
  , prettyRuleACInst

  )  where

import           Prelude              hiding (id, (.))

import           GHC.Generics (Generic)
import           Data.Binary
import qualified Data.ByteString.Char8 as BC
-- import           Data.Foldable        (foldMap)
import           Data.Data
import           Data.List
import qualified Data.Set              as S
import qualified Data.Map              as M
import           Data.Monoid
import           Data.Maybe            (fromMaybe)
import           Safe

-- import           Control.Basics
import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Bind
import           Control.Monad.Reader

import           Extension.Data.Label hiding (get)
import qualified Extension.Data.Label as L
import           Logic.Connectives

import           Term.LTerm
import           Term.Rewriting.Norm  (nf')
import           Term.Unification
import           Theory.Model.Fact
import           Theory.Text.Pretty

-- import           Debug.Trace

------------------------------------------------------------------------------
-- General Rule
------------------------------------------------------------------------------

-- | Rewriting rules with arbitrary additional information and facts with names
-- and logical variables.
data Rule i = Rule {
         _rInfo   :: i
       , _rPrems  :: [LNFact]
       , _rConcs  :: [LNFact]
       , _rActs   :: [LNFact]
       , _rInvars :: [LNFact]
       }
       deriving( Eq, Ord, Show, Data, Typeable, Generic)

instance NFData i => NFData (Rule i)
instance Binary i => Binary (Rule i)

$(mkLabels [''Rule])

-- | An index of a premise. The first premise has index '0'.
newtype PremIdx = PremIdx { getPremIdx :: Int }
  deriving( Eq, Ord, Show, Enum, Data, Typeable, Binary, NFData )

-- | An index of a conclusion. The first conclusion has index '0'.
newtype ConcIdx = ConcIdx { getConcIdx :: Int }
  deriving( Eq, Ord, Show, Enum, Data, Typeable, Binary, NFData )

-- | An index of an invariant. The first invariant has index '0'.
newtype InvarIdx = InvarIdx { getInvarIdx :: Int }
  deriving( Eq, Ord, Show, Enum, Data, Typeable, Binary, NFData )


-- | @lookupPrem i ru@ returns the @i@-th premise of rule @ru@, if possible.
lookupPrem :: PremIdx -> Rule i -> Maybe LNFact
lookupPrem i = (`atMay` getPremIdx i) . L.get rPrems

-- | @lookupConc i ru@ returns the @i@-th conclusion of rule @ru@, if possible.
lookupConc :: ConcIdx -> Rule i -> Maybe LNFact
lookupConc i = (`atMay` getConcIdx i) . L.get rConcs

-- | @lookupInvar i ru@ returns the @i@-th invariant of rule @ru@, if possible.
lookupInvar :: InvarIdx -> Rule i -> Maybe LNFact
lookupInvar i = (`atMay` getInvarIdx i) . L.get rInvars

-- | @rPrem i@ is a lens for the @i@-th premise of a rule.
rPrem :: PremIdx -> (Rule i :-> LNFact)
rPrem i = nthL (getPremIdx i) . rPrems

-- | @rConc i@ is a lens for the @i@-th conclusion of a rule.
rConc :: ConcIdx -> (Rule i :-> LNFact)
rConc i = nthL (getConcIdx i) . rConcs

-- | @rInvar i@ is a lens for the @i@-th invariant of a rule.
rInvar :: InvarIdx -> (Rule i :-> LNFact)
rInvar i = nthL (getInvarIdx i) . rInvars


-- | Enumerate all premises of a rule.
enumPrems :: Rule i -> [(PremIdx, LNFact)]
enumPrems = zip [(PremIdx 0)..] . L.get rPrems

-- | Enumerate all conclusions of a rule.
enumConcs :: Rule i -> [(ConcIdx, LNFact)]
enumConcs = zip [(ConcIdx 0)..] . L.get rConcs

-- | Enumerate all invariants of a rule.
enumInvars :: Rule i -> [(InvarIdx, LNFact)]
enumInvars = zip [(InvarIdx 0)..] . L.get rInvars

-- Instances
------------

instance Functor Rule where
    fmap f (Rule i ps cs as is) = Rule (f i) ps cs as is

instance (Show i, HasFrees i) => HasFrees (Rule i) where
    foldFrees f (Rule i ps cs as is) =
        (foldFrees f i  `mappend`) $
        (foldFrees f ps `mappend`) $
        (foldFrees f cs `mappend`) $
        (foldFrees f as `mappend`) $
        (foldFrees f is)
    foldFreesOcc f c (Rule i ps cs as is) =
        foldFreesOcc f ((show i):c) (ps, cs, as, is)
    mapFrees f (Rule i ps cs as is) =
        Rule <$> mapFrees f i
             <*> mapFrees f ps <*> mapFrees f cs <*> mapFrees f as <*> mapFrees f is

instance Apply i => Apply (Rule i) where
    apply subst (Rule i ps cs as is) =
        Rule (apply subst i) (apply subst ps) (apply subst cs) (apply subst as) (apply subst is)

instance Sized (Rule i) where
  size (Rule _ ps cs as is) = size ps + size cs + size as + size is

------------------------------------------------------------------------------
-- Rule information split into intruder rule and protocol rules
------------------------------------------------------------------------------

-- | Rule information for protocol and intruder rules.
data RuleInfo p i =
         ProtoInfo p
       | IntrInfo i
       deriving( Eq, Ord, Show, Generic)

instance (NFData i, NFData p) => NFData (RuleInfo p i)
instance (Binary i, Binary p) => Binary (RuleInfo p i)

-- | @ruleInfo proto intr@ maps the protocol information with @proto@ and the
-- intruder information with @intr@.
ruleInfo :: (p -> c) -> (i -> c) -> RuleInfo p i -> c
ruleInfo proto _    (ProtoInfo x) = proto x
ruleInfo _     intr (IntrInfo  x) = intr x


-- Instances
------------

instance (HasFrees p, HasFrees i) => HasFrees (RuleInfo p i) where
    foldFrees  f = ruleInfo (foldFrees f) (foldFrees f)
    foldFreesOcc _ _ = const mempty
    mapFrees   f = ruleInfo (fmap ProtoInfo . mapFrees   f)
                            (fmap IntrInfo . mapFrees   f)

instance (Apply p, Apply i) => Apply (RuleInfo p i) where
    apply subst = ruleInfo (ProtoInfo . apply subst) (IntrInfo . apply subst)


------------------------------------------------------------------------------
-- Protocol Rule Information
------------------------------------------------------------------------------

-- | A name of a protocol rule is either one of the special reserved rules or
-- some standard rule.
data ProtoRuleName =
         FreshRule
       | StandRule String -- ^ Some standard protocol rule
       deriving( Eq, Ord, Show, Data, Typeable, Generic)

instance NFData ProtoRuleName
instance Binary ProtoRuleName


-- | Information for protocol rules modulo AC. The variants list the possible
-- instantiations of the free variables of the rule. The source is interpreted
-- modulo AC; i.e., its variants were also built.
data ProtoRuleACInfo = ProtoRuleACInfo
       { _pracName         :: ProtoRuleName
       , _pracVariants     :: Disj (LNSubstVFresh)
       , _pracLoopBreakers :: [PremIdx]
       }
       deriving( Eq, Ord, Show, Generic)
instance NFData ProtoRuleACInfo
instance Binary ProtoRuleACInfo

-- | Information for instances of protocol rules modulo AC.
data ProtoRuleACInstInfo = ProtoRuleACInstInfo
       { _praciName         :: ProtoRuleName
       , _praciLoopBreakers :: [PremIdx]
       }
       deriving( Eq, Ord, Show, Generic)
instance NFData ProtoRuleACInstInfo
instance Binary ProtoRuleACInstInfo


$(mkLabels [''ProtoRuleACInfo, ''ProtoRuleACInstInfo])


-- Instances
------------

instance Apply ProtoRuleName where
    apply _ = id

instance HasFrees ProtoRuleName where
    foldFrees  _ = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees   _ = pure

instance Apply PremIdx where
    apply _ = id

instance HasFrees PremIdx where
    foldFrees  _ = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees   _ = pure

instance Apply ConcIdx where
    apply _ = id

instance HasFrees ConcIdx where
    foldFrees  _ = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees   _ = pure

instance HasFrees ProtoRuleACInfo where
    foldFrees f (ProtoRuleACInfo na vari breakers) =
        foldFrees f na `mappend` foldFrees f vari
                       `mappend` foldFrees f breakers
    foldFreesOcc  _ _ = const mempty
    mapFrees f (ProtoRuleACInfo na vari breakers) =
        ProtoRuleACInfo na <$> mapFrees f vari <*> mapFrees f breakers

instance Apply ProtoRuleACInstInfo where
    apply _ = id

instance HasFrees ProtoRuleACInstInfo where
    foldFrees f (ProtoRuleACInstInfo na breakers) =
        foldFrees f na `mappend` foldFrees f breakers

    foldFreesOcc  _ _ = const mempty

    mapFrees f (ProtoRuleACInstInfo na breakers) =
        ProtoRuleACInstInfo na <$> mapFrees f breakers


------------------------------------------------------------------------------
-- Intruder Rule Information
------------------------------------------------------------------------------

-- | An intruder rule modulo AC is described by its name.
data IntrRuleACInfo =
    ConstrRule BC.ByteString
  | DestrRule BC.ByteString Int Bool Bool
  -- the number of remaining consecutive applications of this destruction rule, 0 means unbounded, -1 means not yet determined
  -- true if the RHS is a true subterm of the LHS
  -- true if the RHS is a constant
  | CoerceRule
  | IRecvRule
  | ISendRule
  | PubConstrRule
  | FreshConstrRule
  | IEqualityRule -- Necessary for diff
  deriving( Ord, Eq, Show, Data, Typeable, Generic)
instance NFData IntrRuleACInfo
instance Binary IntrRuleACInfo

-- | An intruder rule modulo AC.
type IntrRuleAC = Rule IntrRuleACInfo

-- | Converts between these two types of rules, if possible.
ruleACToIntrRuleAC :: RuleAC -> Maybe IntrRuleAC
ruleACToIntrRuleAC (Rule (IntrInfo i) ps cs as is) = Just (Rule i ps cs as is)
ruleACToIntrRuleAC _                            = Nothing

-- | Converts between these two types of rules.
ruleACIntrToRuleAC :: IntrRuleAC -> RuleAC
ruleACIntrToRuleAC (Rule ri ps cs as is) = Rule (IntrInfo ri) ps cs as is

-- | Converts between these two types of rules.
ruleACIntrToRuleACInst :: IntrRuleAC -> RuleACInst
ruleACIntrToRuleACInst (Rule ri ps cs as is) = Rule (IntrInfo ri) ps cs as is

-- Instances
------------

instance Apply IntrRuleACInfo where
    apply _ = id

instance HasFrees IntrRuleACInfo where
    foldFrees _ = const mempty
    foldFreesOcc  _ _ = const mempty
    mapFrees _  = pure


------------------------------------------------------------------------------
-- Concrete rules
------------------------------------------------------------------------------

-- | A rule modulo E is always a protocol rule. Intruder rules are specified
-- abstractly by their operations generating them and are only available once
-- their variants are built.
type ProtoRuleE  = Rule ProtoRuleName

-- | A protocol rule modulo AC.
type ProtoRuleAC = Rule ProtoRuleACInfo

-- | A rule modulo AC is either a protocol rule or an intruder rule
type RuleAC      = Rule (RuleInfo ProtoRuleACInfo IntrRuleACInfo)

-- | A rule instance module AC is either a protocol rule or an intruder rule.
-- The info identifies the corresponding rule modulo AC that the instance was
-- derived from.
type RuleACInst  = Rule (RuleInfo ProtoRuleACInstInfo IntrRuleACInfo)

-- Accessing the rule name
--------------------------

-- | Types that have an associated name.
class HasRuleName t where
  ruleName :: t -> RuleInfo ProtoRuleName IntrRuleACInfo

instance HasRuleName ProtoRuleE where
  ruleName = ProtoInfo . L.get rInfo

instance HasRuleName RuleAC where
  ruleName = ruleInfo (ProtoInfo . L.get pracName) IntrInfo . L.get rInfo

instance HasRuleName ProtoRuleAC where
  ruleName = ProtoInfo . L.get (pracName . rInfo)

instance HasRuleName IntrRuleAC where
  ruleName = IntrInfo . L.get rInfo

instance HasRuleName RuleACInst where
  ruleName = ruleInfo (ProtoInfo . L.get praciName) IntrInfo . L.get rInfo


-- Queries
----------

-- | True iff the rule is a destruction rule.
isDestrRule :: HasRuleName r => r -> Bool
isDestrRule ru = case ruleName ru of
  IntrInfo (DestrRule _ _ _ _) -> True
  IntrInfo IEqualityRule   -> True
  _                        -> False

-- | True iff the rule is an iequality rule.
isIEqualityRule :: HasRuleName r => r -> Bool
isIEqualityRule ru = case ruleName ru of
  IntrInfo IEqualityRule -> True
  _                     -> False

-- | True iff the rule is a construction rule.
isConstrRule :: HasRuleName r => r -> Bool
isConstrRule ru = case ruleName ru of
  IntrInfo (ConstrRule _)  -> True
  IntrInfo FreshConstrRule -> True
  IntrInfo PubConstrRule   -> True
  IntrInfo CoerceRule      -> True
  _                        -> False

-- | True iff the rule is a construction rule.
isPubConstrRule :: HasRuleName r => r -> Bool
isPubConstrRule ru = case ruleName ru of
  IntrInfo PubConstrRule   -> True
  _                        -> False
  
-- | True iff the rule is the special fresh rule.
isFreshRule :: HasRuleName r => r -> Bool
isFreshRule = (ProtoInfo FreshRule ==) . ruleName

-- | True iff the rule is the special learn rule.
isIRecvRule :: HasRuleName r => r -> Bool
isIRecvRule = (IntrInfo IRecvRule ==) . ruleName

-- | True iff the rule is the special knows rule.
isISendRule :: HasRuleName r => r -> Bool
isISendRule = (IntrInfo ISendRule ==) . ruleName

-- | True iff the rule is the special coerce rule.
isCoerceRule :: HasRuleName r => r -> Bool
isCoerceRule = (IntrInfo CoerceRule ==) . ruleName

-- | True iff the rule is a destruction rule with constant RHS.
isConstantRule :: HasRuleName r => r -> Bool
isConstantRule ru = case ruleName ru of
  IntrInfo (DestrRule _ _ _ constant) -> constant
  _                                   -> False

-- | True iff the rule is a destruction rule where the RHS is a true subterm of the LHS.
isSubtermRule :: HasRuleName r => r -> Bool
isSubtermRule ru = case ruleName ru of
  IntrInfo (DestrRule _ _ subterm _) -> subterm
  IntrInfo IEqualityRule             -> True
  -- the equality rule is considered a subterm rule, as it has no RHS.
  _                                  -> False

-- | True if the messages in premises, conclusions, actions, and invariants are in normal form
nfRule :: Rule i -> WithMaude Bool
nfRule (Rule _ ps cs as is) = reader $ \hnd ->
    all (nfFactList hnd) [ps, cs, as, is]
  where
    nfFactList hnd xs =
        getAll $ foldMap (foldMap (All . (\t -> nf' t `runReader` hnd))) xs

-- | Normalize all terms in premises, actions and conclusions
normRule :: Rule i -> WithMaude (Rule i)
normRule (Rule rn ps cs as) = reader $ \hnd -> (Rule rn (normFacts ps hnd) (normFacts cs hnd) (normFacts as hnd))
  where
    normFacts fs hnd' = map (\f -> runReader (normFact f) hnd') fs

-- | True iff the rule is an intruder rule
isIntruderRule :: HasRuleName r => r -> Bool
isIntruderRule ru =
    case ruleName ru of IntrInfo _ -> True; ProtoInfo _ -> False

-- | True iff the rule is an intruder rule
isProtocolRule :: HasRuleName r => r -> Bool
isProtocolRule ru =
    case ruleName ru of IntrInfo _ -> False; ProtoInfo _ -> True
    
-- | True if the protocol rule has only the trivial variant.
isTrivialProtoVariantAC :: ProtoRuleAC -> ProtoRuleE -> Bool
isTrivialProtoVariantAC (Rule info ps as cs is) (Rule _ ps' as' cs' is') =
    L.get pracVariants info == Disj [emptySubstVFresh]
    && ps == ps' && as == as' && cs == cs' && is == is'

-- | Returns a rule's name
getRuleName :: HasRuleName (Rule i) => Rule i -> String
getRuleName ru = case ruleName ru of
                      IntrInfo i  -> case i of
                                      ConstrRule x      -> "Constr" ++ (prefixIfReserved ('c' : BC.unpack x))
                                      DestrRule x _ _ _ -> "Destr" ++ (prefixIfReserved ('d' : BC.unpack x))
                                      CoerceRule        -> "Coerce"
                                      IRecvRule         -> "Recv"
                                      ISendRule         -> "Send"
                                      PubConstrRule     -> "PubConstr"
                                      FreshConstrRule   -> "FreshConstr"
                                      IEqualityRule     -> "Equality"
                      ProtoInfo p -> case p of
                                      FreshRule   -> "FreshRule"
                                      StandRule s -> s

-- | Returns a protocol rule's name
getRuleNameDiff :: HasRuleName (Rule i) => Rule i -> String
getRuleNameDiff ru = case ruleName ru of
                      IntrInfo i  -> "Intr" ++ case i of
                                      ConstrRule x      -> "Constr" ++ (prefixIfReserved ('c' : BC.unpack x))
                                      DestrRule x _ _ _ -> "Destr" ++ (prefixIfReserved ('d' : BC.unpack x))
                                      CoerceRule        -> "Coerce"
                                      IRecvRule         -> "Recv"
                                      ISendRule         -> "Send"
                                      PubConstrRule     -> "PubConstr"
                                      FreshConstrRule   -> "FreshConstr"
                                      IEqualityRule     -> "Equality"
                      ProtoInfo p -> "Proto" ++ case p of
                                      FreshRule   -> "FreshRule"
                                      StandRule s -> s

-- | Returns the remaining rule applications within the deconstruction chain if possible, 0 otherwise
getRemainingRuleApplications :: RuleACInst -> Int
getRemainingRuleApplications ru = case ruleName ru of
  IntrInfo (DestrRule _ i _ _) -> i
  _                            -> 0

-- | Sets the remaining rule applications within the deconstruction chain if possible
setRemainingRuleApplications :: RuleACInst -> Int -> RuleACInst
setRemainingRuleApplications (Rule (IntrInfo (DestrRule name _ subterm constant)) prems concs acts invars) i
    = Rule (IntrInfo (DestrRule name i subterm constant)) prems concs acts invars
setRemainingRuleApplications rule _
    = rule

-- | Converts a protocol rule to its "left" variant
getLeftRule :: ProtoRuleE ->  ProtoRuleE
getLeftRule (Rule ri ps cs as is) =
   (Rule ri (map getLeftFact ps) (map getLeftFact cs) (map getLeftFact as) (map getLeftFact is))

-- | Converts a protocol rule to its "right" variant
getRightRule :: ProtoRuleE ->  ProtoRuleE
getRightRule (Rule ri ps cs as is) =
   (Rule ri (map getRightFact ps) (map getRightFact cs) (map getRightFact as) (map getRightFact as))
   
-- | Returns a list of all new variables introduced in this rule instance and the facts they occur in
getNewVariables :: Rule a -> [(LNFact, LVar)]
getNewVariables ru = map (\(x, _, z) -> (x, z)) $ getNewVariablesWithIndex ru

-- | Returns whether a given rule has new variables
containsNewVars :: Rule i -> Bool
containsNewVars ru = not $ S.null newvars
  where 
    newvars   = S.difference (S.difference concvars premvars) invarvars
    premvars  = S.fromList $ concat $ map (getFactVariables . snd) $ enumPrems ru
    concvars  = S.fromList $ concat $ map (getFactVariables . snd) $ enumConcs ru
    invarvars = S.fromList $ concat $ map (getFactVariables . snd) $ enumInvars ru

-- | Returns a list of all new variables introduced in this rule instance and the facts and indices they occur in
getNewVariablesWithIndex :: Rule a -> [(LNFact, ConcIdx, LVar)]
getNewVariablesWithIndex ru = getFacts $ S.toList newvars
  where 
    newvars   = S.difference (S.difference concvars premvars) invarvars
    premvars  = S.fromList $ concat $ map (getFactVariables . snd) $ enumPrems ru
    concvars  = S.fromList $ concat $ map (getFactVariables . snd) $ enumConcs ru
    invarvars = S.fromList $ concat $ map (getFactVariables . snd) $ enumInvars ru
    
    getFacts []     = []
    getFacts (x:xs) = (map (\(idx, f) -> (f, idx, x)) $ filter (\(_, f) -> x `elem` getFactVariables f) $ enumConcs ru) ++ (getFacts xs)

    
-- | Given a rule instance, returns a substitution determining how all new variables have been instantiated.
getSubstitutionsFixingNewVars :: RuleACInst -> RuleAC -> LNSubst
getSubstitutionsFixingNewVars rule orig = Subst $ M.fromList $ concat $ map getSubst newvars
  where
    newvars = getNewVariablesWithIndex orig
    
    getSubst :: (LNFact, ConcIdx, LVar) -> [(LVar, LNTerm)]
    getSubst (fa, cidx, var) = map (\x -> (var, x)) (getMatchingTerm (fa, cidx, var))
    
    getMatchingTerm :: (LNFact, ConcIdx, LVar) -> [LNTerm]
    getMatchingTerm ((Fact fi ts), cidx, var') = rec var' ts matchingTs 
      where
        matchingTs = case matchingConc of
                          Fact fi' ts' -> if fi == fi' then ts' else (error $ "getMatchingTerm: Matching conclusion with different fact: " ++ show (Fact fi ts) ++ " " ++ show cidx ++ " " ++ show var')
        matchingConc = fromMaybe (error $ "getMatchingTerm: No matching conclusion: " ++ show (Fact fi ts) ++ " " ++ show cidx ++ " " ++ show var') (lookupConc cidx rule)
        
        rec :: LVar -> [LNTerm] -> [LNTerm] -> [LNTerm]
        rec _   []     []       = []
        rec var (x:xs) (mt:mts) = case (viewTerm x, viewTerm mt) of
                                       (Lit (Var a), _)            | a == var -> mt:(rec var xs mts)
                                       (FApp f ts' , FApp f' mts') | f == f'  -> (rec var ts' mts')++(rec var xs mts)
                                       (FApp f _   , FApp f' _   ) | f /= f'  -> error "getMatchingTerm: Non-matching function terms!"
                                       (_          , _           )            -> (rec var xs mts)
        rec _   _      _        = error "getMatchingTerm: Different number of terms!"
        

-- Construction
---------------

-- | Returns a multiplication rule instance of the given size.
multRuleInstance :: Int -> RuleAC
multRuleInstance n = (Rule (IntrInfo (ConstrRule $ BC.pack "mult")) (map xifact [1..n]) [prod] [prod] [])
  where
    prod = Fact KUFact [(FAPP (AC Mult) (map xi [1..n]))]
    
    xi :: Int -> LNTerm
    xi k = (LIT $ Var $ LVar "x" LSortMsg (toInteger k))
    
    xifact :: Int -> LNFact
    xifact k = Fact KUFact [(xi k)]

-- | Returns a union rule instance of the given size.
unionRuleInstance :: Int -> RuleAC
unionRuleInstance n = (Rule (IntrInfo (ConstrRule $ BC.pack "union")) (map xifact [1..n]) [prod] [prod] [])
  where
    prod = Fact KUFact [(FAPP (AC Union) (map xi [1..n]))]
    
    xi :: Int -> LNTerm
    xi k = (LIT $ Var $ LVar "x" LSortMsg (toInteger k))
    
    xifact :: Int -> LNFact
    xifact k = Fact KUFact [(xi k)]

type RuleACConstrs = Disj LNSubstVFresh

-- | Compute /some/ rule instance of a rule modulo AC. If the rule is a
-- protocol rule, then the given source and variants also need to be handled.
someRuleACInst :: MonadFresh m
               => RuleAC
               -> m (RuleACInst, Maybe RuleACConstrs)
someRuleACInst =
    fmap extractInsts . rename
  where
    extractInsts (Rule (ProtoInfo i) ps cs as is) =
      ( Rule (ProtoInfo i') ps cs as is
      , Just (L.get pracVariants i)
      )
      where
        i' = ProtoRuleACInstInfo (L.get pracName i) (L.get pracLoopBreakers i)
    extractInsts (Rule (IntrInfo i) ps cs as is) =
      ( Rule (IntrInfo i) ps cs as is, Nothing )

-- | Compute /some/ rule instance of a rule modulo AC. If the rule is a
-- protocol rule, then the given source and variants also need to be handled.
someRuleACInstAvoiding :: HasFrees t 
               => RuleAC
               -> t
               -> (RuleACInst, Maybe RuleACConstrs)
someRuleACInstAvoiding r s =
    renameAvoiding (extractInsts r) s
  where
    extractInsts (Rule (ProtoInfo i) ps cs as is) =
      ( Rule (ProtoInfo i') ps cs as is
      , Just (L.get pracVariants i)
      )
      where
        i' = ProtoRuleACInstInfo (L.get pracName i) (L.get pracLoopBreakers i)
    extractInsts (Rule (IntrInfo i) ps cs as is) =
      ( Rule (IntrInfo i) ps cs as is, Nothing )

-- | Compute /some/ rule instance of a rule modulo AC. If the rule is a
-- protocol rule, then the given source and variants also need to be handled.
someRuleACInstFixing :: MonadFresh m
               => RuleAC
               -> LNSubst
               -> m (RuleACInst, Maybe RuleACConstrs)
someRuleACInstFixing r subst =
    renameIgnoring (varsRange subst) (extractInsts r)
  where
    extractInsts (Rule (ProtoInfo i) ps cs as is) =
      ( apply subst (Rule (ProtoInfo i') ps cs as is)
      , Just (L.get pracVariants i)
      )
      where
        i' = ProtoRuleACInstInfo (L.get pracName i) (L.get pracLoopBreakers i)
    extractInsts (Rule (IntrInfo i) ps cs as is) =
      ( apply subst (Rule (IntrInfo i) ps cs as is), Nothing )

      
-- | Compute /some/ rule instance of a rule modulo AC. If the rule is a
-- protocol rule, then the given source and variants also need to be handled.
someRuleACInstAvoidingFixing :: HasFrees t 
               => RuleAC
               -> t
               -> LNSubst
               -> (RuleACInst, Maybe RuleACConstrs)
someRuleACInstAvoidingFixing r s subst =
    renameAvoidingIgnoring (extractInsts r) s (varsRange subst)
  where
    extractInsts (Rule (ProtoInfo i) ps cs as is) =
      ( apply subst (Rule (ProtoInfo i') ps cs as is)
      , Just (L.get pracVariants i)
      )
      where
        i' = ProtoRuleACInstInfo (L.get pracName i) (L.get pracLoopBreakers i)
    extractInsts (Rule (IntrInfo i) ps cs as is) =
      ( apply subst (Rule (IntrInfo i) ps cs as is), Nothing )

      
-- | Add the diff label to a rule
addDiffLabel :: Rule a -> String -> Rule a
addDiffLabel (Rule info prems concs acts invars) name 
    = Rule info prems concs (acts ++ [Fact {factTag = ProtoFact Linear name 0, factTerms = []}]) invars

-- | Remove the diff label from a rule
removeDiffLabel :: Rule a -> String -> Rule a
removeDiffLabel (Rule info prems concs acts invars) name = Rule info prems concs (filter isNotDiffAnnotation acts) invars
  where
    isNotDiffAnnotation fa = (fa /= Fact {factTag = ProtoFact Linear name 0, factTerms = []})

-- Unification
--------------

-- | Unify a list of @RuleACInst@ equalities.
unifyRuleACInstEqs :: [Equal RuleACInst] -> WithMaude [LNSubstVFresh]
unifyRuleACInstEqs eqs
  | all unifiable eqs = unifyLNFactEqs $ concatMap ruleEqs eqs
  | otherwise         = return []
  where
    unifiable (Equal ru1 ru2) =
         L.get rInfo ru1            == L.get rInfo ru2
      && length (L.get rPrems ru1) == length (L.get rPrems ru2)
      && length (L.get rConcs ru1) == length (L.get rConcs ru2)
      && length (L.get rInvars ru1) == length (L.get rInvars ru2)

    ruleEqs (Equal ru1 ru2) =
        zipWith Equal (L.get rPrems ru1) (L.get rPrems ru2) ++
        zipWith Equal (L.get rConcs ru1) (L.get rConcs ru2) ++
        zipWith Equal (L.get rInvars ru1) (L.get rInvars ru2)

-- | Are these two rule instances unifiable.
unifiableRuleACInsts :: RuleACInst -> RuleACInst -> WithMaude Bool
unifiableRuleACInsts ru1 ru2 =
    (not . null) <$> unifyRuleACInstEqs [Equal ru1 ru2]


------------------------------------------------------------------------------
-- Fact analysis
------------------------------------------------------------------------------

-- | Globally unique facts.
--
-- A rule instance removes a fact fa if fa is in the rule's premise but not
-- in the rule's conclusion.
--
-- A fact symbol fa is globally fresh with respect to a dependency graph if
-- there are no two rule instances that remove the same fact built from fa.
--
-- We are looking for sufficient criterion to prove that a fact symbol is
-- globally fresh.
--
-- The Fr symbol is globally fresh by construction.
--
-- We have to track every creation of a globally fresh fact to a Fr fact.
--
-- (And show that the equality of of the created fact implies the equality of
-- the corresponding fresh facts. Ignore this for now by assuming that no
-- duplication happens.)
--
-- (fa(x1), fr(y1)), (fa(x2), fr(y2)) : x2 = x1 ==> y1 == y2
--
-- And ensure that every duplication is non-unifiable.
--
-- A Fr fact is described
--
-- We track which symbols are not globally fresh.
--
-- All persistent facts are not globally fresh.
--
-- Adding a rule ru.
--   All fact symbols that occur twice in the conclusion
--
-- For simplicity: globally fresh fact symbols occur at most once in premise
--   and conclusion of a rule.
--
-- A fact is removed by a rule if it occurs in the rules premise
--   1. but doesn't occur in the rule's conclusion
--   2. or does occur but non-unifiable.
--
-- We want a sufficient criterion to prove that a fact is globally unique.
--
--

------------------------------------------------------------------------------
-- Pretty-Printing
------------------------------------------------------------------------------

-- | Prefix the name if it is equal to a reserved name.
--
-- NOTE: We maintain the invariant that a theory does not contain standard
-- rules with a reserved name. This is a last ressort. The pretty-printed
-- theory can then not be parsed anymore.
prefixIfReserved :: String -> String
prefixIfReserved n
  | n `elem` reservedRuleNames = "_" ++ n
  | "_" `isPrefixOf` n         = "_" ++ n
  | otherwise                  = n

-- | List of all reserved rule names.
reservedRuleNames :: [String]
reservedRuleNames = ["Fresh", "irecv", "isend", "coerce", "fresh", "pub", "iequality"]

prettyProtoRuleName :: Document d => ProtoRuleName -> d
prettyProtoRuleName rn = text $ case rn of
    FreshRule   -> "Fresh"
    StandRule n -> prefixIfReserved n

prettyRuleName :: (HighlightDocument d, HasRuleName (Rule i)) => Rule i -> d
prettyRuleName = ruleInfo prettyProtoRuleName prettyIntrRuleACInfo . ruleName

-- | Pretty print the rule name such that it can be used as a case name
showRuleCaseName :: HasRuleName (Rule i) => Rule i -> String
showRuleCaseName =
    render . ruleInfo prettyProtoRuleName prettyIntrRuleACInfo . ruleName

prettyIntrRuleACInfo :: Document d => IntrRuleACInfo -> d
prettyIntrRuleACInfo rn = text $ case rn of
    IRecvRule            -> "irecv"
    ISendRule            -> "isend"
    CoerceRule           -> "coerce"
    FreshConstrRule      -> "fresh"
    PubConstrRule        -> "pub"
    IEqualityRule        -> "iequality"
    ConstrRule name      -> prefixIfReserved ('c' : BC.unpack name)
    DestrRule name _ _ _ -> prefixIfReserved ('d' : BC.unpack name)
--     DestrRule name i -> prefixIfReserved ('d' : BC.unpack name ++ "_" ++ show i)

prettyNamedRule :: (HighlightDocument d, HasRuleName (Rule i))
                => d           -- ^ Prefix.
                -> (i -> d)    -- ^ Rule info pretty printing.
                -> Rule i -> d
prettyNamedRule prefix ppInfo ru =
    prefix <-> prettyRuleName ru <> colon $-$
    nest 2 (sep [ nest 1 $ ppFactsList rPrems
                , if null acts
                    then operator_ "-->"
                    else fsep [operator_ "--[", ppFacts' acts, operator_ "]->"]
                , nest 1 $ ppFactsList rConcs
                , nest 1 $ ppInvarsList rInvars]) $-$
    nest 2 (ppInfo $ L.get rInfo ru)
  where
    acts             = filter isNotDiffAnnotation (L.get rActs ru)
    ppList pp        = fsep . punctuate comma . map pp
    ppFacts' list    = ppList prettyLNFact list
    ppFacts proj     = ppList prettyLNFact $ L.get proj ru
    ppFactsList proj = fsep [operator_ "[", ppFacts proj, operator_ "]"]
    ppInvarsList proj = fsep [operator_ "(preserving ", ppFacts proj, operator_ ")"]
    isNotDiffAnnotation fa = (fa /= Fact {factTag = ProtoFact Linear ("Diff" ++ getRuleNameDiff ru) 0, factTerms = []})

prettyProtoRuleACInfo :: HighlightDocument d => ProtoRuleACInfo -> d
prettyProtoRuleACInfo i =
    (ppVariants $ L.get pracVariants i) $-$
    prettyLoopBreakers i
  where
    ppVariants (Disj [subst]) | subst == emptySubstVFresh = emptyDoc
    ppVariants substs = kwVariantsModulo "AC" $-$ prettyDisjLNSubstsVFresh substs

prettyLoopBreakers :: HighlightDocument d => ProtoRuleACInfo -> d
prettyLoopBreakers i = case breakers of
    []  -> emptyDoc
    [_] -> lineComment_ $ "loop breaker: "  ++ show breakers
    _   -> lineComment_ $ "loop breakers: " ++ show breakers
  where
    breakers = getPremIdx <$> L.get pracLoopBreakers i

prettyProtoRuleE :: HighlightDocument d => ProtoRuleE -> d
prettyProtoRuleE = prettyNamedRule (kwRuleModulo "E") (const emptyDoc)

prettyRuleAC :: HighlightDocument d => RuleAC -> d
prettyRuleAC =
    prettyNamedRule (kwRuleModulo "AC")
        (ruleInfo prettyProtoRuleACInfo (const emptyDoc))

prettyIntrRuleAC :: HighlightDocument d => IntrRuleAC -> d
prettyIntrRuleAC = prettyNamedRule (kwRuleModulo "AC") (const emptyDoc)

prettyProtoRuleAC :: HighlightDocument d => ProtoRuleAC -> d
prettyProtoRuleAC = prettyNamedRule (kwRuleModulo "AC") prettyProtoRuleACInfo

prettyRuleACInst :: HighlightDocument d => RuleACInst -> d
prettyRuleACInst = prettyNamedRule (kwInstanceModulo "AC") (const emptyDoc)
