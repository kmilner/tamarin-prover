{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt, Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Support for reasoning with and about disjunctions of substitutions.
module Theory.Tools.EquationStore (
  -- * Equations
    SplitId(..)

  , EqStore(..)
  , emptyEqStore
  , eqsSubst
  , eqsConj

  -- ** Equalitiy constraint conjunctions
  , falseEqConstrConj

  -- ** Queries
  , eqsIsFalse


  -- ** Adding equalities
  , addEqs
  , addRuleVariants
  , addDisj

  -- ** Case splitting
  , performSplit
  , dropNameHintsBound

  , splits
  , splitSize
  , splitExists

  -- * Simplification
  , simp
  , simpDisjunction

  -- ** Pretty printing
  , prettyEqStore
) where

import           GHC.Generics          (Generic)
import           Logic.Connectives
import           Term.Unification
import           Theory.Text.Pretty

import           Control.Monad.Fresh
import           Control.Monad.Bind
import           Control.Monad.Reader
import           Extension.Prelude
import           Utils.Misc

import           Debug.Trace.Ignore

-- TAM_HS_TRACE_SIMP: reusable env-var-gated tracing for the eq-store
-- simplification pipeline.  Imports the REAL Debug.Trace + System.IO.Unsafe
-- (so we can read the env var without threading IO through the monad
-- transformer stack) and exposes `traceSimp`.  Use sparingly — calls
-- to `traceSimp` short-circuit to id when the env var is unset, so they
-- have negligible runtime cost.
import qualified Debug.Trace
import qualified System.Environment
import qualified System.IO.Unsafe

import           Control.Basics
import           Control.DeepSeq
import           Control.Monad.State   hiding (get, modify, put)
import qualified Control.Monad.State   as MS

import           Data.Binary
import qualified Data.Foldable         as F
import           Data.List          (delete,find,intersect,intersperse,nub,(\\))
import           Data.Maybe
import qualified Data.Set              as S
import           Extension.Data.Label  hiding (for, get)
import qualified Extension.Data.Label  as L
-- import           Extension.Data.Monoid

------------------------------------------------------------------------------
-- Equation Store                                                --
------------------------------------------------------------------------------

-- | Index of disjunction in equation store
newtype SplitId = SplitId { unSplitId :: Integer }
  deriving( Eq, Ord, Show, Enum, Binary, NFData )

instance HasFrees SplitId where
    foldFrees    _   = const mempty
    foldFreesOcc _ _ = const mempty
    mapFrees     _   = pure

-- FIXME: Make comment parse.
--
-- The semantics of an equation store
-- > EqStore sigma_free
-- >         [ [sigma_i1,..,sigma_ik_i] | i <- [1..l] ]
-- where sigma_free = {t1/x1, .., tk/xk} is
-- >    (x1 = t1 /\ .. /\ xk = tk)
-- > /\_{i in [1..l]}
-- >    ([|sigma_i1|] \/ .. \/ [|sigma_ik_1|] \/ [|mtinfo_i|]
-- where @[|{t_1/x_1,..,t_l/x_l}|] = EX vars(t1,..,tl). x_1 = t1 /\ .. /\ x_l = t_l@.
-- Note that the 'LVar's in the range of a substitution are interpreted as
-- fresh variables, i.e., different by construction from the x_i which are
-- free variables.
--
-- The variables in the domain of the substitutions sigma_ij and all
-- variables in sigma_free are free (usually globally existentially quantified).
-- We use Conj [] as a normal form to denote True and Conj [Disj []]
-- as a normal form to denote False.
-- We say a variable @x@ is constrained by a disjunction if there is a substition
-- @s@ in the disjunction with @x `elem` dom s@.
data EqStore = EqStore {
      _eqsSubst       :: LNSubst
    , _eqsConj        :: Conj (SplitId, S.Set LNSubstVFresh)
    , _eqsNextSplitId :: SplitId
    }
  deriving( Eq, Ord, Generic )

instance NFData EqStore
instance Binary EqStore

$(mkLabels [''EqStore])

-- | @emptyEqStore@ is the empty equation store.
emptyEqStore :: EqStore
emptyEqStore = EqStore emptySubst (Conj []) (SplitId 0)

-- | @True@ iff the 'EqStore' is contradictory.
eqsIsFalse :: EqStore -> Bool
eqsIsFalse = any ((S.empty == ) . snd) . getConj . L.get eqsConj

-- | The false conjunction. It is always identified with split number -1.
falseEqConstrConj :: Conj (SplitId, S.Set LNSubstVFresh)
falseEqConstrConj = Conj [ (SplitId (-1), S.empty) ]

dropNameHintsBound :: EqStore -> EqStore
dropNameHintsBound = modify eqsConj (Conj . map (second (S.map dropNameHintsLNSubstVFresh)) . getConj)

dropNameHintsLNSubstVFresh :: LNSubstVFresh -> LNSubstVFresh
dropNameHintsLNSubstVFresh subst =
    substFromListVFresh $ zip (map fst slist)
                              ((`evalFresh` nothingUsed) . (`evalBindT` noBindings) $ renameDropNamehint (map snd slist))
  where slist = substToListVFresh subst

-- Instances
------------

instance Apply LNSubst SplitId where
    apply _ = id

instance HasFrees EqStore where
    {-# INLINABLE foldFrees #-}
    foldFrees f (EqStore subst substs nextSplitId) =
        foldFrees f subst <> foldFrees f substs <> foldFrees f nextSplitId
    foldFreesOcc  _ _ = const mempty
    {-# INLINABLE mapFrees #-}
    mapFrees f (EqStore subst substs nextSplitId) =
        EqStore <$> mapFrees f subst
                <*> mapFrees f substs
                <*> mapFrees f nextSplitId


instance Apply LNSubst EqStore where
    apply subst (EqStore a b c) = EqStore (compose subst a) (fmap (fmap $ S.map $ flip composeVFresh subst) b) (apply subst c) 


-- Equation Store
----------------------------------------------------------------------

-- | We use the empty set (disjunction) to denote false.
falseDisj :: S.Set LNSubstVFresh
falseDisj = S.empty


-- Dealing with equations
----------------------------------------------------------------------

-- | Returns the list of all @SplitId@s valid for the given equation store
-- sorted by the size of the disjunctions.
splits :: EqStore -> [SplitId]
splits eqs = map fst $ nub $ sortOn snd
    [ (idx, S.size conj) | (idx, conj) <- getConj $ L.get eqsConj eqs ]

-- | Returns 'True' if the 'SplitId' is valid.
splitExists :: EqStore -> SplitId -> Bool
splitExists eqs = isJust . splitSize eqs

-- | Returns the number of cases for a given 'SplitId'.
splitSize :: EqStore -> SplitId -> Maybe Int
splitSize eqs sid =
    (S.size . snd) <$> (find ((sid ==) . fst) $ getConj $ L.get eqsConj $ eqs)

-- | Add a disjunction to the equation store at the beginning
addDisj :: EqStore -> (S.Set LNSubstVFresh) -> (EqStore, SplitId)
addDisj eqStore disj =
    (   modify eqsConj ((Conj [(sid, disj)]) `mappend`)
      $ modify eqsNextSplitId succ
      $ eqStore
    , sid
    )
  where
    sid = L.get eqsNextSplitId eqStore

-- | @performSplit eqs i@ performs a case-split on the first disjunction
-- with the given 'SplitId'.
performSplit :: EqStore -> SplitId -> Maybe [EqStore]
performSplit eqStore idx =
    case break ((idx ==) . fst) (getConj $ L.get eqsConj eqStore) of
        (_, [])                   -> Nothing
        (before, (_, disj):after) ->
            let substs   = orderedSubsts disj
                tracedSubsts
                    | dbgPerformSplit =
                        Debug.Trace.trace
                            ("[hs-perform_split] split_id=" ++ show idx
                             ++ ", " ++ show (length substs) ++ " substs (ordered):\n"
                             ++ "  eqsSubst: " ++ show (substToList $ L.get eqsSubst eqStore) ++ "\n"
                             ++ "  all conj sids: " ++ show (map fst (getConj $ L.get eqsConj eqStore)) ++ "\n"
                             ++ concatMap (\(i, s) -> "  case_" ++ show i ++ ": "
                                                      ++ show (substToListVFresh s) ++ "\n")
                                          (zip [(1::Int)..] substs)) substs
                    | otherwise = substs
            in Just $ mkNewEqStore before after <$> tracedSubsts
  where
    -- The disjunction is stored as a @Set LNSubstVFresh@, so @S.toList@ would
    -- enumerate the cases in the derived 'Ord' order of the substitutions. That
    -- order compares the substitutions' range terms, which contain the fresh
    -- witness variables introduced during back-conversion from Maude; their
    -- indices are an artifact of the fresh-variable allocation counter and are
    -- not in any canonical form. As a result the case order (and hence the
    -- positional @split_case_i@ labels in the emitted proof) could depend on the
    -- allocation history rather than on the structure of the unifiers, so a
    -- saved proof would fail to re-validate under a checker that allocates
    -- in a different order (because of threading, etc). Sorting the cases renumbers
    -- witnesses in a canonical order so that it's reproducible across runs.
    orderedSubsts = sortOnMemo dropNameHintsLNSubstVFresh . S.toList

    mkNewEqStore before after subst =
        fst $ addDisj (set eqsConj (Conj (before ++ after)) eqStore)
                      (S.singleton subst)

-- | TAM_HS_DBG_PERFORM_SPLIT: log perform_split's S.toList output (the
-- post-sort order in which case_1, case_2, ... are produced).  Mirrors
-- Rust's TAM_DBG_PERFORM_SPLIT for diffing variant-allocation order.
dbgPerformSplit :: Bool
dbgPerformSplit = System.IO.Unsafe.unsafePerformIO $
    maybe False (== "1") <$> System.Environment.lookupEnv "TAM_HS_DBG_PERFORM_SPLIT"
{-# NOINLINE dbgPerformSplit #-}

-- | Add a list of term equalities to the equation store. Returns the split
-- identifier of the disjunction in resulting equation store.
addEqs :: MonadFresh m
       => MaudeHandle -> [Equal LNTerm] -> EqStore -> m (EqStore, Maybe SplitId)
addEqs hnd eqs0 eqStore =
    (if hsTraceSBind then trace ("[HS_addEqs] eqs0=" ++ show eqs0) else id) $
    case unifyLNTermFactored eqs `runReader` hnd of
        (_, []) ->
            return (set eqsConj falseEqConstrConj eqStore, Nothing)
        (subst, [substFresh]) | substFresh == emptySubstVFresh ->
            (if hsTraceSBind then trace ("[HS_addEqs_subst] subst=" ++ show (substToList subst)) else id) $
            return (applyEqStore hnd subst eqStore, Nothing)
        (subst, substs) -> do
            let (eqStore', sid) = addDisj (applyEqStore hnd subst eqStore)
                                          (S.fromList substs)
            return (eqStore', Just sid)
            {-
            case splitStrat of
                SplitLater ->
                    return [ addDisj (applyEqStore hnd subst eqStore) (S.fromList substs) ]
                SplitNow ->
                    addEqsAC (modify eqsSubst (compose subst) eqStore)
                        <$> simpDisjunction hnd (const False) (Disj substs)
            -}
  where
    eqs = apply (L.get eqsSubst eqStore) $ trace (unlines ["addEqs: ", show eqs0]) $ eqs0
    {-
    addEqsAC eqSt (sfree, Nothing)   = [ applyEqStore hnd sfree eqSt ]
    addEqsAC eqSt (sfree, Just disj) =
      fromMaybe (error "addEqsSplit: impossible, splitAtPos failed")
                (splitAtPos (applyEqStore hnd sfree (addDisj eqSt (S.fromList disj))) 0)
-}

-- TAM_HS_TRACE_S_BIND flag.
hsTraceSBind :: Bool
hsTraceSBind = System.IO.Unsafe.unsafePerformIO $
    maybe False (== "1") <$> System.Environment.lookupEnv "TAM_HS_TRACE_S_BIND"
{-# NOINLINE hsTraceSBind #-}

-- | Apply a substitution to an equation store and bring resulting equations into
--   normal form again by using unification.
--
-- TAM_HS_DBG_APPLY_EQ_STORE=1 dumps every call's asubst, eqsSubst, IN
-- disjs, per-variant applyBound input/output, and OUT disjs.  Pair with
-- Rust's TAM_RS_DBG_APPLY_EQ_STORE for HS↔Rust diffing of variant flow
-- (see [[project-apply-eq-store-divergence]]).
--
-- TAM_HS_DBG_APPLY_EQ_STORE_FILTER=substantive limits dump to calls with
-- non-empty conj (skips trivial composition-only calls).
applyEqStore :: MaudeHandle -> LNSubst -> EqStore -> EqStore
applyEqStore hnd asubst eqStore
    | dom asubst `intersect` varsRange asubst /= [] || trace (show ("applyEqStore", asubst, eqStore)) False
    = error $ "applyEqStore: dom and vrange not disjoint for `"++show asubst++"'"
    | otherwise
    = dbgWrap $ modify eqsConj (fmap (second (S.fromList . concatMap applyBoundDbg . S.toList))) $
          set eqsSubst newsubst eqStore
  where
    newsubst = asubst `compose` L.get eqsSubst eqStore
    dbgEnabled = System.IO.Unsafe.unsafePerformIO $
                 fmap (== Just "1") $ System.Environment.lookupEnv "TAM_HS_DBG_APPLY_EQ_STORE"
    dbgFilterSubstantive = System.IO.Unsafe.unsafePerformIO $
                 fmap (== Just "substantive") $ System.Environment.lookupEnv "TAM_HS_DBG_APPLY_EQ_STORE_FILTER"
    -- Tick every call (even empty conj) so call counts can be compared
    -- against Rust's TAM_RS_DBG_APPLY_EQ_STORE.  Substantive calls
    -- (non-empty conj) also dump per-variant detail.
    dbgWrap r = if dbgEnabled
      then System.IO.Unsafe.unsafePerformIO $ do
        let inDisjs = filter (not . S.null . snd) (getConj $ L.get eqsConj eqStore)
        let substantive = not (null inDisjs)
        -- Always emit a tick line for call counting.
        if substantive || not dbgFilterSubstantive
          then putStrLn $ "[hs-aes-tick] conj=" ++ show (length (getConj $ L.get eqsConj eqStore))
                       ++ " substantive=" ++ show substantive
          else return ()
        if substantive
          then do
            putStrLn $ "[hs-aes] === call ==="
            putStrLn $ "[hs-aes] asubst = " ++ show (substToList asubst)
            putStrLn $ "[hs-aes] eqsSubst = " ++ show (substToList (L.get eqsSubst eqStore))
            mapM_ (\(i, (sid, ss)) -> do
              putStrLn $ "[hs-aes] IN  disj[" ++ show i ++ "] sid=" ++ show sid
                                              ++ " (" ++ show (S.size ss) ++ " substs)"
              mapM_ (\(j, s) -> putStrLn $ "  in[" ++ show j ++ "]: " ++ show (substToListVFresh s))
                    (zip [0::Int ..] (S.toList ss)))
              (zip [0::Int ..] inDisjs)
            mapM_ (\(i, (sid, ss)) -> do
              putStrLn $ "[hs-aes] OUT disj[" ++ show i ++ "] sid=" ++ show sid
                                              ++ " (" ++ show (S.size ss) ++ " substs)"
              mapM_ (\(j, s) -> putStrLn $ "  out[" ++ show j ++ "]: " ++ show (substToListVFresh s))
                    (zip [0::Int ..] (S.toList ss)))
              (zip [0::Int ..] (filter (not . S.null . snd) (getConj $ L.get eqsConj r)))
            return r
          else return r
      else r
    applyBoundDbg s =
      let res = applyBound s in
      if dbgEnabled then System.IO.Unsafe.unsafePerformIO $ do
        putStrLn $ "[hs-aes-applyBound] IN  : " ++ show (substToListVFresh s)
        mapM_ (\(j, o) -> putStrLn $ "  OUT[" ++ show j ++ "]: " ++ show (substToListVFresh o))
              (zip [0::Int ..] res)
        return res
      else res
    -- TAM_HS_DBG_AES_DETAIL=1: dump per-variant slist, avoid set,
    -- renamed RHS, and unifier outputs.  Pair with Rust's
    -- TAM_RS_DBG_AES_DETAIL for HS↔Rust witness-allocation diffing.
    detailDbg = System.IO.Unsafe.unsafePerformIO $
                fmap (== Just "1") $ System.Environment.lookupEnv "TAM_HS_DBG_AES_DETAIL"
    applyBound s =
        let slist = substToListVFresh s
            avoidSet = domVFresh s ++ varsRange newsubst
            ran = renameAvoiding (map snd slist) avoidSet
            eqs = [ Equal (apply newsubst (varTerm lv)) t
                  | (lv, t) <- zip (map fst slist) ran ]
            unifiers = (`runReader` hnd) $ unifyLNTerm eqs
            restricted = map (restrictVFresh (varsRange newsubst ++ domVFresh s)) unifiers
        in if detailDbg
           then System.IO.Unsafe.unsafePerformIO $ do
                  putStrLn $ "[hs-aes-detail] slist=" ++ show slist
                  putStrLn $ "[hs-aes-detail]   avoidSet=" ++ show avoidSet
                  putStrLn $ "[hs-aes-detail]   ran (renamed values)=" ++ show ran
                  putStrLn $ "[hs-aes-detail]   eqs=" ++ show [(l, r) | Equal l r <- eqs]
                  putStrLn $ "[hs-aes-detail]   #unifiers=" ++ show (length unifiers)
                  mapM_ (\(j, u) -> putStrLn $ "[hs-aes-detail]   unifier[" ++ show j ++
                                    "]=" ++ show (substToListVFresh u))
                        (zip [0::Int ..] unifiers)
                  return restricted
           else restricted

{- NOTES for @applyEqStore tau@ to a fresh substitution sigma:
[ FIXME: extend explanation to multiple unifiers ]
Let dom(sigma) = x1,..,xk, vrange(sigma) = y1, .. yl, vrange(tau) = z1,..,zn
Fresh substitution denotes formula
  exists #y1, .., #yl. x1 = t1 /\ .. /\ xk = tk
for variables #yi that do not clash with xi and zi [renameAwayFrom]
and with vars(ti) `subsetOf` [#y1, .. #yl].
We apply tau with vrange(tau) = z1,..,zn to the formula to obtain
  exists ##y1, .., ##yl. tau(x1) = t1 /\ .. /\ tau(xk) = tk
unification then yields a lemma
  forall xi zi #yi.
    tau(x1) = t1 /\ .. /\ tau(xk) = tk
    <-> exists vars(s1,..sm). x1 = .. /\ z1 = .. /\ #y1 = ..
So we have
  exists #y1, .., #yl.
    exists vars(s1,..sm). x1 = .. /\ z1 = .. /\ #y1 = ..
<=>
  exists vars(s1,..sm). x1 = .. /\ z1 = ..
      /\  (exists #y1, .., #yl. #y1 = ..)
<=> [restric]
  exists vars(s1,..sm). x1 = .. /\ z1 = .. /\ True
-}

-- | Add the given rule variants.
addRuleVariants :: Disj LNSubstVFresh -> EqStore -> (EqStore, SplitId)
addRuleVariants (Disj substs) eqStore
    | dom freeSubst `intersect` concatMap domVFresh substs /= []
    = error $ "addRuleVariants: Nonempty intersection between domain of variants and free substitution. "
              ++"This case has not been implemented, add rule variants earlier."
    | otherwise = addDisj eqStore (S.fromList substs)
  where
    freeSubst = L.get eqsSubst eqStore


{-
-- | Return the set of variables that is constrained by disjunction at give position.
constrainedVarsPos :: EqStore -> Int -> [LVar]
constrainedVarsPos eqStore k
    | k < length conj = frees (conj!!k)
    | otherwise       = []
  where
    conj = getConj . L.get eqsConj $ eqStore
-}

-- Simplifying disjunctions
----------------------------------------------------------------------

-- | Simplify given disjunction via EqStore simplification. Obtains fresh
--   names for variables from the underlying 'MonadFresh'.
simpDisjunction :: MonadFresh m
                => MaudeHandle
                -> (LNSubst -> LNSubstVFresh -> Bool)
                -> Disj LNSubstVFresh
                -> m (LNSubst, Maybe [LNSubstVFresh])
simpDisjunction hnd isContr disj0 = do
    eqStore' <- simp hnd isContr eqStore
    return (L.get eqsSubst eqStore', wrap $ L.get eqsConj eqStore')
  where
    eqStore = fst $ addDisj emptyEqStore (S.fromList $ getDisj $ disj0)
    wrap (Conj [])          = Nothing
    wrap (Conj [(_, disj)]) = Just $ S.toList disj
    wrap conj               =
        error ("simplifyDisjunction: imposible, unexpected conjunction `"
               ++ show conj ++ "'")


-- Simplification
----------------------------------------------------------------------

------------------------------------------------------------------------------
-- TAM_HS_TRACE_SIMP — reusable env-var-gated tracing for `simp`.
--
-- Set `TAM_HS_TRACE_SIMP=1` to dump:
--   * the eq-store conj (with full sort info) on entry of every `simp` call,
--   * which passes inside `simp1` fired and the post-pass conj after each one,
--   * the final conj on `simp` exit.
--
-- Designed to stay zero-cost when the env var is unset — `tamHsTraceSimpOn`
-- is evaluated via `unsafePerformIO . lookupEnv` at every callsite but GHC's
-- per-process IORef cache and constant-folded comparisons keep the overhead
-- minimal in practice.
------------------------------------------------------------------------------

tamHsTraceSimpOn :: Bool
tamHsTraceSimpOn = System.IO.Unsafe.unsafePerformIO $
    maybe False (== "1") <$> System.Environment.lookupEnv "TAM_HS_TRACE_SIMP"
{-# NOINLINE tamHsTraceSimpOn #-}

-- | `traceSimp tag x` returns `x`; when `TAM_HS_TRACE_SIMP=1`, also emits
-- `[HS-SIMP] <tag>` to stderr.  Use the `Show`-able payload variant
-- (`traceSimpShow`) when you want to include the value being inspected.
traceSimp :: String -> a -> a
traceSimp tag x =
    if tamHsTraceSimpOn
        then Debug.Trace.trace ("[HS-SIMP] " ++ tag) x
        else x

traceSimpShow :: Show s => String -> s -> a -> a
traceSimpShow tag payload x =
    if tamHsTraceSimpOn
        then Debug.Trace.trace ("[HS-SIMP] " ++ tag ++ " " ++ show payload) x
        else x

-- | Render an EqStore's conj compactly for diagnostic output: per-disj id
-- followed by its substs with explicit sort annotations on every range var.
renderEqStoreConj :: EqStore -> String
renderEqStoreConj eqStore =
    "conj=" ++ show (length (getConj (L.get eqsConj eqStore))) ++
    " " ++ concatMap renderDisj (getConj (L.get eqsConj eqStore))
  where
    renderDisj (idx, substs) =
        "[" ++ show (unSplitId idx) ++ ":" ++
        show (length (S.toList substs)) ++ " " ++
        intercalate " | " (map renderSubst (S.toList substs)) ++ "] "
    renderSubst s =
        "{" ++ intercalate ", " (map renderMapping (substToListVFresh s)) ++ "}"
    renderMapping (v, t) =
        show v ++ ":" ++ show (lvarSort v) ++ "→" ++
        show t ++ rangeSorts t
    rangeSorts t =
        let rangeVars = [ lv | lv <- frees t ]
        in if null rangeVars
            then ""
            else " {sorts: " ++
                 intercalate "," (map (\lv -> show lv ++ ":" ++ show (lvarSort lv)) rangeVars) ++
                 "}"
    intercalate sep = foldr (\a acc -> if null acc then a else a ++ sep ++ acc) ""

-- | @simp eqStore@ simplifies the equation store.
simp :: MonadFresh m => MaudeHandle -> (LNSubst -> LNSubstVFresh -> Bool) -> EqStore -> m EqStore
simp hnd isContr eqStore =
    traceSimp ("ENTER " ++ renderEqStoreConj eqStore) $ do
        out <- execStateT (whileTrue (simp1 hnd isContr))
                          (trace (show ("eqStore", eqStore)) eqStore)
        return $! traceSimp ("EXIT  " ++ renderEqStoreConj out) out


-- | @simp1@ tries to execute one simplification step
--   for the equation store. It returns @True@ if
--   the equation store was modified.
simp1 :: MonadFresh m => MaudeHandle -> (LNSubst -> LNSubstVFresh -> Bool) -> StateT EqStore m Bool
simp1 hnd isContr = do
    eqs <- MS.get
    if eqsIsFalse eqs
        then return False
        else do
          b1 <- simpMinimize (isContr (L.get eqsSubst eqs))
          dumpPostPass "simpMinimize" b1
          b2 <- simpRemoveRenamings
          dumpPostPass "simpRemoveRenamings" b2
          b3 <- simpEmptyDisj
          dumpPostPass "simpEmptyDisj" b3
          b4 <- foreachDisj hnd simpSingleton
          dumpPostPass "simpSingleton" b4
          b5 <- foreachDisj hnd simpAbstractSortedVar
          dumpPostPass "simpAbstractSortedVar" b5
          b6 <- foreachDisj hnd simpIdentify
          dumpPostPass "simpIdentify" b6
          b7 <- foreachDisj hnd simpAbstractFun
          dumpPostPass "simpAbstractFun" b7
          b8 <- foreachDisj hnd simpAbstractName
          dumpPostPass "simpAbstractName" b8
          (trace (show ("simp:", [b1, b2, b3, b4, b5, b6, b7, b8]))) $
              return $ (or [b1, b2, b3, b4, b5, b6, b7, b8])
  where
    dumpPostPass passName fired =
        when (fired && tamHsTraceSimpOn) $ do
            postEqs <- MS.get
            Debug.Trace.traceM ("[HS-SIMP] after " ++ passName ++
                                " " ++ renderEqStoreConj postEqs)


-- | Remove variable renamings in fresh substitutions.
simpRemoveRenamings :: MonadFresh m => StateT EqStore m Bool
simpRemoveRenamings = do
    conj <- gets (L.get eqsConj)
    if F.any (S.foldl' (\b subst -> b || domVFresh subst /= domVFresh (removeRenamings subst)) False . snd) conj
      then modM eqsConj (fmap (second $ S.map removeRenamings)) >> return True
      else return False


-- | If empty disjunction is found, the whole conjunct
--   can be simplified to False.
simpEmptyDisj :: MonadFresh m => StateT EqStore m Bool
simpEmptyDisj = do
    conj <- getM eqsConj
    if (F.any ((== falseDisj) . snd) conj && conj /= falseEqConstrConj)
      then eqsConj =: falseEqConstrConj >> return True
      else return False


-- | If there is a singleton disjunction, it can be
--   composed with the free substitution.
simpSingleton :: MonadFresh m
              => [LNSubstVFresh]
              -> m (Maybe (Maybe LNSubst, [S.Set LNSubstVFresh]))
simpSingleton [subst0] = do
        subst <- freshToFree subst0
        return (Just (Just subst, []))
simpSingleton _        = return Nothing


-- | If all substitutions @si@ map a variable @v@ to terms with the same
--   outermost function symbol @f@, then they all contain the common factor
--   @{v |-> f(x1,..,xk)}@ for fresh variables xi and we can replace
--   @x |-> ..@ by @{x1 |-> ti1, x2 |-> ti2, ..}@ in all substitutions @si@.
simpAbstractFun :: MonadFresh m
                => [LNSubstVFresh]
                -> m (Maybe (Maybe LNSubst, [S.Set LNSubstVFresh]))
simpAbstractFun []             = return Nothing
simpAbstractFun (subst:others) = case commonOperators of
    [] -> return Nothing
    -- abstract all arguments
    (v, o, argss@(args:_)):_ | all ((==length args) . length) argss -> do
        fvars <- mapM (\_ -> freshLVar "x" LSortMsg) args
        let substs' = zipWith (abstractAll v fvars) (subst:others) argss
            fsubst  = substFromList [(v, fApp o (map varTerm fvars))]
        return $ Just (Just fsubst, [S.fromList substs'])
    -- abstract first two arguments
    (v, o@(AC _), argss):_ -> do
        fv1 <- freshLVar "x" LSortMsg
        fv2 <- freshLVar "x" LSortMsg
        let substs' = zipWith (abstractTwo o v fv1 fv2) (subst:others) argss
            fsubst  = substFromList [(v, fApp o (map varTerm [fv1,fv2]))]
        return $ Just (Just fsubst, [S.fromList substs'])
    (_, _ ,_):_ ->
        error "simpAbstract: impossible, invalid arities or List operator encountered."
  where
    commonOperators = do
        (v, viewTerm -> FApp o args) <- substToListVFresh subst
        let images = map (\s -> imageOfVFresh s v) others
            argss  = [ args' | Just (viewTerm -> FApp o' args') <- images, o' == o ]
        guard (length argss == length others)
        return (v, o, args:argss)

    abstractAll v freshVars s args = substFromListVFresh $
        filter ((/= v) . fst) (substToListVFresh s) ++ zip freshVars args

    abstractTwo o v fv1 fv2 s args = substFromListVFresh $
        filter ((/= v) . fst) (substToListVFresh s) ++ newMappings args
      where
        newMappings []      =
            error "simpAbstract: impossible, AC symbols must have arity >= 2."
        newMappings [a1,a2] = [(fv1, a1), (fv2, a2)]
        -- here we always abstract from left to right and do not
        -- take advantage of the AC property of o
        newMappings (a:as)  = [(fv1, a),  (fv2, fApp o as)]


-- | If all substitutions @si@ map a variable @v@ to the same name @n@,
--   then they all contain the common factor
--   @{v |-> n}@ and we can remove @{v -> n}@ from all substitutions @si@
simpAbstractName :: MonadFresh m
                 => [LNSubstVFresh]
                 -> m (Maybe (Maybe LNSubst, [S.Set LNSubstVFresh]))
simpAbstractName []             = return Nothing
simpAbstractName (subst:others) = case commonNames of
    []           -> return Nothing
    (v, c):_     ->
        return $ Just (Just $ substFromList [(v, c)]
                      , [S.fromList (map (\s -> restrictVFresh (delete v (domVFresh s)) s) (subst:others))])
  where
    commonNames = do
        (v, c@(viewTerm -> Lit (Con _))) <- substToListVFresh subst
        let images = map (\s -> imageOfVFresh s v) others
        guard (length images == length [ () | Just c' <- images, c' == c])
        return (v, c)


-- | If all substitutions @si@ map a variable @v@ to variables @xi@ of the same
--   sort @s@ then they all contain the common factor
--   @{v |-> y}@ for a fresh variable of sort @s@
--   and we can replace @{v -> xi}@ by @{y -> xi}@ in all substitutions @si@
simpAbstractSortedVar :: MonadFresh m
                      => [LNSubstVFresh]
                      -> m (Maybe (Maybe LNSubst, [S.Set LNSubstVFresh]))
simpAbstractSortedVar []             = return Nothing
simpAbstractSortedVar (subst:others) = case commonSortedVar of
    []            -> return Nothing
    (v, s, lvs):_ -> do
        fv <- freshLVar (lvarName v) s
        return $ Just (Just $ substFromList [(v, varTerm fv)]
                      , [S.fromList (zipWith (replaceMapping v fv) lvs (subst:others))])
  where
    commonSortedVar = do
        (v, (viewTerm -> Lit (Var lx))) <- substToListVFresh subst
        guard (sortCompare (lvarSort v)  (lvarSort lx) == Just GT)
        let images = map (\s -> imageOfVFresh s v) others
            -- FIXME: could be generalized to choose topsort s of all images if s < sortOf v
            --        could also be generalized to terms of a given sort
            goodImages = [ ly | Just (viewTerm -> Lit (Var ly)) <- images, lvarSort lx == lvarSort ly]
        guard (length images == length goodImages)
        return (v, lvarSort lx, (lx:goodImages))
    replaceMapping v fv lv sigma =
        substFromListVFresh $ (filter ((/=v) . fst) $ substToListVFresh sigma) ++ [(fv, varTerm lv)]

-- | If all substitutions @si@ map two variables @x@ and @y@ to identical terms @ti@,
--   then they all contain the common factor @{x |-> y}@ for a fresh variable @z@
--   and we can remove @{x |-> ti}@ from all @si@.
simpIdentify :: MonadFresh m
             => [LNSubstVFresh]
             -> m (Maybe (Maybe LNSubst, [S.Set LNSubstVFresh]))
simpIdentify []             = return Nothing
simpIdentify (subst:others) = case equalImgPairs of
    []         -> return Nothing
    ((v,v'):_) -> do
        let (vkeep, vremove) = case sortCompare (lvarSort v) (lvarSort v') of
                                 Just GT -> (v', v)
                                 Just _  -> (v, v')
                                 Nothing -> error $ "EquationStore.simpIdentify: impossible, variables with incomparable sorts: "
                                                    ++ show v ++" and "++ show v'
        return $ Just (Just  (substFromList [(vremove, varTerm vkeep)]),
                       [S.fromList (map (removeMappings [vkeep]) (subst:others))])
  where
    equalImgPairs = do
        (v,t)    <- substToListVFresh subst
        (v', t') <- substToListVFresh subst
        guard (t == t' && v < v' && all (agrees_on v v') others)
        return (v,v')
    agrees_on v v' s =
        imageOfVFresh s v == imageOfVFresh s v' && isJust (imageOfVFresh s v)
    removeMappings vs s = restrictVFresh (domVFresh s \\ vs) s


-- | Simplify by removing substitutions that occur twice in a disjunct.
--   We could generalize this function by using AC-equality or subsumption.
simpMinimize :: MonadFresh m => (LNSubstVFresh -> Bool) -> StateT EqStore m Bool
simpMinimize isContr = do
    conj <- MS.gets (L.get eqsConj)
    if F.any (F.any check . snd) conj
      then MS.modify (set eqsConj (fmap (second minimize) conj)) >> return True
      else return False
  where
    minimize substs
      | emptySubstVFresh `S.member` substs = S.singleton emptySubstVFresh
      | otherwise                          = S.filter (not . isContr) substs

    check subst = subst == emptySubstVFresh || isContr subst


-- | Traverse disjunctions and execute @f@ until it returns
--   @Just (mfreeSubst, disjs)@.
--   Then the @disjs@ is inserted at the current position, if @mfreeSubst@ is
--   @Just freesubst@, then it is applied to the equation store. @True@ is
--   returned if any modifications took place.
foreachDisj :: forall m. MonadFresh m
            => MaudeHandle
            -> ([LNSubstVFresh] -> m (Maybe (Maybe LNSubst, [S.Set LNSubstVFresh])))
            -> StateT EqStore m Bool
foreachDisj hnd f =
    go [] =<< gets (getConj . L.get eqsConj)
  where
    go :: [(SplitId, S.Set LNSubstVFresh)] -> [(SplitId, S.Set LNSubstVFresh)] -> StateT EqStore m Bool
    go _     []               = return False
    go lefts ((idx,d):rights) = do
        b <- lift $ f (S.toList d)
        case b of
          Nothing              -> go ((idx,d):lefts) rights
          Just (msubst, disjs) -> do
              eqsConj =: Conj (reverse lefts ++ ((,) idx <$> disjs) ++ rights)
              maybe (return ()) (\s -> MS.modify (applyEqStore hnd s)) msubst
              return True

------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print an 'EqStore'.
prettyEqStore :: HighlightDocument d => EqStore -> d
prettyEqStore eqs@(EqStore substFree (Conj disjs) _nextSplitId) = vcat $
  [if eqsIsFalse eqs then text "CONTRADICTORY" else emptyDoc] ++
  map combine
    [ ("subst", vcat $ prettySubst (text . show) (text . show) substFree)
    , ("conj",  vcat $ map ppDisj disjs)
    ]
  where
    combine (header, d) = fsep [keyword_ header <> colon, nest 2 d]
    ppDisj (idx, substs) =
        text (show (unSplitId idx) ++ ".") <-> numbered' conjs
      where
        conjs  = map ppSubst $ S.toList substs

    ppEq (a,b) =
      prettyNTerm (lit (Var a)) $$ nest (6::Int) (opEqual <-> prettyNTerm b)

    ppSubst subst = sep
      [ hsep (opExists : map prettyLVar (varsRangeVFresh subst)) <> opDot
      , nest 2 $ fsep $ intersperse opLAnd $ map ppEq $ substToListVFresh subst
      ]


-- Derived and delayed instances
--------------------------------

instance Show EqStore where
    show = render . prettyEqStore
