{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE ViewPatterns               #-}
-- FIXME: Better solution for abstrTerm
{-# LANGUAGE FlexibleContexts           #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Variants of protocol rules.
module Theory.Tools.RuleVariants where

import           Term.Narrowing.Variants
import           Term.Rewriting.Norm
import           Theory.Model
import           Theory.Tools.EquationStore

import           Extension.Prelude
import           Logic.Connectives

-- import           Control.Applicative
import           Control.Monad.Bind
import           Control.Monad.Reader
import qualified Control.Monad.Trans.PreciseFresh as Precise

import qualified Data.Map                         as M
import qualified Data.Set                         as S
-- import           Data.Traversable                 (traverse)

-- import           Utils.Misc (stringSHA256)

-- import           System.IO.Unsafe
-- import           System.IO
-- import           System.Directory
-- import qualified Data.Binary as B
-- import qualified Data.ByteString.Lazy as BS

import           Debug.Trace.Ignore
import qualified Debug.Trace as TR
import qualified System.IO.Unsafe as Unsafe
import qualified System.Environment as SysEnv
import Data.Maybe (isJust)
import Term.Positions (findPos)

-- TAM_HS_DBG_VARIANTS=1 dumps composed_substs BEFORE simpDisjunction
-- and after, for each rule's variant generation.  Used to diff against
-- RS's expand_rule_variants to find the dedup divergence.  Established
-- (2026-05-28) that HS's Resolve1 variant disj has 6 substs IDENTICAL
-- to RS's — the H17.10 "HS reduces 6→2" claim was wrong (that trace
-- was from runtime saturate, not variant generation).
tamHsDbgVariants :: Bool
tamHsDbgVariants = Unsafe.unsafePerformIO $
    maybe False (== "1") <$> SysEnv.lookupEnv "TAM_HS_DBG_VARIANTS"
{-# NOINLINE tamHsDbgVariants #-}


tmpdir :: FilePath
tmpdir = "/tmp/tamarin/"


-- Variants of protocol rules
----------------------------------------------------------------------

-- | Compute the variants of a protocol rule.
--   1. Abstract away terms in facts with variables.
--   2. Compute variants of RHSs of equations.
--   3. Apply variant substitutions to equations
--      to obtain DNF of equations.
--   4. Simplify rule.
variantsProtoRule :: MaudeHandle -> ProtoRuleE -> Maybe ProtoRuleAC
variantsProtoRule hnd ru@(Rule (ProtoRuleEInfo na attr _) prems0 concs0 acts0 nvs0) =
    -- rename rule to decrease variable indices
    (`Precise.evalFresh` Precise.nothingUsed) . renamePrecise  $ convertRule `evalFreshTAvoiding` ru
  where
    convertRule :: FreshT Maybe (Rule ProtoRuleACInfo)
    convertRule = do
        (abstrPsCsAs, bindings) <- abstrRule
        let eqsAbstr         = map swap (M.toList bindings)
            abstractedTerms  = map snd eqsAbstr
            abstractionSubst = substFromList eqsAbstr
            variantSubsts    = computeVariantsCached (fAppList abstractedTerms) hnd
            substs           = [ restrictVFresh (frees abstrPsCsAs) $
                                   removeRenamings $ ((`runReader` hnd) . normSubstVFresh')  $
                                   composeVFresh vsubst abstractionSubst
                               |  vsubst <- variantSubsts,
                                  not $ isFreshRedundant vsubst ]

        case substs of
          [] -> mzero
          _  -> do
              -- TAM_HS_DBG_VARIANTS: dump composed substs BEFORE simp.
              () <- if tamHsDbgVariants
                    then do
                        TR.traceM ("[HS_VAR_BEFORE_SIMP] rule=" ++ show na
                            ++ " n_composed=" ++ show (length substs))
                        mapM_ (\(i, s) -> TR.traceM
                            ("[HS_VAR_BEFORE_SIMP]   subst[" ++ show i ++ "]: "
                                ++ show s)) (zip [0::Int ..] substs)
                        return ()
                    else return ()
              x <- simpDisjunction hnd (const (const False)) (Disj substs)
              -- TAM_HS_DBG_VARIANTS: dump after simp.
              () <- if tamHsDbgVariants
                    then case x of
                        (cs, mss) -> do
                            TR.traceM ("[HS_VAR_AFTER_SIMP] rule=" ++ show na
                                ++ " common_subst=" ++ show cs
                                ++ " n_residual=" ++ show (maybe 0 length mss))
                            case mss of
                                Just rs ->
                                    mapM_ (\(i, s) -> TR.traceM
                                        ("[HS_VAR_AFTER_SIMP]   subst[" ++ show i ++ "]: "
                                            ++ show s)) (zip [0::Int ..] rs)
                                Nothing -> return ()
                    else return ()
              case trace (show ("SIMP",abstractedTerms,
                                "abstr", abstrPsCsAs,
                                "substs", substs,
                                "simpSubsts:", x)) x of
                -- the variants can be simplified to a single case
                (commonSubst, Nothing) ->
                  return $ makeRule abstrPsCsAs commonSubst trueDisj
                (commonSubst, Just freshSubsts) ->
                  return $ makeRule abstrPsCsAs commonSubst freshSubsts

    abstrRule = (`runBindT` noBindings) $ do
        -- first import all vars into binding to obtain nicer names
        mapM_ abstrTerm [ varTerm v | v <- frees (prems0, concs0, acts0, nvs0) ]
        (,,,) <$> mapM abstrFact prems0
              <*> mapM abstrFact concs0
              <*> mapM abstrFact acts0
              <*> mapM abstrTerm nvs0

    irreducible = irreducibleFunSyms (mhMaudeSig hnd)
    abstrFact = traverse abstrTerm
    abstrTerm (viewTerm -> FApp o args) | o `S.member` irreducible =
        fApp o <$> mapM abstrTerm args
    abstrTerm t = do
        at :: LNTerm <- varTerm <$> importBinding (`LVar` sortOfLNTerm t) t (getHint t)
        return at
      where getHint (viewTerm -> Lit (Var v)) = lvarName v
            getHint _                         = "z"

    makeRule (ps, cs, as, nvs) subst freshSubsts0 =
        Rule (ProtoRuleACInfo na attr (Disj freshSubsts) []) prems concs acts newvs

      where prems = apply subst ps
            concs = apply subst cs
            acts  = apply subst as
            newvs = apply subst nvs
            freshSubsts = map (restrictVFresh (frees (prems, concs, acts, newvs))) freshSubsts0

    trueDisj = [ emptySubstVFresh ]

    freshlyIntroduced :: [LNTerm]
    freshlyIntroduced = [ t | Fact FreshFact _ [t] <- prems0 ]

    premiseTerms :: [LNTerm]
    premiseTerms = concat [ ts | Fact t _ ts <- prems0, t /= FreshFact ]

    -- Optimization documented in: https://eprint.iacr.org/2026/230
    isFreshRedundant :: LNSubstVFresh -> Bool
    isFreshRedundant sFresh =
      let subst = freshToFreeAvoidingFast sFresh (frees premiseTerms)
          premises = map ((`runReader` hnd) . norm') (apply subst premiseTerms)
          freshTerms = apply subst freshlyIntroduced
      in any (\ft -> any (isJust . findPos ft) premises) freshTerms

computeVariantsCached :: LNTerm -> MaudeHandle -> [LNSubstVFresh]
computeVariantsCached inp hnd = computeVariants inp `runReader` hnd
{-
  unsafePerformIO $ do
    createDirectoryIfMissing True tmpdir
    let hashInput = tmpdir ++ stringSHA256 (show inp)
    fEx <- doesFileExist hashInput
    if fEx
      then B.decodeFile hashInput
      else do let result = computeVariants inp `runReader` hnd
              (tmpFile,tmpHnd) <- openBinaryTempFile tmpdir "variants.tmp"
              BS.hPut tmpHnd $ B.encode result
              renameFile tmpFile hashInput
              return result
-}
