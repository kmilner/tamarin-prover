-- | Ephemeral preparation shared by wellformedness checking and closing.
-- Constructors are private: preparation is evidence about particular family
-- inputs under a particular signature, not a claim that warnings were absent.
module PreparedDiffTheory
    ( PreparedDiffTheory
    , prepareDiffTheory
    , reusePreparedDiffTheory
    , preparedDiffTheory
    , preparedDiffSignature
    , preparedDiffVariantReports
    , preparedDiffItems
    ) where

import qualified Extension.Data.Label as L
import ClosedTheory (normalizeOpenDiffTheory)
import OpenTheory
import Theory.Model
import Theory.Proof
import TheoryObject

type OpenItem = DiffTheoryItem DiffProtoRule OpenProtoRule DiffProofSkeleton ProofSkeleton
type PreparedItem = DiffTheoryItem ClosedDiffRule ClosedRuleFamily DiffProofSkeleton ProofSkeleton
type VariantReport = (Side, OpenProtoRule, [ProtoRuleAC], Bool)

data PreparedDiffTheory = PreparedDiffTheory
    SignatureWithMaude OpenDiffTheory OpenDiffTheory
    [([VariantReport], PreparedItem)]

preparedDiffTheory :: PreparedDiffTheory -> OpenDiffTheory
preparedDiffTheory (PreparedDiffTheory _ _ thy _) = thy

preparedDiffSignature :: PreparedDiffTheory -> SignatureWithMaude
preparedDiffSignature (PreparedDiffTheory sig _ _ _) = sig

prepareDiffTheory :: SignatureWithMaude -> OpenDiffTheory -> PreparedDiffTheory
prepareDiffTheory sig input = PreparedDiffTheory sig input normalized blocks
  where
    normalized = normalizeOpenDiffTheory input
    hnd = L.get sigmMaudeHandle sig
    blocks = map prepareItem (filter isRule (L.get diffThyItems normalized))
    prepareItem (DiffRuleItem ru) =
      let left = prepareSide LHS (getLeftProtoRule ru)
          right = prepareSide RHS (getRightProtoRule ru)
          reports = case L.get dprLeftRight ru of
            Nothing -> []
            Just _ -> [fst left, fst right]
          label (_, ClosedRuleFamily e members) =
            let name = "DiffProto" ++ getRuleName e
            in ClosedRuleFamily (addDiffLabel e name) (map (`addDiffLabel` name) members)
      in (reports, DiffRuleItem (ClosedDiffRule (L.get dprRule ru)
                                 (label (snd left)) (label (snd right))))
    prepareItem (EitherRuleItem (side, ru)) =
      ([], EitherRuleItem (snd (prepareSide side ru)))
    prepareItem _ = error "prepareDiffTheory: non-rule in rule sequence"
    prepareSide side ru =
      let ((aligned, canonical, valid), automatic) = prepareDiffRuleWithAutomatic hnd ru
          closed | null (L.get oprRuleAC ru) = automatic
                 | otherwise = closeProtoRule hnd [] aligned
      in ((side, ru, canonical, valid),
          (side, ClosedRuleFamily (L.get oprRuleE aligned) (map (L.get cprRuleAC) closed)))

-- | Reuse only when the signature, rules and macros are unchanged. The loader
-- adds intruder caches and a default lemma between checking and closing. Those
-- edits preserve evidence; changed source actions, slots, variants or macros do
-- not. On a changed input use the ordinary preparation boundary again.
reusePreparedDiffTheory :: SignatureWithMaude -> OpenDiffTheory
    -> PreparedDiffTheory -> PreparedDiffTheory
reusePreparedDiffTheory sig input (PreparedDiffTheory oldSig original normalized blocks)
    | toSignaturePure sig == toSignaturePure oldSig
      && relevant input == relevant original =
        PreparedDiffTheory sig input
          updated blocks
    | otherwise = prepareDiffTheory sig input
  where
    relevant = filter isInput . L.get diffThyItems
    isInput (DiffMacroItem _) = True
    isInput item = isRule item
    -- Detached compatibility can remove rule items, so original positions are
    -- not a safe stitching boundary there. Keep that legacy path in its adapter.
    updated | any isDetached (L.get diffThyItems input) = normalizeOpenDiffTheory input
            | otherwise = L.set diffThyItems
                (replaceRules normalizedRules (L.get diffThyItems input)) input
    isDetached (EitherRuleItem _) = True
    isDetached _ = False
    normalizedRules = filter isRule (L.get diffThyItems normalized)
    replaceRules _ [] = []
    replaceRules (r:rs) (i:is) | isRule i = r : replaceRules rs is
    replaceRules [] (i:_) | isRule i = error "reusePreparedDiffTheory: missing normalized parent"
    replaceRules rs (i:is) = i : replaceRules rs is

preparedDiffVariantReports :: PreparedDiffTheory -> [VariantReport]
preparedDiffVariantReports (PreparedDiffTheory _ _ _ blocks) = concatMap fst blocks

-- | Retain prepared families as the authoritative compiled representation.
-- Adding a generated label commutes with compilation and alignment: it is a
-- final zero-arity fact, so term abstraction, freshness and substitutions are
-- unchanged. Every old action subsequence match extends by the final pair;
-- every new match must leave that pair available, hence restricts to an old
-- match. This also covers duplicate user labels and rejected supplied families.
preparedDiffItems :: PreparedDiffTheory -> [PreparedItem]
preparedDiffItems (PreparedDiffTheory _ _ thy blocks) = merge blocks (L.get diffThyItems thy)
  where
    merge _ [] = []
    merge ((_,rule):rest) (i:is) | isRule i = rule : merge rest is
    merge [] (i:_) | isRule i = error "preparedDiffItems: missing prepared family"
    merge rest (i:is) = mapDiffTheoryItem (const (error "preparedDiffItems: missing parent block")) (const (error "preparedDiffItems: missing rule block")) id id i : merge rest is

isRule :: OpenItem -> Bool
isRule (DiffRuleItem _) = True
isRule (EitherRuleItem _) = True
isRule _ = False
