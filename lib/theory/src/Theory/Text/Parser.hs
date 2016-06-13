-- |
-- Copyright   : (c) 2010-2012 Simon Meier, Benedikt Schmidt
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : portable
--
-- Parsing protocol theories. See the MANUAL for a high-level description of
-- the syntax.
module Theory.Text.Parser (
    parseOpenTheory
  , parseOpenTheoryString
  , parseOpenDiffTheory
  , parseOpenDiffTheoryString
  , parseLemma
  , parseIntruderRules
  ) where

import           Prelude                    hiding (id, (.))

import qualified Data.ByteString            as B
import qualified Data.ByteString.Char8      as BC
import           Data.Char                  (isUpper, toUpper)
import           Data.Foldable              (asum)
import           Data.Label
import qualified Data.Map                   as M
import           Data.Maybe
import           Data.Monoid                hiding (Last)
import qualified Data.Set                   as S
import           Data.List                  (foldl1')
import qualified Data.Text                  as T
import qualified Data.Text.Encoding         as TE

import           Control.Applicative        hiding (empty, many, optional)
import           Control.Category
import           Control.Monad
import           Control.Monad.Trans

import           Text.Parsec                hiding ((<|>))
import           Text.PrettyPrint.Class     (render)

-- import qualified Extension.Data.Label       as L

import           Term.Substitution
import           Term.SubtermRule
import           Term.Maude.Signature
import           Theory
import           Theory.Text.Parser.Token


------------------------------------------------------------------------------
-- ParseAxiom datatype and functions to parse diff axioms
------------------------------------------------------------------------------

-- | An axiom describes a property that must hold for all traces. Axioms are
-- always used as lemmas in proofs.
data ParseAxiom = ParseAxiom
       { pAxName       :: String
       , pAxAttributes :: [AxiomAttribute]
       , pAxFormula    :: LNFormula
       }
       deriving( Eq, Ord, Show )

-- | True iff the axiom is a LHS axiom.
isLeftAxiom :: ParseAxiom -> Bool
isLeftAxiom ax =
     (LHSAxiom `elem` pAxAttributes ax)

-- | True iff the axiom is a RHS axiom.
isRightAxiom :: ParseAxiom -> Bool
isRightAxiom ax =
     (RHSAxiom `elem` pAxAttributes ax)

-- -- | True iff the axiom is a Both axiom.
-- isBothAxiom :: ParseAxiom -> Bool
-- isBothAxiom ax =
--      (BothAxiom `elem` pAxAttributes ax)

-- | Converts ParseAxioms to Axioms
toAxiom :: ParseAxiom -> Axiom
toAxiom ax = Axiom (pAxName ax) (pAxFormula ax)

------------------------------------------------------------------------------
-- Lexing and parsing theory files and proof methods
------------------------------------------------------------------------------

-- | Parse a security protocol theory file.
parseOpenTheory :: [String] -- ^ Defined flags
                -> FilePath
                -> IO OpenTheory
parseOpenTheory flags = parseFile (theory flags)

-- | Parse a security protocol theory file.
parseOpenDiffTheory :: [String] -- ^ Defined flags
                -> FilePath
                -> IO OpenDiffTheory
parseOpenDiffTheory flags = parseFile (diffTheory flags)


-- | Parse DH intruder rules.
parseIntruderRules
    :: MaudeSig -> String -> B.ByteString -> IO (Either ParseError [IntrRuleAC])
parseIntruderRules msig ctxtDesc =
    parseString ctxtDesc (setState msig >> many intrRule)
  . T.unpack . TE.decodeUtf8

-- | Parse a security protocol theory from a string.
parseOpenTheoryString :: [String]  -- ^ Defined flags.
                      -> String -> IO (Either ParseError OpenTheory)
parseOpenTheoryString flags = parseString "<unknown source>" (theory flags)

-- | Parse a security protocol theory from a string.
parseOpenDiffTheoryString :: [String]  -- ^ Defined flags.
                      -> String -> IO (Either ParseError OpenDiffTheory)
parseOpenDiffTheoryString flags = parseString "<unknown source>" (diffTheory flags)

-- | Parse a lemma for an open theory from a string.
parseLemma :: String -> IO (Either ParseError (Lemma ProofSkeleton))
parseLemma = parseString "<unknown source>" lemma

------------------------------------------------------------------------------
-- Parsing Terms
------------------------------------------------------------------------------

-- | Parse an lit with logical variables.
llit :: Parser LNTerm
llit = asum
    [ freshTerm <$> freshName
    , pubTerm <$> pubName
    , natTerm <$> natName 
    , varTerm <$> msgvar
    ]

-- | Parse an lit with logical variables of the given sort.
sortedLlit :: LSort -> Parser LNTerm
sortedLlit s@(LSortUser _) =
    varTerm <$> asum
      [ try $ sortedLVar [s]
      , do (n, i) <- indexedIdentifier
           return $ LVar n s i ]
sortedLlit s@LSortNat =
    varTerm <$> asum
      [ try $ sortedLVar [s]
      , do (n, i) <- indexedIdentifier
           return $ LVar n s i ]
sortedLlit _ = llit

-- | Lookup the arity of a non-ac symbol. Fails with a sensible error message
-- if the operator is not known.
lookupArity :: String -> Parser (Int, Privacy, Maybe [String], Bool)
lookupArity op = do
    maudeSig <- getState
    case lookup (BC.pack op) [ (noEqOp o, o) | o <- allSyms maudeSig ] of
        Nothing -> do
          fail $ "unknown operator `" ++ op ++ "'"
        Just (NoEqSym _ k priv sts iter) -> return (k,priv,sts,iter)

  where
    allSyms maudeSig =
      S.toList (noEqFunSyms maudeSig)
      ++ [NoEqSym emapSymString 2 Public Nothing False]
      ++ (catMaybes $ map mapACSym (S.toList $ userACSyms maudeSig))
      
    noEqOp (NoEqSym f _ _ _ _) = f
    mapACSym (UserAC f s) = Just (NoEqSym (BC.pack f) 2 Public (Just [s,s,s]) False)
    mapACSym _            = Nothing

-- | Parse an n-ary operator application for arbitrary n.
naryOpApp :: Parser LNTerm -> Parser LNTerm
naryOpApp plit = do
    op <- identifier
    (k,priv,sts,iter) <- lookupArity op
    ts <- parens $ arguments op k sts
    -- Verify arity
    let k' = length ts
    when (k /= k' && k > 1) $ do
        let err = "operator `" ++ op ++"' has arity " ++ show k ++
                  ", but here it is used with arity " ++ show k'
        liftIO $ putStrLn err
        fail err
    let args  = if k' > k && k == 1
                  then [foldr1 (curry fAppPair) ts]
                  else ts
    let app o = if BC.pack op == emapSymString 
                  then fAppC EMap
                  else fAppNoEq o
    msig <- getState
    return $ if op `elem` userACSyms' msig
      then lookupUserAC op (S.toList $ userACSyms msig) args
      else app (NoEqSym (BC.pack op) k priv sts iter) args
  where
    -- Functions on built-in sorts
    arguments _  0 _       = return []
    arguments _  _ Nothing = commaSep (natterm plit)
    -- Functions on user-defined sorts (with type signature)
    arguments op _ (Just xs) =
      commaSepN $ map (sortedTerm op) (zip ([1..] :: [Integer]) $ init xs)

    lookupUserAC idn (sym@(UserAC idn' _):syms) as
      | idn == idn'              = fAppAC sym as
      | otherwise                = lookupUserAC idn syms as
    lookupUserAC idn (_:syms) as = lookupUserAC idn syms as
    lookupUserAC idn [] _ = error $
      "Theory.Text.naryOpApp: error parsing user AC symbol: " ++ idn

    -- Parse a term with the given sort
    sortedTerm op (idx, sortname) = do
      let sort = sortFromString sortname
      lnterm <- natterm $ asum [try $ sortedLlit sort, llit]
      let order = sortCompare (sortOfLNTerm lnterm) sort
      if order == (Just LT) || order == (Just EQ)
        then return lnterm
        -- XXX: Because of limitations in the way Parsec handles errors,
        -- the error message from fail will not show up in the output which
        -- may be confusing to the user. We print an additional error message.
        else do
          pos <- getPosition
          let err = "Error: Function " ++ op ++ " expects argument of sort "
                    ++ sortname ++ " at position " ++ show idx ++
                    ", but found sort " ++ sortTypename (sortOfLNTerm lnterm)
                    ++ " instead! (line " ++ show (sourceLine pos) ++ ")."
          liftIO $ putStrLn err
          fail err

-- | Parse a binary operator written as @op{arg1}arg2@.
binaryAlgApp :: Parser LNTerm -> Parser LNTerm
binaryAlgApp plit = do
    op <- identifier
    (k,priv,sts,iter) <- lookupArity op
    arg1 <- braced (tupleterm plit)
    arg2 <- term plit
    when (k /= 2) $ fail $
      "only operators of arity 2 can be written using the `op{t1}t2' notation"
    return $ fAppNoEq (NoEqSym (BC.pack op) 2 priv sts iter) [arg1, arg2]

diffOp :: Parser LNTerm -> Parser LNTerm
diffOp plit = do
  ts <- symbol "diff" *> parens (commaSep (multterm plit))
  when (2 /= length ts) $ fail $
    "the diff operator requires exactly 2 arguments"
  diff <- enableDiff <$> getState
  when (not diff) $ fail $
    "diff operator found, but flag diff not set"
  let arg1 = head ts
  let arg2 = head (tail ts)
  return $ fAppDiff (arg1, arg2)

-- | Parse a term.
term :: Parser LNTerm -> Parser LNTerm
term plit = asum
    [ pairing       <?> "pairs"
    , parens (natterm plit)
    , symbol "0:nat" *> pure fAppNatZero
    , symbol "1:nat" *> pure fAppNatOne
    , symbol "1"     *> pure fAppOne
    , application   <?> "function application"
    , nullaryApp
    , plit
    ]
    <?> "term"
  where
    application = asum $ map (try . ($ plit)) [naryOpApp, binaryAlgApp, diffOp]
    pairing = angled (tupleterm plit)
    nullaryApp = do
      maudeSig <- getState
      -- FIXME: This try should not be necessary.
      asum [ try (symbol (BC.unpack sym)) *> pure (fApp (NoEq (NoEqSym sym 0 priv sts False)) [])
           | NoEq (NoEqSym sym 0 priv sts False) <- S.toList $ funSyms maudeSig ]

-- | A left-associative sequence of exponentations.
expterm :: Parser LNTerm -> Parser LNTerm
expterm plit = chainl1 (msetterm plit) ((\a b -> fAppExp (a,b)) <$ opExp)

-- | A left-associative sequence of multiplications.
multterm :: Parser LNTerm -> Parser LNTerm
multterm plit = do
    dh <- enableDH <$> getState
    if dh -- if DH is not enabled, do not accept 'multterm's and 'expterm's
        then chainl1 (expterm plit) ((\a b -> fAppAC Mult [a,b]) <$ opMult)
        else msetterm plit

-- | A left-associative sequence of multiset unions.
msetterm :: Parser LNTerm -> Parser LNTerm
msetterm plit = do
    mset <- enableMSet <$> getState
    if mset -- if multiset is not enabled, do not accept 'msetterms's
        then chainl1 (term plit) ((\a b -> fAppAC Union [a,b]) <$ opUnion)
        else term plit

-- | A left-associative sequence of terms on natural numbers.
natterm :: Parser LNTerm -> Parser LNTerm
natterm plit = do
    nats <- enableNat <$> getState
    if nats -- if nat is not enabled, do not accept 'natterms's
        then try (multterm plit) <|> sumterm
        else multterm plit
  where
    sumterm = chainl1 subnatterm ((\a b -> fAppAC NatPlus [a,b]) <$ opPlus)

    subnatterm = try $ asum
      [ parens sumterm
      , symbol "0:nat" *> pure fAppNatZero
      , symbol "1:nat" *> pure fAppNatOne
      , symbol "0"     *> pure fAppNatZero
      , symbol "1"     *> pure fAppNatOne
      , sortedLlit LSortNat
      ]

-- | A right-associative sequence of tuples.
tupleterm :: Parser LNTerm -> Parser LNTerm
tupleterm plit = chainr1 (natterm plit) ((\a b -> fAppPair (a,b)) <$ comma)

-- | Parse a fact.
fact :: Parser LNTerm -> Parser (Fact LNTerm)
fact plit = try (
    do multi <- option Linear (opBang *> pure Persistent)
       i     <- identifier
       case i of
         []                -> fail "empty identifier"
         (c:_) | isUpper c -> return ()
               | otherwise -> fail "facts must start with upper-case letters"
       ts    <- parens (commaSep (natterm plit))
       mkProtoFact multi i ts
    <?> "fact" )
  where
    singleTerm _ constr [t] = return $ constr t
    singleTerm f _      ts  = fail $ "fact '" ++ f ++ "' used with arity " ++
                                     show (length ts) ++ " instead of arity one"

    mkProtoFact multi f = case map toUpper f of
      "OUT" -> singleTerm f outFact
      "IN"  -> singleTerm f inFact
      "KU"  -> singleTerm f kuFact
      "KD"  -> return . Fact KDFact
      "DED" -> return . Fact DedFact
      "FR"  -> singleTerm f freshFact
      _     -> return . protoFact multi f


------------------------------------------------------------------------------
-- Parsing Rules
------------------------------------------------------------------------------

-- | Parse a "(modulo ..)" information.
modulo :: String -> Parser ()
modulo thy = parens $ symbol_ "modulo" *> symbol_ thy

moduloE, moduloAC :: Parser ()
moduloE  = modulo "E"
moduloAC = modulo "AC"

{-
-- | Parse a typing assertion modulo E.
typeAssertions :: Parser TypingE
typeAssertions = fmap TypingE $
    do try (symbols ["type", "assertions"])
       optional moduloE
       colon
       many1 ((,) <$> (try (msgvar <* colon))
                  <*> ( commaSep1 (try $ multterm llit) <|>
                        (opMinus *> pure [])
                      )
             )
    <|> pure []
-}

-- | Parse a protocol rule. For the special rules 'Reveal_fresh', 'Fresh',
-- 'Knows', and 'Learn' no rule is returned as the default theory already
-- contains them.
protoRule :: Parser (ProtoRuleE)
protoRule = do
    name  <- try (symbol "rule" *> optional moduloE *> identifier <* colon)
    when (name `elem` reservedRuleNames) $
        fail $ "cannot use reserved rule name '" ++ name ++ "'"
    subst <- option emptySubst letBlock
    (ps,as,cs) <- genericRule
    return $ apply subst $ Rule (StandRule name) ps cs as

-- | Parse a let block with bottom-up application semantics.
letBlock :: Parser LNSubst
letBlock = do
    toSubst <$> (symbol "let" *> many1 definition <* symbol "in")
  where
    toSubst = foldr1 compose . map (substFromList . return)
    definition = (,) <$> (sortedLVar [LSortMsg] <* equalSign) <*> natterm llit

-- | Parse an intruder rule.
intrRule :: Parser IntrRuleAC
intrRule = do
    info <- try (symbol "rule" *> moduloAC *> intrInfo <* colon)
    (ps,as,cs) <- genericRule
    return $ Rule info ps cs as
  where
    intrInfo = do
        name <- identifier
        case name of
          'c':cname -> return $ ConstrRule (BC.pack cname)
          'd':dname -> return $ DestrRule (BC.pack dname)
          _         -> fail $ "invalid intruder rule name '" ++ name ++ "'"

genericRule :: Parser ([LNFact], [LNFact], [LNFact])
genericRule =  
    (,,) <$> list (fact llit)
         <*> ((pure [] <* symbol "-->") <|>
              (symbol "--[" *> commaSep (fact llit) <* symbol "]->"))
         <*> list (fact llit)

{-
-- | Add facts to a rule.
addFacts :: String        -- ^ Command to be used: add_concs, add_prems
         -> Parser (String, [LNFact])
addFacts cmd =
    (,) <$> (symbol cmd *> identifier <* colon) <*> commaSep1 fact
-}

------------------------------------------------------------------------------
-- Parsing transfer notation
------------------------------------------------------------------------------

{-
-- | Parse an lit with strings for both constants as well as variables.
tlit :: Parser TTerm
tlit = asum
    [ constTerm <$> singleQuoted identifier
    , varTerm  <$> identifier
    ]

-- | Parse a single transfer.
transfer :: Parser Transfer
transfer = do
  tf <- (\l -> Transfer l Nothing Nothing) <$> identifier <* kw DOT
  (do right <- kw RIGHTARROW *> identifier <* colon
      desc <- transferDesc
      return $ tf { tfRecv = Just (desc right) }
   <|>
   do right <- kw LEFTARROW *> identifier <* colon
      descr <- transferDesc
      (do left <- try $ identifier <* kw LEFTARROW <* colon
          descl <- transferDesc
          return $ tf { tfSend = Just (descr right)
                      , tfRecv = Just (descl left) }
       <|>
       do return $ tf { tfSend = Just (descr right) }
       )
   <|>
   do left <- identifier
      (do kw RIGHTARROW
          (do right <- identifier <* colon
              desc <- transferDesc
              return $ tf { tfSend = Just (desc left)
                          , tfRecv = Just (desc right) }
           <|>
           do descl <- colon *> transferDesc
              (do right <- kw RIGHTARROW *> identifier <* colon
                  descr <- transferDesc
                  return $ tf { tfSend = Just (descl left)
                              , tfRecv = Just (descr right) }
               <|>
               do return $ tf { tfSend = Just (descl left) }
               )
           )
       <|>
       do kw LEFTARROW
          (do desc <- colon *> transferDesc
              return $ tf { tfRecv = Just (desc left) }
           <|>
           do right <- identifier <* colon
              desc <- transferDesc
              return $ tf { tfSend = Just (desc right)
                          , tfRecv = Just (desc left) }
           )
       )
    )
  where
    transferDesc = do
        ts        <- tupleterm tlit
        moreConcs <- (symbol "note" *> many1 (try $ fact tlit))
                     <|> pure []
        types     <- typeAssertions
        return $ \a -> TransferDesc a ts moreConcs types


-- | Parse a protocol in transfer notation
transferProto :: Parser [ProtoRuleE]
transferProto = do
    name <- symbol "anb-proto" *> identifier
    braced (convTransferProto name <$> abbrevs <*> many1 transfer)
  where
    abbrevs = (symbol "let" *> many1 abbrev) <|> pure []
    abbrev = (,) <$> try (identifier <* kw EQUAL) <*> natterm tlit

-}

------------------------------------------------------------------------------
-- Parsing Standard and Guarded Formulas
------------------------------------------------------------------------------

-- | Parse an atom with possibly bound logical variables.
blatom :: Parser BLAtom
blatom = (fmap (fmapTerm (fmap Free))) <$> asum
  [ Last        <$> try (symbol "last" *> parens nodevarTerm)        <?> "last atom"
  , flip Action <$> try (fact llit <* opAt)        <*> nodevarTerm   <?> "action atom"
  , Less        <$> try (nodevarTerm <* opLess)    <*> nodevarTerm   <?> "less atom"
  , EqE         <$> try (natterm llit <* opEqual)  <*> natterm llit <?> "term equality"
  , EqE         <$>     (nodevarTerm  <* opEqual)  <*> nodevarTerm   <?> "node equality"
  ]
  where
    nodevarTerm = (lit . Var) <$> nodevar

-- | Parse an atom of a formula.
fatom :: Parser LNFormula
fatom = asum
  [ pure lfalse <* opLFalse
  , pure ltrue  <* opLTrue
  , Ato <$> try blatom
  , quantification
  , parens iff
  ]
  where
    quantification = do
        q <- (pure forall <* opForall) <|> (pure exists <* opExists)
        vs <- many1 lvar <* dot
        f  <- iff
        return $ foldr (hinted q) f vs

    hinted :: ((String, LSort) -> LVar -> a) -> LVar -> a
    hinted f v@(LVar n s _) = f (n,s) v



-- | Parse a negation.
negation :: Parser LNFormula
negation = opLNot *> (Not <$> fatom) <|> fatom

-- | Parse a left-associative sequence of conjunctions.
conjuncts :: Parser LNFormula
conjuncts = chainl1 negation ((.&&.) <$ opLAnd)

-- | Parse a left-associative sequence of disjunctions.
disjuncts :: Parser LNFormula
disjuncts = chainl1 conjuncts ((.||.) <$ opLOr)

-- | An implication.
imp :: Parser LNFormula
imp = do
  lhs <- disjuncts
  asum [ opImplies *> ((lhs .==>.) <$> imp)
       , pure lhs ]

-- | An logical equivalence.
iff :: Parser LNFormula
iff = do
  lhs <- imp
  asum [opLEquiv *> ((lhs .<=>.) <$> imp), pure lhs ]

-- | Parse a standard formula.
standardFormula :: Parser LNFormula
standardFormula = iff

-- | Parse a guarded formula using the hack of parsing a standard formula and
-- converting it afterwards.
--
-- FIXME: Write a proper parser.
guardedFormula :: Parser LNGuarded
guardedFormula = try $ do
    res <- formulaToGuarded <$> standardFormula
    case res of
        Left d   -> fail $ render d
        Right gf -> return gf


------------------------------------------------------------------------------
-- Parsing Axioms
------------------------------------------------------------------------------

-- | Parse a 'AxiomAttribute'.
axiomAttribute :: Parser AxiomAttribute
axiomAttribute = asum
  [ symbol "left"          *> pure LHSAxiom
  , symbol "right"         *> pure RHSAxiom
  , symbol "both"          *> pure BothAxiom
  ]

-- | Parse an axiom.
axiom :: Parser Axiom
axiom = Axiom <$> (symbol "axiom" *> identifier <* colon)
              <*> doubleQuoted standardFormula

-- | Parse a diff axiom.
diffAxiom :: Parser ParseAxiom
diffAxiom = ParseAxiom <$> (symbol "axiom" *> identifier)
              <*> (option [] $ list axiomAttribute)
              <*> (colon *> doubleQuoted standardFormula)

------------------------------------------------------------------------------
-- Parsing Lemmas
------------------------------------------------------------------------------

-- | Parse a 'LemmaAttribute'.
lemmaAttribute :: Parser LemmaAttribute
lemmaAttribute = asum
  [ symbol "typing"        *> pure TypingLemma
  , symbol "reuse"         *> pure ReuseLemma
  , symbol "use_induction" *> pure InvariantLemma
  , symbol "hide_lemma="   *> (HideLemma <$> identifier)
  , symbol "left"          *> pure LHSLemma
  , symbol "right"         *> pure RHSLemma
--   , symbol "both"          *> pure BothLemma
  ]

-- | Parse a 'TraceQuantifier'.
traceQuantifier :: Parser TraceQuantifier
traceQuantifier = asum
  [ symbol "all-traces" *> pure AllTraces
  , symbol "exists-trace"  *> pure ExistsTrace
  ]

-- | Parse a lemma.
lemma :: Parser (Lemma ProofSkeleton)
lemma = skeletonLemma <$> (symbol "lemma" *> optional moduloE *> identifier)
                      <*> (option [] $ list lemmaAttribute)
                      <*> (colon *> option AllTraces traceQuantifier)
                      <*> doubleQuoted standardFormula
                      <*> (proofSkeleton <|> pure (unproven ()))

-- | Parse a diff lemma.
diffLemma :: Parser (DiffLemma DiffProofSkeleton)
diffLemma = skeletonDiffLemma <$> (symbol "diffLemma" *> identifier)
                              <*> (option [] $ list lemmaAttribute)
                              <*> (colon *> (diffProofSkeleton <|> pure (diffUnproven ())))

                      
------------------------------------------------------------------------------
-- Parsing Proofs
------------------------------------------------------------------------------

-- | Parse a node premise.
nodePrem :: Parser NodePrem
nodePrem = parens ((,) <$> nodevar
                       <*> (comma *> fmap (PremIdx . fromIntegral) natural))

-- | Parse a node conclusion.
nodeConc :: Parser NodeConc
nodeConc = parens ((,) <$> nodevar
                       <*> (comma *> fmap (ConcIdx .fromIntegral) natural))

-- | Parse a goal.
goal :: Parser Goal
goal = asum
    [ premiseGoal
    , actionGoal
    , chainGoal
    , disjSplitGoal
    , eqSplitGoal
    ]
  where
    actionGoal = do
        fa <- try (fact llit <* opAt)
        i  <- nodevar
        return $ ActionG i fa

    premiseGoal = do
        (fa, v) <- try ((,) <$> fact llit <*> opRequires)
        i  <- nodevar
        return $ PremiseG (i, v) fa

    chainGoal = ChainG <$> (try (nodeConc <* opChain)) <*> nodePrem

    disjSplitGoal = (DisjG . Disj) <$> sepBy1 guardedFormula (symbol "∥")

    eqSplitGoal = try $ do
        symbol_ "splitEqs"
        parens $ (SplitG . SplitId . fromIntegral) <$> natural


-- | Parse a proof method.
proofMethod :: Parser ProofMethod
proofMethod = asum
  [ symbol "sorry"         *> pure (Sorry Nothing)
  , symbol "simplify"      *> pure Simplify
  , symbol "solve"         *> (SolveGoal <$> parens goal)
  , symbol "contradiction" *> pure (Contradiction Nothing)
  , symbol "induction"     *> pure Induction
  ]

-- | Parse a proof skeleton.
proofSkeleton :: Parser ProofSkeleton
proofSkeleton =
    solvedProof <|> finalProof <|> interProof
  where
    solvedProof =
        symbol "SOLVED" *> pure (LNode (ProofStep Solved ()) M.empty)

    finalProof = do
        method <- symbol "by" *> proofMethod
        return (LNode (ProofStep method ()) M.empty)

    interProof = do
        method <- proofMethod
        cases  <- (sepBy oneCase (symbol "next") <* symbol "qed") <|>
                  ((return . (,) "") <$> proofSkeleton          )
        return (LNode (ProofStep method ()) (M.fromList cases))

    oneCase = (,) <$> (symbol "case" *> identifier) <*> proofSkeleton

-- | Parse a proof method.
diffProofMethod :: Parser DiffProofMethod
diffProofMethod = asum
  [ symbol "sorry"            *> pure (DiffSorry Nothing)
  , symbol "rule-equivalence" *> pure DiffRuleEquivalence
  , symbol "backward-search"  *> pure DiffBackwardSearch
  , symbol "step"             *> (DiffBackwardSearchStep <$> parens proofMethod)
  , symbol "ATTACK"           *> pure DiffAttack
  ]
    
-- | Parse a diff proof skeleton.
diffProofSkeleton :: Parser DiffProofSkeleton
diffProofSkeleton =
    solvedProof {-<|> attackProof-} <|> finalProof <|> interProof
  where
    solvedProof =
        symbol "MIRRORED" *> pure (LNode (DiffProofStep DiffMirrored ()) M.empty)

--     attackProof =
--         symbol "ATTACK" *> pure (LNode (DiffProofStep DiffAttack ()) M.empty)
        
    finalProof = do
        method <- symbol "by" *> diffProofMethod
        return (LNode (DiffProofStep method ()) M.empty)

    interProof = do
        method <- diffProofMethod
        cases  <- (sepBy oneCase (symbol "next") <* symbol "qed") <|>
                  ((return . (,) "") <$> diffProofSkeleton          )
        return (LNode (DiffProofStep method ()) (M.fromList cases))

    oneCase = (,) <$> (symbol "case" *> identifier) <*> diffProofSkeleton

------------------------------------------------------------------------------
-- Parsing Signatures
------------------------------------------------------------------------------

-- | Builtin signatures.
builtins :: Parser ()
builtins =
    symbol "builtins" *> colon *> commaSep1 builtinTheory *> pure ()
  where
    extendSig msig = modifyState (`mappend` msig)

    builtinTheory = asum
      [ try (symbol "diffie-hellman")
          *> extendSig dhMaudeSig
      , try (symbol "natural-numbers")
          *> extendSig natMaudeSig
      , try (symbol "bilinear-pairing")
          *> extendSig bpMaudeSig
      , try (symbol "multiset")
          *> extendSig msetMaudeSig
      , try (symbol "symmetric-encryption")
          *> extendSig symEncMaudeSig
      , try (symbol "asymmetric-encryption")
          *> extendSig asymEncMaudeSig
      , try (symbol "signing")
          *> extendSig signatureMaudeSig
      , symbol "hashing"
          *> extendSig hashMaudeSig
      ]

-- | User-defined sorts.
usersorts :: Parser ()
usersorts =
    symbol "usersorts" *> colon *> commaSep1 sortSymbol *> pure ()
  where
    sortSymbol = do
      ident <- identifier
      sig   <- getState
      setState (addUserSort ident sig)

functions :: Parser ()
functions =
    symbol "functions" *> colon *> commaSep1 functionSymbol *> pure ()
  where
    functionSymbol = do
        f          <- BC.pack <$> identifier
        (k, sorts) <- parseArity
        priv       <- option Public (symbol "[private]" *> pure Private)
        ac         <- option False (symbol "[AC]" *> pure True)
        iter       <- option False (symbol "[iterated]" *> pure True)
        sig        <- getState
        -- Sanity checks for iterated functions
        when (iter && not (enableNat sig)) $ fail $
          "Natural numbers must be enabled to use iterated functions, " ++
          "please activate the natural-numbers builtin!"
        when iter (verifyIter f sorts)
        -- Sanity checks for user-sorted functions
        when (isJust sorts) (verifySorts (fromJust sorts) sig)
        if ac
          then do
            verifySymbol f (fromJust sorts)
            setState $ addUserACSym (UserAC (BC.unpack f) (head $ fromJust sorts)) sig
          else do
            let noeqsym = NoEqSym f k priv sorts iter
            verifyArities noeqsym sig
            setState $ addFunSym noeqsym sig

    -- Parse old-style function symbol (such as h/1, f/2, etc) or
    -- new-style function symbol (with function signature, such as
    -- f: Msg Msg -> Msg).
    parseArity = oldStyle <|> newStyle
    
    oldStyle = do
      k <- opSlash *> (fromIntegral <$> natural)
      return (k, Nothing)

    newStyle = do
      args <- colon *> wsSep identifier
      void $ symbol "->"
      retv <- identifier
      let sorts = args ++ [retv]
      return (length sorts - 1, Just sorts)

    verifySorts xs msig = flip mapM_ xs $ \sort ->
      if elem (sortFromString sort) (allSorts msig)
        then return ()
        else fail $ "Invalid sort specified: " ++ sort

    verifySymbol _ ([x,y,z]) | x == y && y == z = return ()
    verifySymbol f _ = fail $ "Invalid AC symbol: " ++ (BC.unpack f)
    
    verifyIter _ (Just ["Nat", "Msg", "Msg"]) = return ()
    verifyIter f _ = fail $ "Invalid iterated symbol: " ++ (BC.unpack f)

    verifyArities sym@(NoEqSym f _ _ _ _) sig = 
      case lookup f [ (noEqOp o, o) | o <- S.toList (stFunSyms sig)] of
        Just other | other /= sym ->
          fail $ "conflicting symbols: " ++
                 show sym ++ " and " ++ show other
        _ -> return ()
      where
        noEqOp (NoEqSym fs _ _ _ _) = fs

    allSorts msig =
      [LSortMsg, LSortFresh, LSortPub, LSortNat] ++
      (S.toList $ userSortsForMaudeSig msig)

equations :: Parser ()
equations =
    symbol "equations" *> colon *> commaSep1 equation *> pure ()
  where
    equation = do
        rrule <- RRule <$> term llit <*> (equalSign *> term llit)
        case rRuleToStRule rrule of
          Just str ->
              modifyState (addStRule str)
          Nothing  ->
              fail $ "Not a subterm rule: " ++ show rrule

------------------------------------------------------------------------------
-- Parsing Theories
------------------------------------------------------------------------------


-- | Parse a theory.
theory :: [String]   -- ^ Defined flags.
       -> Parser OpenTheory
theory flags0 = do 
    msig <- getState
    when ("diff" `S.member` (S.fromList flags0)) $ putState (msig `mappend` enableDiffMaudeSig) -- Add the diffEnabled flag into the MaudeSig when the diff flag is set on the command line.
    symbol_ "theory"
    thyId <- identifier
    symbol_ "begin"
--        *> addItems (S.fromList flags0) (set thyName thyId defaultOpenTheory)
        *> addItems (S.fromList flags0) (set thyName thyId (defaultOpenTheory ("diff" `S.member` (S.fromList flags0))))
--        *> addItems (S.fromList flags0) (set (sigpMaudeSig . thySignature) (TEMPORARY.MaudeSig False False False True pairFunSig TEMP2.pairRules S.empty S.empty)  (set thyName thyId (defaultOpenTheory True)))  -- instead of "True" use: ("diff" `S.member` (S.fromList flags0))
--           set (enableDiff . sigpMaudeSig . thySignature) msig thy
-- debugging:    fail $ "hallo" ++ show msig
--set (enableDiff . sigpMaudeSig . thySignature) (True)    
        <* symbol "end"
  where
    addItems :: S.Set String -> OpenTheory -> Parser OpenTheory
    addItems flags thy = asum
      [ do builtins
           msig <- getState
           addItems flags $ set (sigpMaudeSig . thySignature) msig thy
      , do usersorts
           msig <- getState
           addItems flags $ set (sigpMaudeSig . thySignature) msig thy
      , do functions
           msig <- getState
           addItems flags $ set (sigpMaudeSig . thySignature) msig thy
      , do equations
           msig <- getState
           addItems flags $ set (sigpMaudeSig . thySignature) msig thy
--      , do thy' <- foldM liftedAddProtoRule thy =<< transferProto
--           addItems flags thy'
      , do thy' <- liftedAddAxiom thy =<< axiom
           addItems flags thy'
      , do thy' <- liftedAddLemma thy =<< lemma
           addItems flags thy'
      , do ru <- protoRule
           thy' <- liftedAddProtoRule thy ru
           addItems flags thy'
      , do r <- intrRule
           addItems flags (addIntrRuleACs [r] thy)
      , do c <- formalComment
           addItems flags (addFormalComment c thy)
      , do ifdef flags thy
      , do define flags thy
      , do return thy
      ]

    define :: S.Set String -> OpenTheory -> Parser OpenTheory
    define flags thy = do
       flag <- try (symbol "#define") *> identifier
       addItems (S.insert flag flags) thy

    ifdef :: S.Set String -> OpenTheory -> Parser OpenTheory
    ifdef flags thy = do
       flag <- symbol_ "#ifdef" *> identifier
       thy' <- addItems flags thy
       symbol_ "#endif"
       if flag `S.member` flags
         then addItems flags thy'
         else addItems flags thy

    liftedAddProtoRule thy ru = case addProtoRule ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate rule: " ++ render (prettyRuleName ru)

    liftedAddLemma thy lem = case addLemma lem thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate lemma: " ++ get lName lem

    liftedAddAxiom thy ax = case addAxiom ax thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate axiom: " ++ get axName ax

        
-- | Parse a diff theory.
diffTheory :: [String]   -- ^ Defined flags.
       -> Parser OpenDiffTheory
diffTheory flags0 = do 
    msig <- getState
    putState (msig `mappend` enableDiffMaudeSig) -- Add the diffEnabled flag into the MaudeSig when the diff flag is set on the command line.
    symbol_ "theory"
    thyId <- identifier
    symbol_ "begin"
        *> addItems (S.fromList flags0) (set diffThyName thyId (defaultOpenDiffTheory ("diff" `S.member` (S.fromList flags0))))
        <* symbol "end"
  where
    addItems :: S.Set String -> OpenDiffTheory -> Parser OpenDiffTheory
    addItems flags thy = asum
      [ do builtins
           msig <- getState
           addItems flags $ set (sigpMaudeSig . diffThySignature) msig thy
      , do functions
           msig <- getState
           addItems flags $ set (sigpMaudeSig . diffThySignature) msig thy
      , do equations
           msig <- getState
           addItems flags $ set (sigpMaudeSig . diffThySignature) msig thy
--      , do thy' <- foldM liftedAddProtoRule thy =<< transferProto
--           addItems flags thy'
      , do thy' <- liftedAddAxiom thy =<< diffAxiom
           addItems flags thy'
      , do thy' <- liftedAddLemma thy =<< lemma
           addItems flags thy'
      , do thy' <- liftedAddDiffLemma thy =<< diffLemma
           addItems flags thy'
      , do ru <- protoRule
           thy' <- liftedAddProtoRule thy ru
           addItems flags thy'
      , do r <- intrRule
           addItems flags (addIntrRuleACsDiffAll [r] thy)
      , do c <- formalComment
           addItems flags (addFormalCommentDiff c thy)
      , do ifdef flags thy
      , do define flags thy
      , do return thy
      ]

    define :: S.Set String -> OpenDiffTheory -> Parser OpenDiffTheory
    define flags thy = do
       flag <- try (symbol "#define") *> identifier
       addItems (S.insert flag flags) thy

    ifdef :: S.Set String -> OpenDiffTheory -> Parser OpenDiffTheory
    ifdef flags thy = do
       flag <- symbol_ "#ifdef" *> identifier
       thy' <- addItems flags thy
       symbol_ "#endif"
       if flag `S.member` flags
         then addItems flags thy'
         else addItems flags thy

    liftedAddProtoRule thy ru = case addProtoDiffRule ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate rule: " ++ render (prettyRuleName ru)

    liftedAddDiffLemma thy ru = case addDiffLemma ru thy of
        Just thy' -> return thy'
        Nothing   -> fail $ "duplicate Diff Lemma: " ++ render (prettyDiffLemmaName ru)
        
    liftedAddLemma thy lem = if isLeftLemma lem
                                then case addLemmaDiff LHS lem thy of
                                        Just thy' -> return thy'
                                        Nothing   -> fail $ "duplicate lemma: " ++ get lName lem
                                else if isRightLemma lem 
                                     then case addLemmaDiff RHS lem thy of
                                             Just thy' -> return thy'
                                             Nothing   -> fail $ "duplicate lemma: " ++ get lName lem
                                     else case addLemmaDiff RHS (addRightLemma lem) thy of
                                             Just thy' -> case addLemmaDiff LHS (addLeftLemma lem) thy' of
                                                             Just thy'' -> return thy''
                                                             Nothing   -> fail $ "duplicate lemma: " ++ get lName lem
                                             Nothing   -> fail $ "duplicate lemma: " ++ get lName lem

    liftedAddAxiom thy ax = if isLeftAxiom ax
                               then case addAxiomDiff LHS (toAxiom ax) thy of
                                       Just thy' -> return thy'
                                       Nothing   -> fail $ "duplicate axiom: " ++ get axName (toAxiom ax)
                               else if isRightAxiom ax
                                       then case addAxiomDiff RHS (toAxiom ax) thy of
                                          Just thy' -> return thy'
                                          Nothing   -> fail $ "duplicate axiom: " ++ get axName (toAxiom ax)
                                       else case addAxiomDiff RHS (toAxiom ax) thy of
                                          Just thy' -> case addAxiomDiff LHS (toAxiom ax) thy' of
                                             Just thy'' -> return thy''
                                             Nothing   -> fail $ "duplicate axiom: " ++ get axName (toAxiom ax)
                                          Nothing   -> fail $ "duplicate axiom: " ++ get axName (toAxiom ax)
