{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

-- | Parser and affine elaborator for the small general-purpose .tel2 language.
module Telomare.Tel2
  ( CompileError (..)
  , compileTel2
  ) where

import Control.Monad (foldM, void)
import Data.Char (isAsciiUpper, ord)
import Data.Functor (($>))
import qualified Data.Map.Strict as Map
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import Numeric.Natural (Natural)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Telomare.Compiler.Direct
import Telomare.Machine
import Telomare.Surface

newtype CompileError = CompileError String
  deriving (Eq, Show)

data Type
  = TName String
  | TUnit
  | TNat
  | TText
  | TList Type
  | TProd Type Type
  | TSum Type Type
  | TReply Type
  deriving (Eq, Show)

data Pattern = PVar String | PWild | PTuple [String]
  deriving (Eq, Show)

data Expr
  = EVar String
  | EUnit
  | ENat Natural
  | EText String
  | ECon String
  | EPair Expr Expr
  | ELet Pattern Type Expr Expr
  | ECall String Expr
  | ECopy Expr
  | EPrepend String Expr
  | ELeft Expr
  | ERight Expr
  | EMatchText Expr [(String, Expr)] Pattern Expr
  | EMatchNat Expr [(Natural, Expr)] Pattern Expr
  | ECase Expr [(String, Expr)]
  deriving (Eq, Show)

data Decl
  = DType String Type
  | DData String [String]
  | DDef String String Type Type Expr
  deriving (Eq, Show)

type Parser = Parsec Void String

spaceConsumer :: Parser ()
spaceConsumer = L.space space1 (L.skipLineComment "#") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: String -> Parser String
symbol = L.symbol spaceConsumer

identifier :: Parser String
identifier = lexeme ((:) <$> letterChar <*> many (alphaNumChar <|> char '_'))

reserved :: String -> Parser ()
reserved word = lexeme (string word *> notFollowedBy alphaNumChar)

stringLiteral :: Parser String
stringLiteral = lexeme (char '"' *> manyTill L.charLiteral (char '"'))

natural :: Parser Natural
natural = lexeme L.decimal

typeParser :: Parser Type
typeParser = makeSum
  where
    makeSum = chainRight makeProd "+" TSum
    makeProd = chainRight atom "*" TProd
    atom = between (symbol "(") (symbol ")") typeParser
      <|> (reserved "Unit" $> TUnit)
      <|> (reserved "Nat" $> TNat)
      <|> (reserved "Text" $> TText)
      <|> (reserved "List" *> (TList <$> atom))
      <|> (reserved "Reply" *> (TReply <$> atom))
      <|> (TName <$> identifier)
    chainRight value op constructor = do
      first <- value
      rest <- optional (symbol op *> chainRight value op constructor)
      pure (maybe first (constructor first) rest)

patternParser :: Parser Pattern
patternParser = (symbol "_" $> PWild) <|> try pairPattern <|> (PVar <$> identifier)
  where
    pairPattern = between (symbol "(") (symbol ")") $
      PTuple <$> sepBy1 identifier (symbol ",")

exprParser :: Parser Expr
exprParser = choice
  [ try letExpr
  , try matchTextExpr
  , try matchNatExpr
  , try caseExpr
  , try copyExpr
  , try prependExpr
  , try leftExpr
  , try rightExpr
  , atomExpr
  ]
  where
    letExpr = do
      reserved "let"
      pat <- patternParser
      void (symbol ":")
      ty <- typeParser
      void (symbol "=")
      value <- exprParser
      reserved "in"
      ELet pat ty value <$> exprParser
    matchTextExpr = do
      reserved "matchText"
      value <- exprParser
      reserved "of"
      void (symbol "{")
      arms <- many (try $ do key <- stringLiteral; void (symbol "->")
                             body <- exprParser; void (symbol ";"); pure (key, body))
      pat <- patternParser
      void (symbol "->")
      fallback <- exprParser
      void (optional (symbol ";"))
      void (symbol "}")
      pure (EMatchText value arms pat fallback)
    matchNatExpr = do
      reserved "matchNat"
      value <- exprParser
      reserved "of"
      void (symbol "{")
      arms <- many (try $ do key <- natural; void (symbol "->")
                             body <- exprParser; void (symbol ";"); pure (key, body))
      pat <- patternParser
      void (symbol "->")
      fallback <- exprParser
      void (optional (symbol ";"))
      void (symbol "}")
      pure (EMatchNat value arms pat fallback)
    caseExpr = do
      reserved "case"
      value <- exprParser
      reserved "of"
      arms <- between (symbol "{") (symbol "}") (some arm)
      pure (ECase value arms)
    arm = do
      con <- identifier
      void (symbol "->")
      body <- exprParser
      void (optional (symbol ";"))
      pure (con, body)
    copyExpr = reserved "copy" *> (ECopy <$> exprParser)
    prependExpr = reserved "prepend" *> (EPrepend <$> stringLiteral <*> exprParser)
    leftExpr = reserved "left" *> (ELeft <$> exprParser)
    rightExpr = reserved "right" *> (ERight <$> exprParser)
    atomExpr = choice
      [ try (symbol "()" $> EUnit)
      , between (symbol "(") (symbol ")") (try pairExpr <|> exprParser)
      , EText <$> stringLiteral
      , ENat <$> natural
      , try callExpr
      , do name <- identifier
           pure (if startsUpper name then ECon name else EVar name)
      ]
    pairExpr = do
      values <- sepBy1 exprParser (symbol ",")
      if length values < 2
        then fail "expected a tuple"
        else pure (foldr1 EPair values)
    callExpr = do
      name <- identifier
      ECall name <$> between (symbol "(") (symbol ")") exprParser

startsUpper :: String -> Bool
startsUpper (c : _) = isAsciiUpper c
startsUpper [] = False

declParser :: Parser Decl
declParser = choice [dataDecl, typeDecl, defDecl]
  where
    typeDecl = reserved "type" *> (DType <$> identifier <* symbol "=" <*> typeParser <* symbol ";")
    dataDecl = do
      reserved "data"
      name <- identifier
      void (symbol "=")
      names <- sepBy1 identifier (symbol "|")
      void (symbol ";")
      pure (DData name names)
    defDecl = do
      reserved "def"
      name <- identifier
      (arg, input) <- between (symbol "(") (symbol ")") $ do
        arg <- identifier
        void (symbol ":")
        (,) arg <$> typeParser
      void (symbol ":")
      output <- typeParser
      void (symbol "=")
      body <- exprParser
      void (symbol ";")
      pure (DDef name arg input output body)

sourceParser :: Parser [Decl]
sourceParser = spaceConsumer *> many declParser <* eof

data SomeTy where
  SomeTy :: SUTy a -> SomeTy

data Env c where
  Empty :: Env 'UUnit
  Bind :: String -> SUTy a -> Env c -> Env (a ':**: c)

data Elab c where
  Elab :: SUTy a -> Env r -> UMorph c (a ':**: r) -> Elab c

data SomeDef where
  SomeDef :: SUTy a -> SUTy b -> UMorph a b -> SomeDef

data Tables = Tables
  { aliases :: Map.Map String Type
  , constructors :: Map.Map String (String, Natural)
  , definitions :: Map.Map String SomeDef
  }

emptyTables :: Tables
emptyTables = Tables Map.empty Map.empty Map.empty

compileTel2 :: String -> Either CompileError Program
compileTel2 source = do
  decls <- either (bad . errorBundlePretty) Right
    (parse sourceParser "<tel2>" source)
  tables <- foldM addDecl emptyTables decls
  SomeTy stateTy <- resolveType tables (TName "State")
  SomeDef initIn initOut initU <- lookupDef tables "init"
  SomeDef stepIn stepOut stepU <- lookupDef tables "step"
  case (sameTy initIn SUUnit, sameTy initOut (replyTy stateTy),
        sameTy stepIn (SUProd (SUList SUNat) stateTy),
        sameTy stepOut (replyTy stateTy)) of
    (Just Refl, Just Refl, Just Refl, Just Refl) -> do
      initCore <- direct initU
      stepCore <- direct stepU
      pure (Program stateTy initU stepU initCore stepCore)
    _ -> bad "init/step do not implement the machine ABI for State"
  where
    replyTy stateTy = SUProd (SUList SUNat) (SUSum SUUnit stateTy)
    direct morph = either (bad . ("direct compilation failed: " <>) . show) Right
      (compileDirect morph)

addDecl :: Tables -> Decl -> Either CompileError Tables
addDecl tables (DType name ty)
  | Map.member name (aliases tables) = bad ("duplicate type " <> name)
  | otherwise = Right tables {aliases = Map.insert name ty (aliases tables)}
addDecl tables (DData name names)
  | null names = bad ("empty data " <> name)
  | Map.member name (aliases tables) = bad ("duplicate type " <> name)
  | not (unique names) = bad ("duplicate constructor in " <> name)
  | any (`Map.member` constructors tables) names = bad "duplicate constructor"
  | otherwise = Right tables
      { aliases = Map.insert name TNat (aliases tables)
      , constructors = foldl insert (constructors tables) (zip names [0 ..])
      }
  where
    insert cs (con, tag) = Map.insert con (name, tag) cs
addDecl tables (DDef name arg input output body)
  | Map.member name (definitions tables) = bad ("duplicate definition " <> name)
  | otherwise = do
      SomeTy inputTy <- resolveType tables input
      SomeTy outputTy <- resolveType tables output
      Elab actual _ bodyU <- elaborate tables (Bind arg inputTy Empty) outputTy body
      Refl <- requireSame outputTy actual
      let function = UExl :..: bodyU :..: URunit
      pure tables {definitions = Map.insert name
        (SomeDef inputTy outputTy function) (definitions tables)}

resolveType :: Tables -> Type -> Either CompileError SomeTy
resolveType tables = go []
  where
    go _ TUnit = Right (SomeTy SUUnit)
    go _ TNat = Right (SomeTy SUNat)
    go _ TText = Right (SomeTy (SUList SUNat))
    go seen (TList ty) = do SomeTy a <- go seen ty; pure (SomeTy (SUList a))
    go seen (TProd x y) = do
      SomeTy a <- go seen x
      SomeTy b <- go seen y
      pure (SomeTy (SUProd a b))
    go seen (TSum x y) = do
      SomeTy a <- go seen x
      SomeTy b <- go seen y
      pure (SomeTy (SUSum a b))
    go seen (TReply state) = go seen (TProd TText (TSum TUnit state))
    go seen (TName name)
      | name `elem` seen = bad ("cyclic type alias involving " <> name)
      | otherwise = case Map.lookup name (aliases tables) of
          Nothing -> bad ("unknown type " <> name)
          Just ty -> go (name : seen) ty

elaborate :: Tables -> Env c -> SUTy expected -> Expr -> Either CompileError (Elab c)
elaborate _ env expected (EVar name) = do
  Taken actual rest morph <- takeVar name env
  Refl <- requireSame expected actual
  pure (Elab expected rest morph)
elaborate _ env SUUnit EUnit = pure (constant env SUUnit UId)
elaborate _ env SUNat (ENat n) = pure (constant env SUNat (UConst n))
elaborate _ env (SUList SUNat) (EText text) =
  pure (constant env (SUList SUNat) (textU (encode text)))
elaborate tables env expected (ECon name) = case Map.lookup name (constructors tables) of
  Nothing -> bad ("unknown constructor " <> name)
  Just (_, tag) -> case sameTy expected SUNat of
    Just Refl -> pure (constant env SUNat (UConst tag))
    Nothing -> bad ("constructor " <> name <> " requires its data type")
elaborate tables env (SUProd a b) (EPair x y) = do
  Elab ax rest first <- elaborate tables env a x
  Refl <- requireSame a ax
  Elab by rest' second <- elaborate tables rest b y
  Refl <- requireSame b by
  pure (Elab (SUProd a b) rest'
    (UUnassoc :..: (UId :****: second) :..: first))
elaborate tables env expected (ELet pat ty value body) = do
  SomeTy valueTy <- resolveType tables ty
  Elab actual rest first <- elaborate tables env valueTy value
  Refl <- requireSame valueTy actual
  Bound boundEnv reshape <- bindPattern pat valueTy rest
  Elab result rest' second <- elaborate tables boundEnv expected body
  Refl <- requireSame expected result
  pure (Elab expected rest' (second :..: reshape :..: first))
elaborate tables env expected (ECall name argument) = do
  SomeDef input output function <- lookupDef tables name
  Refl <- requireSame expected output
  Elab actual rest arg <- elaborate tables env input argument
  Refl <- requireSame input actual
  pure (Elab output rest ((function :****: UId) :..: arg))
elaborate tables env (SUProd a b) (ECopy value) = do
  Refl <- requireSame a b
  copier <- copyMorph a
  Elab actual rest input <- elaborate tables env a value
  Refl <- requireSame a actual
  pure (Elab (SUProd a a) rest ((copier :****: UId) :..: input))
elaborate tables env (SUList SUNat) (EPrepend prefix suffix) = do
  Elab actual rest input <- elaborate tables env (SUList SUNat) suffix
  Refl <- requireSame (SUList SUNat) actual
  pure (Elab (SUList SUNat) rest
    ((prependU (encode prefix) :****: UId) :..: input))
elaborate tables env (SUSum a b) (ELeft value) = do
  Elab actual rest input <- elaborate tables env a value
  Refl <- requireSame a actual
  pure (Elab (SUSum a b) rest ((UInl :****: UId) :..: input))
elaborate tables env (SUSum a b) (ERight value) = do
  Elab actual rest input <- elaborate tables env b value
  Refl <- requireSame b actual
  pure (Elab (SUSum a b) rest ((UInr :****: UId) :..: input))
elaborate tables env expected (EMatchText value arms fallbackPat fallback) =
  elaborateMatches tables env expected (SUList SUNat) partitionTextU encode
    value arms fallbackPat fallback
elaborate tables env expected (EMatchNat value arms fallbackPat fallback) =
  elaborateMatches tables env expected SUNat partitionNatU id
    value arms fallbackPat fallback
elaborate tables env expected (ECase value arms) = do
  resolved <- traverse resolveArm arms
  let typeNames = [typeName | (typeName, _, _) <- resolved]
      armNames = fmap fst arms
  case resolved of
    [] -> bad "case has no arms"
    ((typeName, _, _) : _)
      | any (/= typeName) typeNames -> bad "case mixes constructors from different data types"
      | not (unique armNames) -> bad "case repeats a constructor"
      | length resolved /= constructorCount tables typeName ->
          bad ("case is not exhaustive for " <> typeName)
      | otherwise ->
          let tagged = [(tag, body) | (_, tag, body) <- resolved]
          in elaborateMatches tables env expected SUNat partitionNatU id value
               (init tagged) PWild (snd (last tagged))
  where
    resolveArm (name, body) = case Map.lookup name (constructors tables) of
      Nothing -> bad ("unknown constructor " <> name)
      Just (typeName, tag) -> Right (typeName, tag, body)
elaborate _ _ _ expression = bad ("type mismatch in expression " <> show expression)

-- Exact matching consumes the scrutinee once. Failed partitions reconstruct it
-- before trying the next arm; every selected branch may weaken its own context.
elaborateMatches
  :: Tables
  -> Env c
  -> SUTy out
  -> SUTy keyTy
  -> (key -> UMorph keyTy (keyTy ':++: keyTy))
  -> (literal -> key)
  -> Expr
  -> [(literal, Expr)]
  -> Pattern
  -> Expr
  -> Either CompileError (Elab c)
elaborateMatches tables env out keyTy partition convert value arms fallbackPat fallback = do
  Elab actual rest input <- elaborate tables env keyTy value
  Refl <- requireSame keyTy actual
  let branch pat body = do
        Bound branchEnv reshape <- bindPattern pat keyTy rest
        Elab actual' leftovers compiled <- elaborate tables branchEnv out body
        Refl <- requireSame out actual'
        pure (URunit :..: finish leftovers compiled :..: reshape)
      arm (literal, body) miss = do
        hit <- branch PWild body
        pure (UCase hit miss :..: distRight
          :..: (partition (convert literal) :****: UId))
  fallbackBranch <- branch fallbackPat fallback
  dispatch <- foldrM arm fallbackBranch arms
  pure (Elab out Empty (dispatch :..: input))

finish :: Env r -> UMorph c (a ':**: r) -> UMorph c a
finish _ morph = UExl :..: morph

data Taken c where
  Taken :: SUTy a -> Env r -> UMorph c (a ':**: r) -> Taken c

takeVar :: String -> Env c -> Either CompileError (Taken c)
takeVar name Empty = bad ("unknown or already consumed variable " <> name)
takeVar name (Bind current ty rest)
  | name == current = Right (Taken ty rest UId)
  | otherwise = do
      Taken found remaining morph <- takeVar name rest
      pure (Taken found (Bind current ty remaining)
        ((UId :****: USwap) :..: UAssoc :..: (morph :****: UId) :..: USwap))

data Bound c where
  Bound :: Env d -> UMorph c d -> Bound c

bindPattern :: Pattern -> SUTy a -> Env r -> Either CompileError (Bound (a ':**: r))
bindPattern PWild _ rest = Right (Bound rest UExr)
bindPattern (PVar name) ty rest
  | envContains name rest = bad ("duplicate or shadowed binder " <> name)
  | otherwise = Right (Bound (Bind name ty rest) UId)
bindPattern (PTuple names) ty rest
  | not (unique names) = bad "tuple pattern repeats a binder"
  | any (`envContains` rest) names = bad "tuple pattern shadows an existing binder"
  | otherwise = bindTuple names ty rest

bindTuple :: [String] -> SUTy a -> Env r -> Either CompileError (Bound (a ':**: r))
bindTuple [name] ty rest = Right (Bound (Bind name ty rest) UId)
bindTuple (name : names) (SUProd a b) rest = do
  Bound tailEnv tailMorph <- bindTuple names b rest
  pure (Bound (Bind name a tailEnv) ((UId :****: tailMorph) :..: UAssoc))
bindTuple _ _ _ = bad "tuple pattern does not match a right-associated product"

constant :: Env c -> SUTy a -> UMorph 'UUnit a -> Elab c
constant env ty value = Elab ty env ((value :****: UId) :..: ULunit)

copyMorph :: SUTy a -> Either CompileError (UMorph a (a ':**: a))
copyMorph SUUnit = Right ULunit
copyMorph SUNat = Right (UDup SUNat)
copyMorph (SUProd a b) = do
  left <- copyMorph a
  right <- copyMorph b
  pure (shuffle :..: (left :****: right))
  where
    shuffle = UAssoc :..: (UUnassoc :****: UId)
      :..: ((UId :****: USwap) :****: UId)
      :..: UUnassoc :..: (UId :****: UUnassoc) :..: UAssoc
copyMorph _ = bad "copy is available only for Unit, Nat, and their products"

distRight :: UMorph ((a ':++: b) ':**: c) ((a ':**: c) ':++: (b ':**: c))
distRight = UCase (UInl :..: USwap) (UInr :..: USwap) :..: UDistl :..: USwap

textU :: [Natural] -> UMorph 'UUnit ('UList 'UNat)
textU = foldr cons UNil
  where
    cons c rest = UCons :..: (UConst c :****: rest) :..: ULunit

prependU :: [Natural] -> UMorph ('UList 'UNat) ('UList 'UNat)
prependU = foldr cons UId
  where
    cons c rest = UCons :..: (UConst c :****: rest) :..: ULunit

partitionNatU :: Natural -> UMorph 'UNat ('UNat ':++: 'UNat)
partitionNatU 0 = UCase (UInl :..: UConst 0) (UInr :..: USuc) :..: UNatOut
partitionNatU n = UCase (UInr :..: UConst 0) recur :..: UNatOut
  where
    recur = UCase (UInl :..: USuc) (UInr :..: USuc) :..: partitionNatU (n - 1)

partitionTextU :: [Natural]
               -> UMorph ('UList 'UNat) ('UList 'UNat ':++: 'UList 'UNat)
partitionTextU [] = UCase (UInl :..: UNil) (UInr :..: UCons) :..: UUncons
partitionTextU (c : cs) = UCase emptyList nonempty :..: UUncons
  where
    emptyList = UInr :..: UNil
    nonempty = rebuild :..: distRight :..: (partitionNatU c :****: UId)
    rebuild = UCase matching (UInr :..: UCons)
    matching = UCase (UInl :..: UCons) (UInr :..: UCons)
      :..: UDistl :..: (UId :****: partitionTextU cs)

sameTy :: SUTy a -> SUTy b -> Maybe (a :~: b)
sameTy SUUnit SUUnit = Just Refl
sameTy SUNat SUNat = Just Refl
sameTy (SUProd a b) (SUProd c d) = do Refl <- sameTy a c; Refl <- sameTy b d; pure Refl
sameTy (SUSum a b) (SUSum c d) = do Refl <- sameTy a c; Refl <- sameTy b d; pure Refl
sameTy (SUList a) (SUList b) = do Refl <- sameTy a b; pure Refl
sameTy _ _ = Nothing

requireSame :: SUTy a -> SUTy b -> Either CompileError (a :~: b)
requireSame a b = maybe (bad "type mismatch") Right (sameTy a b)

lookupDef :: Tables -> String -> Either CompileError SomeDef
lookupDef tables name = maybe (bad ("unknown definition " <> name)) Right
  (Map.lookup name (definitions tables))

envContains :: String -> Env c -> Bool
envContains _ Empty = False
envContains name (Bind current _ rest) = name == current || envContains name rest

constructorCount :: Tables -> String -> Int
constructorCount tables typeName = length
  [() | (_, (owner, _)) <- Map.toList (constructors tables), owner == typeName]

unique :: Ord a => [a] -> Bool
unique values = length values == Map.size (Map.fromList [(value, ()) | value <- values])

encode :: String -> [Natural]
encode = fmap (fromIntegral . ord)

foldrM :: Monad m => (a -> b -> m b) -> b -> [a] -> m b
foldrM f z = foldM (flip f) z . reverse

bad :: String -> Either CompileError a
bad = Left . CompileError
