{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | Parser and affine elaborator for the small general-purpose .tel2 language.
module Telomare.Tel2
  ( CompileError (..)
  , compileTel2
  , compileTel2File
  ) where

import qualified Control.Exception as Exception
import Control.Monad (foldM, void)
import Data.Char (isAsciiUpper, ord)
import Data.Foldable (traverse_)
import Data.Functor (($>))
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import Numeric.Natural (Natural)
import System.Directory (doesFileExist)
import System.FilePath (takeDirectory, (</>))
import Text.Megaparsec hiding (State, count)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Paths_telomare (getDataFileName)
import Telomare.Compiler.Direct
import Telomare.Core (Morph (..), STy (..), Ty (..))
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
  | ESuc Expr
  | EAdd Expr
  | EIter Natural Expr String
  | EFold Expr Expr String
  | EWhile Natural Expr String String
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

data Source = Source
  { sourceModule  :: Maybe String
  , sourceImports :: [String]
  , sourceDecls   :: [Decl]
  }

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
  , try iterExpr
  , try foldExpr
  , try whileExpr
  , try copyExpr
  , try sucExpr
  , try addExpr
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
    iterExpr = do
      reserved "iterate"
      count <- natural
      reserved "from"
      seed <- exprParser
      reserved "with"
      EIter count seed <$> identifier
    foldExpr = do
      reserved "fold"
      input <- exprParser
      reserved "from"
      seed <- exprParser
      reserved "with"
      EFold input seed <$> identifier
    whileExpr = do
      reserved "while"
      limit <- natural
      reserved "from"
      seed <- exprParser
      reserved "testing"
      test <- identifier
      reserved "stepping"
      EWhile limit seed test <$> identifier
    copyExpr = reserved "copy" *> (ECopy <$> exprParser)
    sucExpr = reserved "suc" *> (ESuc <$> exprParser)
    addExpr = reserved "add" *> (EAdd <$> exprParser)
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
startsUpper []      = False

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

sourceParser :: Parser Source
sourceParser = spaceConsumer *> (Source <$> optional moduleHeader <*> many importDecl <*> many declParser) <* eof
  where
    moduleHeader = reserved "module" *> identifier <* symbol ";"
    importDecl = reserved "import" *> identifier <* symbol ";"

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
  { aliases      :: Map.Map String Type
  , constructors :: Map.Map String (String, Natural)
  , definitions  :: Map.Map String SomeDef
  }

emptyTables :: Tables
emptyTables = Tables Map.empty Map.empty Map.empty

compileTel2 :: String -> Either CompileError Program
compileTel2 source = do
  parsed <- parseSource "<tel2>" source
  if null (sourceImports parsed)
    then compileDecls (sourceDecls parsed)
    else bad "imports require compileTel2File"

-- | Compile a module and its imports. An import @Foo@ prefers @Foo.tel2@ in
-- the entry module's directory, then falls back to the packaged stdlib.
compileTel2File :: FilePath -> IO (Either CompileError Program)
compileTel2File path = do
  loaded <- loadModule (takeDirectory path) [] Nothing path
  pure $ do
    modules <- loaded
    compileDecls (concatMap snd (deduplicate modules))
  where
    deduplicate = go Set.empty
    go _ [] = []
    go seen (item@(name, _) : rest)
      | Set.member name seen = go seen rest
      | otherwise = item : go (Set.insert name seen) rest

loadModule
  :: FilePath
  -> [String]
  -> Maybe String
  -> FilePath
  -> IO (Either CompileError [(String, [Decl])])
loadModule root stack expected path = do
  contents <- Exception.try $ do
    source <- readFile path
    length source `seq` pure source
  case contents of
    Left err -> pure (bad (loadError expected path err))
    Right source -> case parseSource path source of
      Left err -> pure (Left err)
      Right parsed -> case sourceModule parsed of
        Nothing -> pure (bad ("module header required in " <> path))
        Just name
          | maybe False (/= name) expected ->
                pure (bad ("imported module " <> fromMaybe "" expected
                <> " declares module " <> name))
          | name `elem` stack ->
              pure (bad (renderCycle stack name name))
          | otherwise -> do
              imports <- traverse (loadImport name) (sourceImports parsed)
              pure $ do
                dependencies <- sequence imports
                pure (concat dependencies <> [(name, sourceDecls parsed)])
  where
    loadImport current name
      | name `elem` (current : stack) =
          pure (bad (renderCycle stack current name))
      | otherwise = do
          resolved <- resolveImport root name
          case resolved of
            Left err -> pure (Left err)
            Right importedPath ->
              loadModule root (current : stack) (Just name) importedPath
    loadError Nothing file err = "cannot load module file " <> file <> ": " <> show (err :: IOError)
    loadError (Just name) file err = "cannot load module " <> name <> " from " <> file <> ": " <> show (err :: IOError)
    renderCycle ancestors current name = "import cycle: "
      <> intercalate " -> " (reverse (current : ancestors) <> [name])

resolveImport :: FilePath -> String -> IO (Either CompileError FilePath)
resolveImport root name = do
  let sibling = root </> name <> ".tel2"
  siblingExists <- doesFileExist sibling
  if siblingExists
    then pure (Right sibling)
    else do
      packaged <- getDataFileName ("stdlib" </> name <> ".tel2")
      packagedExists <- doesFileExist packaged
      pure $ if packagedExists
        then Right packaged
        else bad ("cannot load module " <> name <> "; searched "
          <> sibling <> " and packaged stdlib " <> packaged)

parseSource :: FilePath -> String -> Either CompileError Source
parseSource name = either (bad . errorBundlePretty) Right . parse sourceParser name

compileDecls :: [Decl] -> Either CompileError Program
compileDecls decls = do
  validateRecursion decls
  tablesWithTypes <- foldM addTypeDecl emptyTables decls
  orderedDefs <- orderDefinitions decls
  tables <- foldM addDef tablesWithTypes orderedDefs
  SomeTy stateTy <- resolveType tables (TName "State")
  SomeDef initIn initOut initU <- lookupDef tables "init"
  SomeDef stepIn stepOut stepU <- lookupDef tables "step"
  case (sameTy initIn SUUnit, sameTy initOut (replyTy stateTy),
        sameTy stepIn (SUProd (SUList SUNat) stateTy),
        sameTy stepOut (replyTy stateTy)) of
    (Just Refl, Just Refl, Just Refl, Just Refl) -> do
      initCore <- compileEntry tables decls "init" SUUnit (replyTy stateTy) initU
      stepCore <- compileEntry tables decls "step"
        (SUProd (SUList SUNat) stateTy) (replyTy stateTy) stepU
      pure (Program stateTy initU stepU initCore stepCore)
    _ -> bad "init/step do not implement the machine ABI for State"
  where
    replyTy stateTy = SUProd (SUList SUNat) (SUSum SUUnit stateTy)

compileEntry
  :: Tables
  -> [Decl]
  -> String
  -> SUTy input
  -> SUTy output
  -> UMorph input output
  -> Either CompileError (CoreEntry input output)
compileEntry tables decls name inputTy outputTy source =
  case [body | DDef current _ _ _ body <- decls, current == name] of
    [body] | Just (bindings, continuation) <- closedEntry body -> do
      let names = Set.fromList [binder | BindingSpec binder _ _ <- bindings]
      if length bindings == Set.size names
        then Right ()
        else bad "recursive bindings must have unique names"
      if freeVars continuation `Set.isSubsetOf` names
        then Right ()
        else bad "recursive continuation cannot capture the entry context"
      CompiledBindings bindingEnv _ bindingCore <-
        compileBindings tables bindings
      Elab result continuationRest continuationU <- elaborate tables
        bindingEnv outputTy continuation
      Refl <- requireSame outputTy result
      continuationCore <- direct (finish continuationRest continuationU)
      let core = BoxS continuationCore :.: bindingCore :.: WeakS
      pure (CoreEntry inputTy (SBang (liftSTy outputTy))
        (stripLift outputTy) core)
    _ -> do
      core <- direct source
      pure (CoreEntry inputTy (liftSTy outputTy) (stripLift outputTy) core)
  where
    direct morph = either (bad . ("direct compilation failed: " <>) . show) Right
      (compileDirect morph)

data BindingSpec = BindingSpec String Type Expr

closedEntry :: Expr -> Maybe ([BindingSpec], Expr)
closedEntry = go []
  where
    go bindings (ELet (PVar name) ty value body)
      | isClosedLoop value = go (bindings <> [BindingSpec name ty value]) body
    go [] _ = Nothing
    go bindings continuation = Just (bindings, continuation)

isClosedLoop :: Expr -> Bool
isClosedLoop EIter {}  = True
isClosedLoop EFold {}  = True
isClosedLoop EWhile {} = True
isClosedLoop _         = False

data SomeClosedLoop where
  SomeClosedLoop
    :: SUTy a
    -> Morph 'Unit ('Bang (Lift a))
    -> SomeClosedLoop

compileClosedLoop :: Tables -> Type -> Expr -> Either CompileError SomeClosedLoop
compileClosedLoop tables annotation expression = do
  SomeTy resultTy <- resolveType tables annotation
  case expression of
    EIter count seed stepName -> do
      requireClosed "iteration seed" seed
      SomeDef stepIn stepOut stepU <- lookupDef tables stepName
      Refl <- requireSame resultTy stepIn
      Refl <- requireSame resultTy stepOut
      seedCore <- compileClosed tables resultTy seed
      stepCore <- directCompile stepU
      pure (SomeClosedLoop resultTy
        (IterS stepCore :.: (ConstS count :***: BoxValS seedCore) :.: RunitS))
    EFold input seed stepName -> do
      requireClosed "fold input" input
      requireClosed "fold seed" seed
      SomeDef stepIn stepOut stepU <- lookupDef tables stepName
      case stepIn of
        SUProd accumulator element -> do
          Refl <- requireSame resultTy accumulator
          Refl <- requireSame resultTy stepOut
          inputCore <- compileClosed tables (SUList element) input
          seedCore <- compileClosed tables accumulator seed
          stepCore <- directCompile stepU
          pure (SomeClosedLoop accumulator
            (FoldS stepCore :.: (inputCore :***: BoxValS seedCore) :.: RunitS))
        _ -> bad "fold step must accept accumulator * element"
    EWhile limit seed testName stepName -> do
      requireClosed "while seed" seed
      SomeDef testIn testOut testU <- lookupDef tables testName
      SomeDef stepIn stepOut stepU <- lookupDef tables stepName
      Refl <- requireSame resultTy testIn
      Refl <- requireSame resultTy stepIn
      Refl <- requireSame resultTy stepOut
      Refl <- requireSame testOut (SUSum SUUnit SUUnit)
      seedCore <- compileClosed tables resultTy seed
      testCore <- directCompile testU
      stepCore <- directCompile stepU
      pure (SomeClosedLoop resultTy
        (WhileS (liftSTy resultTy) testCore stepCore
          :.: (ConstS limit :***: BoxValS seedCore) :.: RunitS))
    _ -> bad "expected a closed recursive binding"
  where
    requireClosed description value
      | Set.null (freeVars value) && not (containsIter value) = Right ()
      | otherwise = bad (description <> " cannot capture or contain recursion")

compileClosed
  :: Tables
  -> SUTy a
  -> Expr
  -> Either CompileError (Morph 'Unit (Lift a))
compileClosed tables ty value = do
  Elab actual rest source <- elaborate tables Empty ty value
  Refl <- requireSame ty actual
  directCompile (finish rest source)

directCompile :: UMorph a b -> Either CompileError (Morph (Lift a) (Lift b))
directCompile morph = either
  (bad . ("direct compilation failed: " <>) . show) Right (compileDirect morph)

data CompiledBindings where
  CompiledBindings
    :: Env c
    -> STy (Lift c)
    -> Morph 'Unit ('Bang (Lift c))
    -> CompiledBindings

compileBindings :: Tables -> [BindingSpec] -> Either CompileError CompiledBindings
compileBindings _ [] = Right (CompiledBindings Empty SUnit (BoxValS IdS))
compileBindings tables (BindingSpec name annotation expression : rest) = do
  SomeTy declaredTy <- resolveType tables annotation
  SomeClosedLoop actualTy loopCore <- compileClosedLoop tables annotation expression
  Refl <- requireSame declaredTy actualTy
  CompiledBindings env envTy restCore <- compileBindings tables rest
  if envContains name env
    then bad ("duplicate recursive binder " <> name)
    else pure (CompiledBindings (Bind name declaredTy env)
      (SProd (liftSTy declaredTy) envTy)
      (MergeS :.: (loopCore :***: restCore) :.: RunitS))

stripLift :: SUTy a -> Strip (Lift a) :~: a
stripLift SUUnit = Refl
stripLift SUNat = Refl
stripLift (SUProd a b) = case (stripLift a, stripLift b) of
  (Refl, Refl) -> Refl
stripLift (SUSum a b) = case (stripLift a, stripLift b) of
  (Refl, Refl) -> Refl
stripLift (SUList a) = case stripLift a of Refl -> Refl

validateRecursion :: [Decl] -> Either CompileError ()
validateRecursion = traverse_ validate
  where
    validate (DDef name _ _ _ body)
      | not (containsIter body) = Right ()
      | name `elem` ["init", "step"]
      , Just (bindings, continuation) <- closedEntry body
      , not (containsIter continuation)
      , all validBinding bindings = Right ()
      | otherwise = bad "recursion requires whole entry-level closed bindings"
    validate _ = Right ()
    validBinding (BindingSpec _ _ expression) = case expression of
      EIter _ seed _     -> not (containsIter seed)
      EFold input seed _ -> not (containsIter input || containsIter seed)
      EWhile _ seed _ _  -> not (containsIter seed)
      _                  -> False

addTypeDecl :: Tables -> Decl -> Either CompileError Tables
addTypeDecl tables (DType name ty)
  | Map.member name (aliases tables) = bad ("duplicate type " <> name)
  | otherwise = Right tables {aliases = Map.insert name ty (aliases tables)}
addTypeDecl tables (DData name names)
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
addTypeDecl tables DDef {} = Right tables

addDef :: Tables -> Decl -> Either CompileError Tables
addDef tables (DDef name arg input output body) = do
  SomeTy inputTy <- resolveType tables input
  SomeTy outputTy <- resolveType tables output
  Elab actual _ bodyU <- elaborate tables (Bind arg inputTy Empty) outputTy body
  Refl <- requireSame outputTy actual
  let function = UExl :..: bodyU :..: URunit
  pure tables {definitions = Map.insert name
    (SomeDef inputTy outputTy function) (definitions tables)}
addDef tables _ = Right tables

orderDefinitions :: [Decl] -> Either CompileError [Decl]
orderDefinitions decls = do
  defs <- foldM insertDef Map.empty [decl | decl@DDef {} <- decls]
  traverse_ (checkCalls defs) (Map.toList defs)
  go defs []
  where
    insertDef defs decl@(DDef name _ _ _ _)
      | Map.member name defs = bad ("duplicate definition " <> name)
      | otherwise = Right (Map.insert name decl defs)
    insertDef defs _ = Right defs
    checkCalls defs (name, DDef _ _ _ _ body) =
      case filter (`Map.notMember` defs) (Set.toList (exprCalls body)) of
        missing : _ -> bad ("unknown definition " <> missing <> " called by " <> name)
        [] -> Right ()
    checkCalls _ _ = Right ()
    go pending ordered
      | Map.null pending = Right ordered
      | null ready = bad ("cyclic definitions: " <> intercalate ", " (Map.keys pending))
      | otherwise = go (foldr Map.delete pending readyNames) (ordered <> ready)
      where
        ready = [decl | decl@(DDef _ _ _ _ body) <- Map.elems pending,
          Set.null (Set.intersection (exprCalls body) (Map.keysSet pending))]
        readyNames = [name | DDef name _ _ _ _ <- ready]

exprCalls :: Expr -> Set.Set String
exprCalls (ECall name argument) = Set.insert name (exprCalls argument)
exprCalls (EPair x y) = exprCalls x `Set.union` exprCalls y
exprCalls (ELet _ _ value body) = exprCalls value `Set.union` exprCalls body
exprCalls (ECopy value) = exprCalls value
exprCalls (ESuc value) = exprCalls value
exprCalls (EAdd value) = exprCalls value
exprCalls (EIter _ seed step) = Set.insert step (exprCalls seed)
exprCalls (EFold input seed step) =
  Set.insert step (exprCalls input `Set.union` exprCalls seed)
exprCalls (EWhile _ seed test step) =
  Set.insert test (Set.insert step (exprCalls seed))
exprCalls (EPrepend _ value) = exprCalls value
exprCalls (ELeft value) = exprCalls value
exprCalls (ERight value) = exprCalls value
exprCalls (EMatchText value arms _ fallback) = branchCalls value arms fallback
exprCalls (EMatchNat value arms _ fallback) = branchCalls value arms fallback
exprCalls (ECase value arms) = exprCalls value `Set.union` Set.unions (fmap (exprCalls . snd) arms)
exprCalls _ = Set.empty

branchCalls :: Expr -> [(a, Expr)] -> Expr -> Set.Set String
branchCalls value arms fallback =
  exprCalls value `Set.union` Set.unions (exprCalls fallback : fmap (exprCalls . snd) arms)

containsIter :: Expr -> Bool
containsIter = not . Set.null . iterSteps

iterSteps :: Expr -> Set.Set String
iterSteps (EIter _ seed step) = Set.insert step (iterSteps seed)
iterSteps (EFold input seed step) =
  Set.insert step (iterSteps input `Set.union` iterSteps seed)
iterSteps (EWhile _ seed test step) =
  Set.insert test (Set.insert step (iterSteps seed))
iterSteps (EPair x y) = iterSteps x `Set.union` iterSteps y
iterSteps (ELet _ _ value body) = iterSteps value `Set.union` iterSteps body
iterSteps (ECall _ argument) = iterSteps argument
iterSteps (ECopy value) = iterSteps value
iterSteps (ESuc value) = iterSteps value
iterSteps (EAdd value) = iterSteps value
iterSteps (EPrepend _ value) = iterSteps value
iterSteps (ELeft value) = iterSteps value
iterSteps (ERight value) = iterSteps value
iterSteps (EMatchText value arms _ fallback) = branchIters value arms fallback
iterSteps (EMatchNat value arms _ fallback) = branchIters value arms fallback
iterSteps (ECase value arms) =
  iterSteps value `Set.union` Set.unions (fmap (iterSteps . snd) arms)
iterSteps _ = Set.empty

branchIters :: Expr -> [(a, Expr)] -> Expr -> Set.Set String
branchIters value arms fallback =
  iterSteps value `Set.union` Set.unions (iterSteps fallback : fmap (iterSteps . snd) arms)

freeVars :: Expr -> Set.Set String
freeVars (EVar name) = Set.singleton name
freeVars (EPair x y) = freeVars x `Set.union` freeVars y
freeVars (ELet pat _ value body) =
  freeVars value `Set.union` (freeVars body Set.\\ patternNames pat)
freeVars (ECall _ argument) = freeVars argument
freeVars (ECopy value) = freeVars value
freeVars (ESuc value) = freeVars value
freeVars (EAdd value) = freeVars value
freeVars (EIter _ seed _) = freeVars seed
freeVars (EFold input seed _) = freeVars input `Set.union` freeVars seed
freeVars (EWhile _ seed _ _) = freeVars seed
freeVars (EPrepend _ value) = freeVars value
freeVars (ELeft value) = freeVars value
freeVars (ERight value) = freeVars value
freeVars (EMatchText value arms pat fallback) = branchVars value arms pat fallback
freeVars (EMatchNat value arms pat fallback) = branchVars value arms pat fallback
freeVars (ECase value arms) =
  freeVars value `Set.union` Set.unions (fmap (freeVars . snd) arms)
freeVars _ = Set.empty

branchVars :: Expr -> [(a, Expr)] -> Pattern -> Expr -> Set.Set String
branchVars value arms pat fallback = freeVars value `Set.union`
  Set.unions ((freeVars fallback Set.\\ patternNames pat) : fmap (freeVars . snd) arms)

patternNames :: Pattern -> Set.Set String
patternNames (PVar name)    = Set.singleton name
patternNames PWild          = Set.empty
patternNames (PTuple names) = Set.fromList names

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
    Nothing   -> bad ("constructor " <> name <> " requires its data type")
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
elaborate tables env SUNat (ESuc value) = do
  Elab actual rest input <- elaborate tables env SUNat value
  Refl <- requireSame SUNat actual
  pure (Elab SUNat rest ((USuc :****: UId) :..: input))
elaborate tables env SUNat (EAdd value) = do
  let pairTy = SUProd SUNat SUNat
  Elab actual rest input <- elaborate tables env pairTy value
  Refl <- requireSame pairTy actual
  pure (Elab SUNat rest ((UAdd :****: UId) :..: input))
elaborate tables env expected (EIter count seed stepName) = do
  SomeDef stepIn stepOut step <- lookupDef tables stepName
  Refl <- requireSame expected stepIn
  Refl <- requireSame expected stepOut
  Elab actual rest input <- elaborate tables env expected seed
  Refl <- requireSame expected actual
  pure (Elab expected rest
    ((UIter step :****: UId)
      :..: ((UConst count :****: UId) :****: UId)
      :..: (ULunit :****: UId) :..: input))
elaborate tables env expected (EFold input seed stepName) = do
  SomeDef stepIn stepOut step <- lookupDef tables stepName
  case stepIn of
    SUProd accumulator element -> do
      Refl <- requireSame expected accumulator
      Refl <- requireSame expected stepOut
      let inputsTy = SUList element
      Elab pairActual rest pair <- elaborate tables env
        (SUProd inputsTy accumulator) (EPair input seed)
      Refl <- requireSame (SUProd inputsTy accumulator) pairActual
      pure (Elab accumulator rest ((UFold step :****: UId) :..: pair))
    _ -> bad "fold step must accept accumulator * element"
elaborate tables env expected (EWhile limit seed testName stepName) = do
  SomeDef testIn testOut test <- lookupDef tables testName
  SomeDef stepIn stepOut step <- lookupDef tables stepName
  Refl <- requireSame expected testIn
  Refl <- requireSame expected stepIn
  Refl <- requireSame expected stepOut
  Refl <- requireSame testOut (SUSum SUUnit SUUnit)
  Elab pairActual rest pair <- elaborate tables env
    (SUProd SUNat expected) (EPair (ENat limit) seed)
  Refl <- requireSame (SUProd SUNat expected) pairActual
  pure (Elab expected rest ((UWhile expected test step :****: UId) :..: pair))
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
      Nothing              -> bad ("unknown constructor " <> name)
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
