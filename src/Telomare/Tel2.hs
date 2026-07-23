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
import qualified Telomare.Compiler.Closed as Closed
import Telomare.Compiler.Direct
import Telomare.Core (Ground, Morph (..), STy (..), Ty (..), groundOfSTy)
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
  | TArrow Type Type
  | TReply Type
  deriving (Eq, Show)

data Pattern = PVar String | PWild | PTuple [String]
  deriving (Eq, Show)

-- | Shape of the first arm of a @case@, which picks its dispatch.
data ArmShape = ArmText | ArmNat | ArmCon

data Expr
  = EVar String
  | EUnit
  | ENat Natural
  | EText String
  | ECon String
  | EPair Expr Expr
  | ELet Pattern (Maybe Type) Expr Expr
  | ECall String Expr
  | ECopy Expr
  | ESuc Expr
  | EAdd Expr
  | ENil
  | ECons Expr Expr
  | EMap Expr String
  | EIter Expr Expr String
  | EFold Expr Expr String
  | EWhile Expr Expr String String
  | EPrepend String Expr
  | ELeft Expr
  | ERight Expr
  | EMatchText Expr [(String, Expr)] Pattern Expr
  | EMatchNat Expr [(Natural, Expr)] Pattern Expr
  | ECase Expr [(String, Expr)]
  | ELam Pattern Expr
  | EApply Expr Expr
  | EMapC Expr Expr
  | EIterC Expr Expr Expr
  | EFoldC Expr Expr Expr
  | EWhileC Expr Expr Expr Expr
  -- | Juxtaposition application @f x@. Exists only between parsing and
  -- 'resolveApps', which rewrites every occurrence to ECall or EApply.
  | EApp Expr Expr
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

-- | Within-line space: spaces, tabs, and comments — never a newline.
-- Every token consumes this as trailing space, so a token at the start of
-- a line is only reached through an explicit layout point ('scn'). That is
-- what lets indentation delimit declarations, let bindings, and case arms.
spaceConsumer :: Parser ()
spaceConsumer =
  L.space (void (some (char ' ' <|> char '\t'))) lineComment blockComment

-- | A layout point: whitespace including newlines.
scn :: Parser ()
scn = L.space space1 lineComment blockComment

lineComment :: Parser ()
lineComment = L.skipLineComment "--"

blockComment :: Parser ()
blockComment = L.skipBlockCommentNested "{-" "-}"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceConsumer

symbol :: String -> Parser String
symbol = L.symbol spaceConsumer

-- | Excluded from identifiers so juxtaposition application stops at keywords
-- (otherwise @let a: T = f x in ...@ would consume @in@ as an argument).
reservedWords :: Set.Set String
reservedWords = Set.fromList
  [ "module", "import", "type", "data", "def"
  , "let", "in", "if", "then", "else"
  , "matchText", "matchNat", "case", "of"
  , "map", "mapc", "iterc", "foldc", "whilec", "iterate", "fold", "while"
  , "from", "with", "testing", "stepping"
  , "copy", "onto"
  , "left", "right"
  ]

identifier :: Parser String
identifier = lexeme . try $ do
  name <- (:) <$> letterChar <*> many (alphaNumChar <|> char '_')
  if name `Set.member` reservedWords
    then fail ("keyword " <> name <> " cannot be an identifier")
    else pure name

reserved :: String -> Parser ()
reserved word =
  lexeme (try (string word *> notFollowedBy (alphaNumChar <|> char '_')))

stringLiteral :: Parser String
stringLiteral = lexeme (char '"' *> manyTill L.charLiteral (char '"'))

natural :: Parser Natural
natural = lexeme L.decimal

typeParser :: Parser Type
typeParser = makeArrow
  where
    makeArrow = chainRight makeSum "-o" TArrow
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
  [ try lamExpr
  , try letExpr
  , try mapcExpr
  , try itercExpr
  , try foldcExpr
  , try whilecExpr
  , try matchTextExpr
  , try matchNatExpr
  , try caseExpr
  , try ifExpr
  , try mapExpr
  , try iterExpr
  , try foldExpr
  , try whileExpr
  , try copyExpr
  , try sucExpr
  , try addExpr
  , try consExpr
  , try prependExpr
  , try leftExpr
  , try rightExpr
  , appExpr
  ]
  where
    -- Juxtaposition application is a line fold: arguments continue on
    -- later lines only when indented past the head of the application.
    -- That is what ends a declaration body — the next declaration starts
    -- at column 1 and cannot be a continuation argument.
    appExpr = L.lineFold scn $ \sc' -> do
      function <- atomExpr
      args <- many (try (sc' *> atomExpr))
      pure (foldl EApp function args)
    letExpr = do
      reserved "let"
      scn
      bindings <- some letBinding
      reserved "in"
      scn
      body <- exprParser
      pure (foldr (\(pat, ty, value) rest -> ELet pat ty value rest) body bindings)
    letBinding = try $ do
      pat <- patternParser
      ty <- optional (symbol ":" *> typeParser)
      void (symbol "=")
      scn
      value <- exprParser
      scn
      void (optional (symbol ";"))
      scn
      pure (pat, ty, value)
    ifExpr = do
      reserved "if"
      scn
      condition <- exprParser
      scn
      reserved "then"
      scn
      whenTrue <- exprParser
      scn
      reserved "else"
      scn
      whenFalse <- exprParser
      pure (EMatchNat condition [(0, whenFalse)] PWild whenTrue)
    matchTextExpr = do
      reserved "matchText"
      scn
      value <- exprParser
      scn
      reserved "of"
      scn
      (arms, pat, fallback) <- matchArms stringLiteral
      pure (EMatchText value arms pat fallback)
    matchNatExpr = do
      reserved "matchNat"
      scn
      value <- exprParser
      scn
      reserved "of"
      scn
      (arms, pat, fallback) <- matchArms natural
      pure (EMatchNat value arms pat fallback)
    -- One case form, as in telomare0: the shape of the first arm picks the
    -- dispatch — string literals match text, nat literals match naturals
    -- (both keep the binding default arm), constructor tags eliminate a
    -- data enum (exhaustive, no default).
    caseExpr = do
      reserved "case"
      scn
      value <- exprParser
      scn
      reserved "of"
      scn
      kind <- lookAhead (optional (symbol "{") *> scn *> armShape)
      case kind of
        ArmText -> do
          (arms, pat, fallback) <- matchArms stringLiteral
          pure (EMatchText value arms pat fallback)
        ArmNat -> do
          (arms, pat, fallback) <- matchArms natural
          pure (EMatchNat value arms pat fallback)
        ArmCon -> ECase value <$> enumArms
    armShape = choice
      [ ArmText <$ try stringLiteral
      , ArmNat <$ try natural
      , do name <- identifier
           if startsUpper name
             then pure ArmCon
             else fail "case needs at least one literal or constructor arm"
      ]
    -- Keyed arms plus a binding default, either braced with semicolons
    -- (transitional) or layout-aligned like telomare0.
    matchArms :: Parser key -> Parser ([(key, Expr)], Pattern, Expr)
    matchArms keyParser = bracedArms <|> alignedArms
      where
        bracedArms = do
          void (symbol "{")
          scn
          arms <- many (try $ do key <- keyParser; void (symbol "->"); scn
                                 body <- exprParser; scn; void (symbol ";"); scn
                                 pure (key, body))
          pat <- patternParser
          void (symbol "->")
          scn
          fallback <- exprParser
          scn
          void (optional (symbol ";"))
          scn
          void (symbol "}")
          pure (arms, pat, fallback)
        alignedArms = do
          lvl <- L.indentLevel
          arms <- many (try $ do
            atLevel lvl
            key <- keyParser
            void (symbol "->")
            scn
            body <- exprParser
            scn
            void (optional (symbol ";"))
            scn
            pure (key, body))
          atLevel lvl
          pat <- patternParser
          void (symbol "->")
          scn
          fallback <- exprParser
          pure (arms, pat, fallback)
    enumArms = bracedEnum <|> alignedEnum
      where
        bracedEnum = between (symbol "{" <* scn) (symbol "}") (some bracedArm)
        bracedArm = do
          con <- identifier
          void (symbol "->")
          scn
          body <- exprParser
          scn
          void (optional (symbol ";"))
          scn
          pure (con, body)
        alignedEnum = do
          lvl <- L.indentLevel
          some (try $ do
            atLevel lvl
            con <- identifier
            void (symbol "->")
            scn
            body <- exprParser
            scn
            void (optional (symbol ";"))
            scn
            pure (con, body))
    atLevel lvl = do
      pos <- L.indentLevel
      if pos == lvl then pure () else fail "expected an arm at the same indentation"
    mapExpr = do
      reserved "map"
      scn
      input <- exprParser
      scn
      reserved "with"
      scn
      EMap input <$> identifier
    mapcExpr = do
      reserved "mapc"
      scn
      input <- exprParser
      scn
      reserved "with"
      scn
      EMapC input <$> exprParser
    itercExpr = do
      reserved "iterc"
      scn
      count <- exprParser
      scn
      reserved "from"
      scn
      seed <- exprParser
      scn
      reserved "with"
      scn
      EIterC count seed <$> exprParser
    foldcExpr = do
      reserved "foldc"
      scn
      input <- exprParser
      scn
      reserved "from"
      scn
      seed <- exprParser
      scn
      reserved "with"
      scn
      EFoldC input seed <$> exprParser
    whilecExpr = do
      reserved "whilec"
      scn
      limit <- exprParser
      scn
      reserved "from"
      scn
      seed <- exprParser
      scn
      reserved "testing"
      scn
      test <- exprParser
      scn
      reserved "stepping"
      scn
      EWhileC limit seed test <$> exprParser
    iterExpr = do
      reserved "iterate"
      scn
      count <- exprParser
      scn
      reserved "from"
      scn
      seed <- exprParser
      scn
      reserved "with"
      scn
      EIter count seed <$> identifier
    foldExpr = do
      reserved "fold"
      scn
      input <- exprParser
      scn
      reserved "from"
      scn
      seed <- exprParser
      scn
      reserved "with"
      scn
      EFold input seed <$> identifier
    whileExpr = do
      reserved "while"
      scn
      limit <- exprParser
      scn
      reserved "from"
      scn
      seed <- exprParser
      scn
      reserved "testing"
      scn
      test <- identifier
      scn
      reserved "stepping"
      scn
      EWhile limit seed test <$> identifier
    lamExpr = do
      void (symbol "\\")
      pats <- some patternParser
      void (symbol "->")
      scn
      body <- exprParser
      pure (foldr ELam body pats)
    copyExpr = reserved "copy" *> (ECopy <$> exprParser)
    sucExpr = reserved "suc" *> (ESuc <$> exprParser)
    addExpr = reserved "add" *> (EAdd <$> exprParser)
    consExpr = do
      reserved "cons"
      scn
      value <- exprParser
      scn
      reserved "onto"
      scn
      ECons value <$> exprParser
    prependExpr = reserved "prepend" *> (EPrepend <$> stringLiteral <*> exprParser)
    leftExpr = reserved "left" *> (ELeft <$> exprParser)
    rightExpr = reserved "right" *> (ERight <$> exprParser)
    atomExpr = choice
      [ try (symbol "()" $> EUnit)
      , listExpr
      , parensExpr
      , EText <$> stringLiteral
      , ENat <$> natural
      , do name <- identifier
           pure (if startsUpper name then ECon name else EVar name)
      ]
    listExpr = do
      void (symbol "[")
      scn
      values <- sepBy (exprParser <* scn) (symbol "," <* scn)
      void (symbol "]")
      pure (foldr ECons ENil values)
    -- Parentheses group and build tuples; newlines are free inside them.
    parensExpr = do
      void (symbol "(")
      scn
      values <- sepBy1 (exprParser <* scn) (symbol "," <* scn)
      void (symbol ")")
      case values of
        [single] -> pure single
        more     -> pure (foldr1 EPair more)

startsUpper :: String -> Bool
startsUpper (c : _) = isAsciiUpper c
startsUpper []      = False

declParser :: Parser Decl
declParser = choice [dataDecl, typeDecl, defDecl, sigDefDecl]
  where
    typeDecl = reserved "type" *> (DType <$> identifier <* symbol "="
      <*> typeParser <* optional (symbol ";"))
    dataDecl = do
      reserved "data"
      name <- identifier
      void (symbol "=")
      names <- sepBy1 identifier (symbol "|")
      void (optional (symbol ";"))
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
      scn
      body <- exprParser
      void (optional (symbol ";"))
      pure (DDef name arg input output body)
    -- telomare0-style top level: @name : A -o B = \x -> body@ — the type
    -- sits where telomare0 puts its refinement annotation, and the body is
    -- a lambda whose first pattern becomes the definition argument.
    sigDefDecl = do
      name <- identifier
      void (symbol ":")
      ty <- typeParser
      void (symbol "=")
      scn
      body <- exprParser
      void (optional (symbol ";"))
      case ty of
        TArrow input output -> case body of
          ELam (PVar arg) inner -> pure (DDef name arg input output inner)
          ELam pat inner ->
            let arg = "%arg%" <> name
            in pure (DDef name arg input output
                 (ELet pat Nothing (EVar arg) inner))
          _ -> fail ("top-level definition " <> name
                 <> " must be a lambda; bind constants in a let")
        _ -> fail ("top-level definition " <> name
               <> " needs an arrow type; bind constants in a let")

sourceParser :: Parser Source
sourceParser = scn *> (Source <$> optional moduleHeader <*> many importDecl
  <*> many (declParser <* scn)) <* eof
  where
    moduleHeader = reserved "module" *> identifier <* optional (symbol ";") <* scn
    importDecl = reserved "import" *> identifier <* optional (symbol ";") <* scn

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
compileDecls parsedDecls = expandMain parsedDecls >>= compileExpanded

-- | telomare0-style entry sugar: when neither @init@ nor @step@ is declared
-- and @main@ is, synthesize both from @main : Text * State -> Text * State@
-- (defaulting @type State = Nat;@), halting when the next state is 0. The
-- priced @matchNat@ on the returned state is the honest halt test. The
-- @main@ call is bound with a plain variable so a recursive @main@ still
-- matches the placement path.
expandMain :: [Decl] -> Either CompileError [Decl]
expandMain decls
  | not hasMain = Right decls
  | hasInit || hasStep =
      bad "main cannot be combined with init/step; pick one entry style"
  | replyMain = do
      startExpr <- generalStart
      Right (decls <> [stateDecl | not hasState]
        <> [initReplyDecl startExpr, stepReplyDecl])
  | otherwise = Right (decls <> [stateDecl | not hasState] <> [initDecl, stepDecl])
  where
    defined name = not (null [() | DDef current _ _ _ _ <- decls, current == name])
    hasMain = defined "main"
    hasInit = defined "init"
    hasStep = defined "step"
    hasStart = defined "start"
    hasState = "State" `elem`
      ([name | DType name _ <- decls] <> [name | DData name _ <- decls])
    stateDecl = DType "State" TNat
    -- The general entry: @main : Text * State -o Reply State@ for any
    -- machine State. Freshness is encoded in State by the program itself
    -- (telomare0's state-0 test), supplied by @start : Unit -o State@ —
    -- defaulted to 0 when State is Nat. Halting is main's own left ().
    replyMain = case [output | DDef "main" _ _ output _ <- decls] of
      [TReply _] -> True
      _          -> False
    stateIsNat = not hasState || case [t | DType "State" t <- decls] of
      [TNat] -> True
      _      -> False
    generalStart
      | hasStart = Right (ECall "start" EUnit)
      | stateIsNat = Right (ENat 0)
      | otherwise =
          bad "main returning Reply State needs start : Unit -o State"
    bindCall body = ELet (PVar "pair") Nothing body (EVar "pair")
    initReplyDecl startExpr = DDef "init" "u" TUnit (TReply (TName "State"))
      (bindCall (ECall "main" (EPair (EText "") startExpr)))
    stepReplyDecl = DDef "step" "request" (TProd TText (TName "State"))
      (TReply (TName "State"))
      (bindCall (ECall "main" (EVar "request")))
    reply body = ELet (PVar "pair") Nothing body
      (ELet (PTuple ["text", "s"]) Nothing (EVar "pair")
        (EPair (EVar "text")
          (EMatchNat (EVar "s") [(0, ELeft EUnit)] (PVar "k") (ERight (EVar "k")))))
    initDecl = DDef "init" "u" TUnit (TReply (TName "State"))
      (reply (ECall "main" (EPair (EText "") (ENat 0))))
    stepDecl = DDef "step" "request" (TProd TText (TName "State"))
      (TReply (TName "State"))
      (reply (ECall "main" (EVar "request")))

compileExpanded :: [Decl] -> Either CompileError Program
compileExpanded rawDecls = do
  tablesWithTypes <- foldM addTypeDecl emptyTables decls
  orderedDefs <- orderDefinitions decls
  tables <- foldM addDef tablesWithTypes orderedDefs
  SomeTy stateTy <- resolveType tables (TName "State")
  if firstOrderTy stateTy
    then Right ()
    else bad "machine state must be first-order; closures cannot cross the machine boundary"
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
    decls = fmap resolveDecl rawDecls
    defNames = Set.fromList [name | DDef name _ _ _ _ <- rawDecls]
    resolveDecl (DDef name arg input output body) =
      DDef name arg input output (resolveApps defNames (Set.singleton arg) body)
    resolveDecl decl = decl

-- | Resolve surface applications after parsing: a juxtaposition head (or a
-- call form @f(x)@) naming a local binding applies a closure, an unshadowed
-- definition name is a call — lexical scope wins. No EApp survives this
-- pass, so the elaborator and the placement\/free-variable analyses only
-- ever see ECall and EApply.
resolveApps :: Set.Set String -> Set.Set String -> Expr -> Expr
resolveApps defs = go
  where
    go bound expression = case expression of
      -- Builtin functions, as in telomare0's Prelude names: ordinary
      -- identifiers unless shadowed by a local binding or a definition.
      EApp (EApp (EVar "cons") x) xs
        | builtin bound "cons" -> ECons (go bound x) (go bound xs)
      EApp (EApp (EVar "prepend") (EText prefix)) rest
        | builtin bound "prepend" -> EPrepend prefix (go bound rest)
      EApp (EVar "succ") argument
        | builtin bound "succ" -> ESuc (go bound argument)
      EApp (EVar "add") argument
        | builtin bound "add" -> EAdd (go bound argument)
      EApp (EVar name) argument
        | name `Set.member` bound -> EApply (EVar name) (go bound argument)
        | name `Set.member` defs -> ECall name (go bound argument)
        | otherwise -> EApply (EVar name) (go bound argument)
      EApp function argument -> EApply (go bound function) (go bound argument)
      ECall name argument
        | name `Set.member` bound -> EApply (EVar name) (go bound argument)
        | otherwise -> ECall name (go bound argument)
      EVar {} -> expression
      EUnit -> expression
      ENat {} -> expression
      EText {} -> expression
      ECon {} -> expression
      ENil -> expression
      EPair x y -> EPair (go bound x) (go bound y)
      ELet pat ty value body ->
        ELet pat ty (go bound value) (go (bind pat bound) body)
      ECopy value -> ECopy (go bound value)
      ESuc value -> ESuc (go bound value)
      EAdd value -> EAdd (go bound value)
      ECons value rest -> ECons (go bound value) (go bound rest)
      EMap input mapper -> EMap (go bound input) mapper
      EIter count seed step -> EIter (go bound count) (go bound seed) step
      EFold input seed step -> EFold (go bound input) (go bound seed) step
      EWhile limit seed test step ->
        EWhile (go bound limit) (go bound seed) test step
      EPrepend prefix value -> EPrepend prefix (go bound value)
      ELeft value -> ELeft (go bound value)
      ERight value -> ERight (go bound value)
      EMatchText value arms pat fallback -> EMatchText (go bound value)
        (fmap (fmap (go bound)) arms) pat (go (bind pat bound) fallback)
      EMatchNat value arms pat fallback -> EMatchNat (go bound value)
        (fmap (fmap (go bound)) arms) pat (go (bind pat bound) fallback)
      ECase value arms -> ECase (go bound value) (fmap (fmap (go bound)) arms)
      ELam pat body -> ELam pat (go (bind pat bound) body)
      EApply function argument -> EApply (go bound function) (go bound argument)
      EMapC input mapper -> EMapC (go bound input) (go bound mapper)
      EIterC count seed mapper ->
        EIterC (go bound count) (go bound seed) (go bound mapper)
      EFoldC input seed mapper ->
        EFoldC (go bound input) (go bound seed) (go bound mapper)
      EWhileC limit seed test step ->
        EWhileC (go bound limit) (go bound seed) (go bound test)
          (go bound step)
    bind pat bound = patternNames pat `Set.union` bound
    builtin bound name =
      not (name `Set.member` bound) && not (name `Set.member` defs)

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
        bindingEnv Set.empty outputTy continuation
      Refl <- requireSame outputTy result
      core <- fromDirect (Closed.closedContinueFrom
        (finish continuationRest continuationU) WeakS bindingCore)
      pure (CoreEntry inputTy (SBang (liftSTy outputTy))
        (stripLift outputTy) core)
    [body] -> case compileDirect source of
      Right core ->
        pure (CoreEntry inputTy (liftSTy outputTy) (stripLift outputTy) core)
      Left (RecursionRequiresPlacement _) -> do
        argument <- case [arg | DDef current arg _ _ _ <- decls, current == name] of
          [arg] -> Right arg
          _     -> bad ("missing entry definition " <> name)
        placed <- compilePlacedBody tables decls (Bind argument inputTy Empty) outputTy body
        pure (CoreEntry inputTy (SBang (liftSTy outputTy))
          (stripLift outputTy) (placed :.: RunitS))
      Left err -> fromDirect (Left err)
    _ -> bad ("missing entry definition " <> name)

data SomePlacedDef where
  SomePlacedDef
    :: SUTy a
    -> SUTy b
    -> Morph (Lift a) ('Bang (Lift b))
    -> SomePlacedDef

compilePlacedDef :: Tables -> [Decl] -> String -> Either CompileError SomePlacedDef
compilePlacedDef tables decls name = case
    [decl | decl@(DDef current _ _ _ _) <- decls, current == name] of
  [DDef _ argument input output body] -> do
    if containsIter body || callsRecursiveDef decls body
      then Right ()
      else bad ("definition " <> name <> " does not require placement")
    SomeTy inputTy <- resolveType tables input
    SomeTy outputTy <- resolveType tables output
    core <- compilePlacedBody tables decls (Bind argument inputTy Empty) outputTy body
    pure (SomePlacedDef inputTy outputTy (core :.: RunitS))
  _ -> bad ("unknown definition " <> name)

compilePlacedBody
  :: Tables
  -> [Decl]
  -> Env c
  -> SUTy output
  -> Expr
  -> Either CompileError (Morph (Lift c) ('Bang (Lift output)))
compilePlacedBody tables decls env output expression = case expression of
  ELet (PVar binder) annotation loop body | isClosedLoop loop -> do
    SomeTy resultTy <- resolveAnnotation tables env annotation loop
    SomePlacedLoop actualTy loopCore <- compileAffineLoop tables env resultTy loop
    Refl <- requireSame resultTy actualTy
    compilePlacedContinuation tables binder resultTy output body loopCore
  ELet (PVar binder) annotation (ECall name argument) body
    | definitionRequiresPlacement decls name -> do
        SomePlacedDef inputTy actualTy callee <- compilePlacedDef tables decls name
        SomeTy resultTy <- case annotation of
          Just declared -> resolveType tables declared
          Nothing       -> pure (SomeTy actualTy)
        Refl <- requireSame resultTy actualTy
        Elab argumentTy rest argumentU <- elaborate tables env Set.empty inputTy argument
        Refl <- requireSame inputTy argumentTy
        argumentCore <- fromDirect (compileDirect (finish rest argumentU))
        compilePlacedContinuation tables binder resultTy output body
          (callee :.: argumentCore)
  ELet pat annotation value body
    | not (containsIter value || callsRecursiveDef decls value) -> do
        SomeTy valueTy <- resolveAnnotation tables env annotation value
        Elab actual rest valueU <- elaborate tables env Set.empty valueTy value
        Refl <- requireSame valueTy actual
        Bound boundEnv reshape <- bindPattern pat valueTy rest
        prefix <- fromDirect (compileDirect (reshape :..: valueU))
        suffix <- compilePlacedBody tables decls boundEnv output body
        pure (suffix :.: prefix)
  ECall name argument | definitionRequiresPlacement decls name -> do
    SomePlacedDef inputTy resultTy callee <- compilePlacedDef tables decls name
    Refl <- requireSame output resultTy
    Elab argumentTy rest argumentU <- elaborate tables env Set.empty inputTy argument
    Refl <- requireSame inputTy argumentTy
    argumentCore <- fromDirect (compileDirect (finish rest argumentU))
    pure (callee :.: argumentCore)
  loop | isClosedLoop loop -> do
    SomePlacedLoop resultTy loopCore <- compileAffineLoop tables env output loop
    Refl <- requireSame output resultTy
    pure loopCore
  _ -> bad "recursion placement requires an affine controller, a closed seed, and no live context after the loop"

compilePlacedContinuation
  :: Tables
  -> String
  -> SUTy result
  -> SUTy output
  -> Expr
  -> Morph x ('Bang (Lift result))
  -> Either CompileError (Morph x ('Bang (Lift output)))
compilePlacedContinuation tables binder resultTy output body value = do
  if freeVars body `Set.isSubsetOf` Set.singleton binder
    then Right ()
    else bad "unboxed context cannot remain live after recursion"
  Elab actual rest continuation <- elaborate tables (Bind binder resultTy Empty) Set.empty output body
  Refl <- requireSame output actual
  continuationCore <- fromDirect
    (compileDirect (finish rest continuation :..: URunit))
  pure (BoxS continuationCore :.: value)

data SomePlacedLoop c where
  SomePlacedLoop
    :: SUTy a
    -> Morph (Lift c) ('Bang (Lift a))
    -> SomePlacedLoop c

compileAffineLoop
  :: Tables
  -> Env c
  -> SUTy result
  -> Expr
  -> Either CompileError (SomePlacedLoop c)
compileAffineLoop tables env resultTy expression = case expression of
  EMap input mapperName -> do
    SomeDef mapperIn mapperOut mapperU <- lookupDef tables mapperName
    case resultTy of
      SUList resultElement -> do
        Refl <- requireSame resultElement mapperOut
        Elab inputTy rest inputU <- elaborate tables env Set.empty (SUList mapperIn) input
        Refl <- requireSame (SUList mapperIn) inputTy
        core <- fromDirect
          (Closed.affineMapValueFrom (finish rest inputU) mapperU)
        pure (SomePlacedLoop resultTy core)
      _ -> bad "map result must be a list"
  EMapC input mapper -> case resultTy of
    SUList resultElement -> do
      SomeTy inputListTy <- synthType tables env input
      case inputListTy of
        SUList elementTy -> do
          Elab inputActual rest inputU <- elaborate tables env
            (freeVars mapper) (SUList elementTy) input
          Refl <- requireSame (SUList elementTy) inputActual
          inputCore <- fromDirect (compileDirect inputU)
          selector <- promoteClosureSelector tables rest
            elementTy resultElement mapper
          pure (SomePlacedLoop resultTy
            (MapCS :.: (selector :***: IdS) :.: SwapS :.: inputCore))
        _ -> bad "mapc expects a list input with an inferable type"
    _ -> bad "mapc result must be a list"
  -- closure-bodied loops (M5): the reusable body is a promoted-closure
  -- selector (mapc's discipline); the Ground seed enters the modality
  -- through PromoteS at the loop boundary.
  EIterC count seed mapper -> do
    ground <- requireGround "iterc seed" seed resultTy
    let pairTy = SUProd SUNat resultTy
    Elab pairActual rest pairU <- elaborate tables env (freeVars mapper)
      pairTy (EPair count seed)
    Refl <- requireSame pairTy pairActual
    pairCore <- fromDirect (compileDirect pairU)
    selector <- promoteClosureSelector tables rest resultTy resultTy mapper
    pure (SomePlacedLoop resultTy
      (IterCS :.: (selector :***: (IdS :***: PromoteS ground))
        :.: SwapS :.: pairCore))
  EFoldC input seed mapper -> do
    ground <- requireGround "foldc seed" seed resultTy
    SomeTy inputListTy <- synthType tables env input
    case inputListTy of
      SUList elementTy -> do
        let pairTy = SUProd (SUList elementTy) resultTy
        Elab pairActual rest pairU <- elaborate tables env (freeVars mapper)
          pairTy (EPair input seed)
        Refl <- requireSame pairTy pairActual
        pairCore <- fromDirect (compileDirect pairU)
        selector <- promoteClosureSelector tables rest
          (SUProd resultTy elementTy) resultTy mapper
        pure (SomePlacedLoop resultTy
          (FoldCS :.: (selector :***: (IdS :***: PromoteS ground))
            :.: SwapS :.: pairCore))
      _ -> bad "foldc expects a list input with an inferable type"
  EWhileC limit seed test step -> do
    ground <- requireGround "whilec seed" seed resultTy
    if Set.null (freeVars step)
      then Right ()
      else bad "whilec's stepping selector must be closed"
    let pairTy = SUProd SUNat resultTy
    Elab pairActual rest pairU <- elaborate tables env (freeVars test)
      pairTy (EPair limit seed)
    Refl <- requireSame pairTy pairActual
    pairCore <- fromDirect (compileDirect pairU)
    testSel <- promoteClosureSelector tables rest resultTy
      (SUSum SUUnit SUUnit) test
    stepSel <- promoteClosureSelector tables Empty resultTy resultTy step
    pure (SomePlacedLoop resultTy
      (WhileCS (liftSTy resultTy)
        :.: (testSel :***:
              ((stepSel :***: (IdS :***: PromoteS ground)) :.: LunitS))
        :.: SwapS :.: pairCore))
  EIter count seed stepName -> do
    SomeDef stepIn stepOut stepU <- lookupDef tables stepName
    Refl <- requireSame resultTy stepIn
    Refl <- requireSame resultTy stepOut
    if closedSeed seed
      then do
        Elab countTy rest countU <- elaborate tables env Set.empty SUNat count
        Refl <- requireSame SUNat countTy
        seedU <- elaborateClosed tables resultTy seed
        core <- fromDirect
          (Closed.affineIterValueFrom (finish rest countU) seedU stepU)
        pure (SomePlacedLoop resultTy core)
      else do
        ground <- requireGround "iteration seed" seed resultTy
        let pairTy = SUProd SUNat resultTy
        Elab pairActual rest pairU <- elaborate tables env Set.empty pairTy
          (EPair count seed)
        Refl <- requireSame pairTy pairActual
        core <- fromDirect
          (Closed.affineIterOpenFrom ground (finish rest pairU) stepU)
        pure (SomePlacedLoop resultTy core)
  EFold input seed stepName -> do
    SomeDef stepIn stepOut stepU <- lookupDef tables stepName
    case stepIn of
      SUProd accumulator element -> do
        Refl <- requireSame resultTy accumulator
        Refl <- requireSame resultTy stepOut
        if closedSeed seed
          then do
            Elab inputTy rest inputU <- elaborate tables env Set.empty (SUList element) input
            Refl <- requireSame (SUList element) inputTy
            seedU <- elaborateClosed tables accumulator seed
            core <- fromDirect
              (Closed.affineFoldValueFrom (finish rest inputU) seedU stepU)
            pure (SomePlacedLoop accumulator core)
          else do
            ground <- requireGround "fold seed" seed accumulator
            let pairTy = SUProd (SUList element) accumulator
            Elab pairActual rest pairU <- elaborate tables env Set.empty pairTy
              (EPair input seed)
            Refl <- requireSame pairTy pairActual
            core <- fromDirect
              (Closed.affineFoldOpenFrom ground (finish rest pairU) stepU)
            pure (SomePlacedLoop accumulator core)
      _ -> bad "fold step must accept accumulator * element"
  EWhile limit seed testName stepName -> do
    SomeDef testIn testOut testU <- lookupDef tables testName
    SomeDef stepIn stepOut stepU <- lookupDef tables stepName
    Refl <- requireSame resultTy testIn
    Refl <- requireSame resultTy stepIn
    Refl <- requireSame resultTy stepOut
    Refl <- requireSame testOut (SUSum SUUnit SUUnit)
    if closedSeed seed
      then do
        Elab limitTy rest limitU <- elaborate tables env Set.empty SUNat limit
        Refl <- requireSame SUNat limitTy
        seedU <- elaborateClosed tables resultTy seed
        core <- fromDirect (Closed.affineWhileValueFrom resultTy
          (finish rest limitU) seedU testU stepU)
        pure (SomePlacedLoop resultTy core)
      else do
        ground <- requireGround "while seed" seed resultTy
        let pairTy = SUProd SUNat resultTy
        Elab pairActual rest pairU <- elaborate tables env Set.empty pairTy
          (EPair limit seed)
        Refl <- requireSame pairTy pairActual
        core <- fromDirect (Closed.affineWhileOpenFrom resultTy ground
          (finish rest pairU) testU stepU)
        pure (SomePlacedLoop resultTy core)
  _ -> bad "expected recursion with an affine controller"
  where
    closedSeed value = Set.null (freeVars value) && not (containsIter value)
    -- R2: an open seed is promoted at the loop boundary when its type is
    -- Ground (bang- and arrow-free first-order data) — design/PROMOTE.md.
    requireGround :: String -> Expr -> SUTy a
                  -> Either CompileError (Ground (Lift a))
    requireGround description value ty
      | containsIter value =
          bad (description <> " cannot contain recursion")
      | otherwise = case groundOfSTy (liftSTy ty) of
          Just ground -> Right ground
          Nothing -> bad (description
            <> " must be closed or promotable first-order data;"
            <> " closures cannot be promoted")

-- | Compile a reusable-mapper expression to a promoted closure selector:
-- closed lambdas at the leaves (each promoted by empty-context BoxValS),
-- runtime dispatch via matchNat\/case over an affine scrutinee.  This is
-- the only way to form the Bang (Lolly a b) that MapCS needs — no general
-- promotion of an already-selected closure exists.
promoteClosureSelector
  :: Tables
  -> Env r
  -> SUTy a
  -> SUTy b
  -> Expr
  -> Either CompileError
       (Morph (Lift r) ('Bang ('Lolly (Lift a) (Lift b))))
promoteClosureSelector tables env a b expression = case expression of
  ELam _ _ | Set.null (freeVars expression) -> do
    leafCore <- leaf expression
    pure (BoxValS leafCore :.: WeakS)
  EMatchNat scrutinee arms fallbackPat fallback
    | all (Set.null . freeVars . snd) arms
        && Set.null (freeVars fallback Set.\\ patternNames fallbackPat) -> do
        Elab keyActual rest scrutU <- elaborate tables env Set.empty
          SUNat scrutinee
        Refl <- requireSame SUNat keyActual
        scrutCore <- fromDirect (compileDirect (finish rest scrutU))
        dispatch <- dispatchNat arms fallback
        pure (dispatch :.: scrutCore)
  EMatchText scrutinee arms fallbackPat fallback
    | all (Set.null . freeVars . snd) arms
        && Set.null (freeVars fallback Set.\\ patternNames fallbackPat) -> do
        Elab keyActual rest scrutU <- elaborate tables env Set.empty
          (SUList SUNat) scrutinee
        Refl <- requireSame (SUList SUNat) keyActual
        scrutCore <- fromDirect (compileDirect (finish rest scrutU))
        dispatch <- dispatchText arms fallback
        pure (dispatch :.: scrutCore)
  ECase scrutinee arms -> do
    resolved <- traverse resolveArm arms
    let typeNames = [typeName | (typeName, _, _) <- resolved]
        armNames = fmap fst arms
    case resolved of
      [] -> bad "case has no arms"
      ((typeName, _, _) : _)
        | any (/= typeName) typeNames ->
            bad "case mixes constructors from different data types"
        | not (unique armNames) -> bad "case repeats a constructor"
        | length resolved /= constructorCount tables typeName ->
            bad ("case is not exhaustive for " <> typeName)
        | otherwise ->
            let tagged = [(tag, body) | (_, tag, body) <- resolved]
            in promoteClosureSelector tables env a b
                 (EMatchNat scrutinee (init tagged) PWild (snd (last tagged)))
  _ -> bad "a reusable mapper must select among closed lambdas"
  where
    resolveArm (name, body) = case Map.lookup name (constructors tables) of
      Nothing              -> bad ("unknown constructor " <> name)
      Just (typeName, tag) -> Right (typeName, tag, body)
    leaf lambda = do
      lamU <- elaborateClosed tables (SULolly a b) lambda
      fromDirect (compileDirect lamU)
    dispatchNat [] fallback = do
      fallbackCore <- leaf fallback
      pure (BoxValS fallbackCore :.: WeakS)
    dispatchNat ((literal, arm) : rest) fallback = do
      hit <- leaf arm
      miss <- dispatchNat rest fallback
      partCore <- fromDirect (compileDirect (partitionNatU literal))
      pure (CaseS (BoxValS hit :.: WeakS) miss :.: partCore)
    dispatchText [] fallback = do
      fallbackCore <- leaf fallback
      pure (BoxValS fallbackCore :.: WeakS)
    dispatchText ((literal, arm) : rest) fallback = do
      hit <- leaf arm
      miss <- dispatchText rest fallback
      partCore <- fromDirect (compileDirect (partitionTextU (encode literal)))
      pure (CaseS (BoxValS hit :.: WeakS) miss :.: partCore)

definitionRequiresPlacement :: [Decl] -> String -> Bool
definitionRequiresPlacement decls name = case
  [body | DDef current _ _ _ body <- decls, current == name] of
  [body] -> containsIter body || callsRecursiveDef decls body
  _      -> False

callsRecursiveDef :: [Decl] -> Expr -> Bool
callsRecursiveDef decls expression = any (definitionRequiresPlacement decls)
  (Set.toList (exprCalls expression))

data BindingSpec = BindingSpec String (Maybe Type) Expr

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
isClosedLoop EMap {}   = True
isClosedLoop EMapC {}  = True
isClosedLoop EIterC {} = True
isClosedLoop EFoldC {} = True
isClosedLoop EWhileC {} = True
isClosedLoop _         = False

data SomeClosedLoop where
  SomeClosedLoop
    :: SUTy a
    -> Morph 'Unit ('Bang (Lift a))
    -> SomeClosedLoop

compileClosedLoop :: Tables -> SomeTy -> Expr -> Either CompileError SomeClosedLoop
compileClosedLoop tables (SomeTy resultTy) expression =
  case expression of
    EMap input mapperName -> do
      requireClosed "map input" input
      SomeDef mapperIn mapperOut mapperU <- lookupDef tables mapperName
      case resultTy of
        SUList resultElement -> do
          Refl <- requireSame resultElement mapperOut
          inputU <- elaborateClosed tables (SUList mapperIn) input
          loopCore <- fromDirect (Closed.closedMapValue inputU mapperU)
          pure (SomeClosedLoop resultTy loopCore)
        _ -> bad "map result must be a list"
    EIter count seed stepName -> do
      requireClosed "iteration bound" count
      requireClosed "iteration seed" seed
      SomeDef stepIn stepOut stepU <- lookupDef tables stepName
      Refl <- requireSame resultTy stepIn
      Refl <- requireSame resultTy stepOut
      countU <- elaborateClosed tables SUNat count
      seedU <- elaborateClosed tables resultTy seed
      loopCore <- fromDirect (Closed.closedIterValueFrom countU seedU stepU)
      pure (SomeClosedLoop resultTy loopCore)
    EFold input seed stepName -> do
      requireClosed "fold input" input
      requireClosed "fold seed" seed
      SomeDef stepIn stepOut stepU <- lookupDef tables stepName
      case stepIn of
        SUProd accumulator element -> do
          Refl <- requireSame resultTy accumulator
          Refl <- requireSame resultTy stepOut
          inputU <- elaborateClosed tables (SUList element) input
          seedU <- elaborateClosed tables accumulator seed
          loopCore <- fromDirect (Closed.closedFoldValue inputU seedU stepU)
          pure (SomeClosedLoop accumulator loopCore)
        _ -> bad "fold step must accept accumulator * element"
    EWhile limit seed testName stepName -> do
      requireClosed "while bound" limit
      requireClosed "while seed" seed
      SomeDef testIn testOut testU <- lookupDef tables testName
      SomeDef stepIn stepOut stepU <- lookupDef tables stepName
      Refl <- requireSame resultTy testIn
      Refl <- requireSame resultTy stepIn
      Refl <- requireSame resultTy stepOut
      Refl <- requireSame testOut (SUSum SUUnit SUUnit)
      limitU <- elaborateClosed tables SUNat limit
      seedU <- elaborateClosed tables resultTy seed
      loopCore <- fromDirect
        (Closed.closedWhileValueFrom resultTy limitU seedU testU stepU)
      pure (SomeClosedLoop resultTy loopCore)
    _ -> bad "expected a closed recursive binding"
  where
    requireClosed description value
      | Set.null (freeVars value) && not (containsIter value) = Right ()
      | otherwise = bad (description <> " cannot capture or contain recursion")

elaborateClosed
  :: Tables
  -> SUTy a
  -> Expr
  -> Either CompileError (UMorph 'UUnit a)
elaborateClosed tables ty value = do
  Elab actual rest source <- elaborate tables Empty Set.empty ty value
  Refl <- requireSame ty actual
  pure (finish rest source)

data CompiledBindings where
  CompiledBindings
    :: Env c
    -> STy (Lift c)
    -> Morph 'Unit ('Bang (Lift c))
    -> CompiledBindings

compileBindings :: Tables -> [BindingSpec] -> Either CompileError CompiledBindings
compileBindings _ [] = do
  core <- fromDirect (Closed.closedValue UId)
  pure (CompiledBindings Empty SUnit core)
compileBindings tables (BindingSpec name annotation expression : rest) = do
  declared@(SomeTy declaredTy) <- resolveAnnotation tables Empty annotation expression
  SomeClosedLoop actualTy loopCore <- compileClosedLoop tables declared expression
  Refl <- requireSame declaredTy actualTy
  CompiledBindings env envTy restCore <- compileBindings tables rest
  if envContains name env
    then bad ("duplicate recursive binder " <> name)
    else pure (CompiledBindings (Bind name declaredTy env)
      (SProd (liftSTy declaredTy) envTy)
      (Closed.closedMerge loopCore restCore))

stripLift :: SUTy a -> Strip (Lift a) :~: a
stripLift SUUnit = Refl
stripLift SUNat = Refl
stripLift (SUProd a b) = case (stripLift a, stripLift b) of
  (Refl, Refl) -> Refl
stripLift (SUSum a b) = case (stripLift a, stripLift b) of
  (Refl, Refl) -> Refl
stripLift (SUList a) = case stripLift a of Refl -> Refl

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
  Elab actual _ bodyU <- elaborate tables (Bind arg inputTy Empty) Set.empty outputTy body
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
exprCalls (ECons value rest) = exprCalls value `Set.union` exprCalls rest
exprCalls (EMap input mapper) = Set.insert mapper (exprCalls input)
exprCalls (EIter count seed step) =
  Set.insert step (exprCalls count `Set.union` exprCalls seed)
exprCalls (EFold input seed step) =
  Set.insert step (exprCalls input `Set.union` exprCalls seed)
exprCalls (EWhile limit seed test step) =
  Set.insert test (Set.insert step (exprCalls limit `Set.union` exprCalls seed))
exprCalls (EPrepend _ value) = exprCalls value
exprCalls (ELeft value) = exprCalls value
exprCalls (ERight value) = exprCalls value
exprCalls (EMatchText value arms _ fallback) = branchCalls value arms fallback
exprCalls (EMatchNat value arms _ fallback) = branchCalls value arms fallback
exprCalls (ECase value arms) = exprCalls value `Set.union` Set.unions (fmap (exprCalls . snd) arms)
exprCalls (ELam _ body) = exprCalls body
exprCalls (EApply function argument) =
  exprCalls function `Set.union` exprCalls argument
exprCalls (EMapC input mapper) =
  exprCalls input `Set.union` exprCalls mapper
exprCalls (EIterC count seed mapper) =
  exprCalls count `Set.union` exprCalls seed `Set.union` exprCalls mapper
exprCalls (EFoldC input seed mapper) =
  exprCalls input `Set.union` exprCalls seed `Set.union` exprCalls mapper
exprCalls (EWhileC limit seed test step) = Set.unions
  [exprCalls limit, exprCalls seed, exprCalls test, exprCalls step]
exprCalls _ = Set.empty

branchCalls :: Expr -> [(a, Expr)] -> Expr -> Set.Set String
branchCalls value arms fallback =
  exprCalls value `Set.union` Set.unions (exprCalls fallback : fmap (exprCalls . snd) arms)

containsIter :: Expr -> Bool
containsIter = not . Set.null . iterSteps

iterSteps :: Expr -> Set.Set String
iterSteps (EIter count seed step) =
  Set.insert step (iterSteps count `Set.union` iterSteps seed)
iterSteps (EFold input seed step) =
  Set.insert step (iterSteps input `Set.union` iterSteps seed)
iterSteps (EWhile limit seed test step) =
  Set.insert test (Set.insert step (iterSteps limit `Set.union` iterSteps seed))
iterSteps (EPair x y) = iterSteps x `Set.union` iterSteps y
iterSteps (ELet _ _ value body) = iterSteps value `Set.union` iterSteps body
iterSteps (ECall _ argument) = iterSteps argument
iterSteps (ECopy value) = iterSteps value
iterSteps (ESuc value) = iterSteps value
iterSteps (EAdd value) = iterSteps value
iterSteps (ECons value rest) = iterSteps value `Set.union` iterSteps rest
iterSteps (EMap input mapper) = Set.insert mapper (iterSteps input)
iterSteps (EPrepend _ value) = iterSteps value
iterSteps (ELeft value) = iterSteps value
iterSteps (ERight value) = iterSteps value
iterSteps (EMatchText value arms _ fallback) = branchIters value arms fallback
iterSteps (EMatchNat value arms _ fallback) = branchIters value arms fallback
iterSteps (ECase value arms) =
  iterSteps value `Set.union` Set.unions (fmap (iterSteps . snd) arms)
iterSteps (ELam _ body) = iterSteps body
iterSteps (EApply function argument) =
  iterSteps function `Set.union` iterSteps argument
iterSteps (EMapC input mapper) =
  -- the anonymous runtime mapper marks a recursion site by itself
  Set.insert "mapc" (iterSteps input `Set.union` iterSteps mapper)
iterSteps (EIterC count seed mapper) =
  Set.insert "mapc" (Set.unions [iterSteps count, iterSteps seed, iterSteps mapper])
iterSteps (EFoldC input seed mapper) =
  Set.insert "mapc" (Set.unions [iterSteps input, iterSteps seed, iterSteps mapper])
iterSteps (EWhileC limit seed test step) =
  Set.insert "mapc" (Set.unions
    [iterSteps limit, iterSteps seed, iterSteps test, iterSteps step])
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
freeVars (ECons value rest) = freeVars value `Set.union` freeVars rest
freeVars (EMap input _) = freeVars input
freeVars (EIter count seed _) = freeVars count `Set.union` freeVars seed
freeVars (EFold input seed _) = freeVars input `Set.union` freeVars seed
freeVars (EWhile limit seed _ _) = freeVars limit `Set.union` freeVars seed
freeVars (EPrepend _ value) = freeVars value
freeVars (ELeft value) = freeVars value
freeVars (ERight value) = freeVars value
freeVars (EMatchText value arms pat fallback) = branchVars value arms pat fallback
freeVars (EMatchNat value arms pat fallback) = branchVars value arms pat fallback
freeVars (ECase value arms) =
  freeVars value `Set.union` Set.unions (fmap (freeVars . snd) arms)
freeVars (ELam pat body) = freeVars body Set.\\ patternNames pat
freeVars (EApply function argument) =
  freeVars function `Set.union` freeVars argument
freeVars (EMapC input mapper) = freeVars input `Set.union` freeVars mapper
freeVars (EIterC count seed mapper) = Set.unions
  [freeVars count, freeVars seed, freeVars mapper]
freeVars (EFoldC input seed mapper) = Set.unions
  [freeVars input, freeVars seed, freeVars mapper]
freeVars (EWhileC limit seed test step) = Set.unions
  [freeVars limit, freeVars seed, freeVars test, freeVars step]
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
    go seen (TArrow x y) = do
      SomeTy a <- go seen x
      SomeTy b <- go seen y
      pure (SomeTy (SULolly a b))
    go seen (TReply state) = go seen (TProd TText (TSum TUnit state))
    go seen (TName name)
      | name `elem` seen = bad ("cyclic type alias involving " <> name)
      | otherwise = case Map.lookup name (aliases tables) of
          Nothing -> bad ("unknown type " <> name)
          Just ty -> go (name : seen) ty

-- | The demand set holds the variables the REST of the current execution
-- path will still consume.  A variable looked up while demanded is peeked
-- (left in the environment behind a priced implicit copy) rather than
-- consumed; the last use takes it, so every reuse is charged exactly once
-- per extra use per execution path (spec: T3.Source.Affine's `both`
-- split rule).
elaborate :: Tables -> Env c -> Set.Set String -> SUTy expected -> Expr -> Either CompileError (Elab c)
elaborate _ env demand expected (EVar name) = do
  Taken actual rest morph <-
    if name `Set.member` demand then peekVar name env else takeVar name env
  case actual of
    SULolly _ _ | name `Set.member` demand ->
      bad ("function " <> name
        <> " cannot be implicitly copied; a closure is applied at most once")
    _ -> Right ()
  Refl <- requireSame expected actual
  pure (Elab expected rest morph)
elaborate _ env _ SUUnit EUnit = pure (constant env SUUnit UId)
elaborate _ env _ SUNat (ENat n) = pure (constant env SUNat (UConst n))
elaborate _ env _ (SUList SUNat) (EText text) =
  pure (constant env (SUList SUNat) (textU (encode text)))
elaborate tables env _ expected (ECon name) = case Map.lookup name (constructors tables) of
  Nothing -> bad ("unknown constructor " <> name)
  Just (_, tag) -> case sameTy expected SUNat of
    Just Refl -> pure (constant env SUNat (UConst tag))
    Nothing   -> bad ("constructor " <> name <> " requires its data type")
elaborate tables env demand (SUProd a b) (EPair x y) = do
  Elab ax rest first <- elaborate tables env
    (demand `Set.union` freeVars y) a x
  Refl <- requireSame a ax
  Elab by rest' second <- elaborate tables rest demand b y
  Refl <- requireSame b by
  pure (Elab (SUProd a b) rest'
    (UUnassoc :..: (UId :****: second) :..: first))
elaborate tables env demand expected (ELet pat annotation value body) = do
  SomeTy valueTy <- resolveAnnotation tables env annotation value
  Elab actual rest first <- elaborate tables env
    (demand `Set.union` (freeVars body Set.\\ patternNames pat)) valueTy value
  Refl <- requireSame valueTy actual
  Bound boundEnv reshape <- bindPattern pat valueTy rest
  Elab result rest' second <- elaborate tables boundEnv demand expected body
  Refl <- requireSame expected result
  pure (Elab expected rest' (second :..: reshape :..: first))
elaborate tables env demand expected (ECall name argument) = do
  SomeDef input output function <- lookupDef tables name
  Refl <- requireSame expected output
  Elab actual rest arg <- elaborate tables env demand input argument
  Refl <- requireSame input actual
  pure (Elab output rest ((function :****: UId) :..: arg))
elaborate tables env demand (SUProd a b) (ECopy value) = do
  Refl <- requireSame a b
  case a of
    SULolly _ _ -> bad "cannot copy a function; closure reuse is not permitted"
    _           -> Right ()
  Elab actual rest input <- elaborate tables env demand a value
  Refl <- requireSame a actual
  pure (Elab (SUProd a a) rest ((copyMorph a :****: UId) :..: input))
elaborate tables env demand SUNat (ESuc value) = do
  Elab actual rest input <- elaborate tables env demand SUNat value
  Refl <- requireSame SUNat actual
  pure (Elab SUNat rest ((USuc :****: UId) :..: input))
elaborate tables env demand SUNat (EAdd value) = do
  let pairTy = SUProd SUNat SUNat
  Elab actual rest input <- elaborate tables env demand pairTy value
  Refl <- requireSame pairTy actual
  pure (Elab SUNat rest ((UAdd :****: UId) :..: input))
elaborate _ env _ expected@(SUList _) ENil =
  pure (constant env expected UNil)
elaborate tables env demand expected@(SUList element) (ECons value rest) = do
  Elab actual remaining pair <- elaborate tables env demand
    (SUProd element expected) (EPair value rest)
  Refl <- requireSame (SUProd element expected) actual
  pure (Elab expected remaining ((UCons :****: UId) :..: pair))
elaborate tables env demand expected@(SUList resultElement) (EMap input mapperName) = do
  SomeDef mapperIn mapperOut mapper <- lookupDef tables mapperName
  Refl <- requireSame resultElement mapperOut
  Elab actual rest inputU <- elaborate tables env demand (SUList mapperIn) input
  Refl <- requireSame (SUList mapperIn) actual
  pure (Elab expected rest ((UMap mapper :****: UId) :..: inputU))
elaborate tables env demand expected (EIter count seed stepName) = do
  SomeDef stepIn stepOut step <- lookupDef tables stepName
  Refl <- requireSame expected stepIn
  Refl <- requireSame expected stepOut
  Elab pairActual rest pair <- elaborate tables env demand
    (SUProd SUNat expected) (EPair count seed)
  Refl <- requireSame (SUProd SUNat expected) pairActual
  pure (Elab expected rest ((UIter step :****: UId) :..: pair))
elaborate tables env demand expected (EFold input seed stepName) = do
  SomeDef stepIn stepOut step <- lookupDef tables stepName
  case stepIn of
    SUProd accumulator element -> do
      Refl <- requireSame expected accumulator
      Refl <- requireSame expected stepOut
      let inputsTy = SUList element
      Elab pairActual rest pair <- elaborate tables env demand
        (SUProd inputsTy accumulator) (EPair input seed)
      Refl <- requireSame (SUProd inputsTy accumulator) pairActual
      pure (Elab accumulator rest ((UFold step :****: UId) :..: pair))
    _ -> bad "fold step must accept accumulator * element"
elaborate tables env demand expected (EWhile limit seed testName stepName) = do
  SomeDef testIn testOut test <- lookupDef tables testName
  SomeDef stepIn stepOut step <- lookupDef tables stepName
  Refl <- requireSame expected testIn
  Refl <- requireSame expected stepIn
  Refl <- requireSame expected stepOut
  Refl <- requireSame testOut (SUSum SUUnit SUUnit)
  Elab pairActual rest pair <- elaborate tables env demand
    (SUProd SUNat expected) (EPair limit seed)
  Refl <- requireSame (SUProd SUNat expected) pairActual
  pure (Elab expected rest ((UWhile expected test step :****: UId) :..: pair))
elaborate tables env demand (SUList SUNat) (EPrepend prefix suffix) = do
  Elab actual rest input <- elaborate tables env demand (SUList SUNat) suffix
  Refl <- requireSame (SUList SUNat) actual
  pure (Elab (SUList SUNat) rest
    ((prependU (encode prefix) :****: UId) :..: input))
elaborate tables env demand (SUSum a b) (ELeft value) = do
  Elab actual rest input <- elaborate tables env demand a value
  Refl <- requireSame a actual
  pure (Elab (SUSum a b) rest ((UInl :****: UId) :..: input))
elaborate tables env demand (SUSum a b) (ERight value) = do
  Elab actual rest input <- elaborate tables env demand b value
  Refl <- requireSame b actual
  pure (Elab (SUSum a b) rest ((UInr :****: UId) :..: input))
elaborate tables env demand expected (EMatchText value arms fallbackPat fallback) =
  elaborateMatches tables env demand expected (SUList SUNat) partitionTextU encode
    value arms fallbackPat fallback
elaborate tables env demand expected (EMatchNat value arms fallbackPat fallback) =
  elaborateMatches tables env demand expected SUNat partitionNatU id
    value arms fallbackPat fallback
elaborate tables env demand expected (ECase value arms) = do
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
          in elaborateMatches tables env demand expected SUNat partitionNatU id value
               (init tagged) PWild (snd (last tagged))
  where
    resolveArm (name, body) = case Map.lookup name (constructors tables) of
      Nothing              -> bad ("unknown constructor " <> name)
      Just (typeName, tag) -> Right (typeName, tag, body)
elaborate tables env demand expected@(SUList b) (EMapC input mapper) = do
  SomeTy inputListTy <- synthType tables env input
  case inputListTy of
    SUList a -> do
      -- input first: a dispatching mapper consumes the whole remaining
      -- context, so it must elaborate after the list is taken
      let pairTy = SUProd inputListTy (SULolly a b)
      Elab pairActual rest pair <- elaborate tables env demand pairTy
        (EPair input mapper)
      Refl <- requireSame pairTy pairActual
      pure (Elab expected rest (((UMapC :..: USwap) :****: UId) :..: pair))
    _ -> bad "mapc expects a list input with an inferable type"
elaborate tables env demand expected (EIterC count seed mapper) = do
  -- controller pair first (mapc's rule): the dispatching mapper
  -- consumes the whole remaining context
  let pairTy = SUProd (SUProd SUNat expected) (SULolly expected expected)
  Elab pairActual rest pair <- elaborate tables env demand pairTy
    (EPair (EPair count seed) mapper)
  Refl <- requireSame pairTy pairActual
  pure (Elab expected rest (((UIterC :..: USwap) :****: UId) :..: pair))
elaborate tables env demand expected (EFoldC input seed mapper) = do
  SomeTy inputListTy <- synthType tables env input
  case inputListTy of
    SUList a -> do
      let pairTy = SUProd (SUProd inputListTy expected)
            (SULolly (SUProd expected a) expected)
      Elab pairActual rest pair <- elaborate tables env demand pairTy
        (EPair (EPair input seed) mapper)
      Refl <- requireSame pairTy pairActual
      pure (Elab expected rest (((UFoldC :..: USwap) :****: UId) :..: pair))
    _ -> bad "foldc expects a list input with an inferable type"
elaborate tables env demand expected (EWhileC limit seed test step) = do
  let pairTy = SUProd (SUProd SUNat expected)
        (SUProd (SULolly expected (SUSum SUUnit SUUnit))
          (SULolly expected expected))
  Elab pairActual rest pair <- elaborate tables env demand pairTy
    (EPair (EPair limit seed) (EPair test step))
  Refl <- requireSame pairTy pairActual
  pure (Elab expected rest
    (((UWhileC expected :..: UAssoc :..: USwap) :****: UId) :..: pair))
elaborate tables env demand expected (EIterC count seed mapper) = do
  -- controller pair first (mapc's rule): the dispatching mapper
  -- consumes the whole remaining context
  let pairTy = SUProd (SUProd SUNat expected) (SULolly expected expected)
  Elab pairActual rest pair <- elaborate tables env demand pairTy
    (EPair (EPair count seed) mapper)
  Refl <- requireSame pairTy pairActual
  pure (Elab expected rest (((UIterC :..: USwap) :****: UId) :..: pair))
elaborate tables env demand expected (EFoldC input seed mapper) = do
  SomeTy inputListTy <- synthType tables env input
  case inputListTy of
    SUList a -> do
      let pairTy = SUProd (SUProd inputListTy expected)
            (SULolly (SUProd expected a) expected)
      Elab pairActual rest pair <- elaborate tables env demand pairTy
        (EPair (EPair input seed) mapper)
      Refl <- requireSame pairTy pairActual
      pure (Elab expected rest (((UFoldC :..: USwap) :****: UId) :..: pair))
    _ -> bad "foldc expects a list input with an inferable type"
elaborate tables env demand expected (EWhileC limit seed test step) = do
  let pairTy = SUProd (SUProd SUNat expected)
        (SUProd (SULolly expected (SUSum SUUnit SUUnit))
          (SULolly expected expected))
  Elab pairActual rest pair <- elaborate tables env demand pairTy
    (EPair (EPair limit seed) (EPair test step))
  Refl <- requireSame pairTy pairActual
  pure (Elab expected rest
    (((UWhileC expected :..: UAssoc :..: USwap) :****: UId) :..: pair))
elaborate tables env demand (SULolly a b) (ELam pat body) = do
  let captureNames = Set.toList (freeVars body Set.\\ patternNames pat)
  captures <- traverse (\name -> (,) name <$> envTypeOf name env) captureNames
  SomeCaps capsTy capsEnv capsExpr <- pure (buildCaps captures)
  Elab capsActual rest capsU <- elaborate tables env demand capsTy capsExpr
  Refl <- requireSame capsTy capsActual
  Bound innerEnv reshape <- bindPattern pat a capsEnv
  Elab bodyActual leftover bodyU <- elaborate tables innerEnv Set.empty b body
  Refl <- requireSame b bodyActual
  let bodyCore = finish leftover bodyU :..: reshape :..: USwap
  pure (Elab (SULolly a b) rest ((UCurry capsTy bodyCore :****: UId) :..: capsU))
elaborate _ _ _ _ (ELam _ _) =
  bad "a lambda needs a function type; annotate the enclosing binding with -o"
elaborate tables env demand expected (EApply function argument) = do
  SomeTy funTy <- synthType tables env function
  case funTy of
    SULolly argTy resTy -> do
      Refl <- requireSame expected resTy
      let pairTy = SUProd (SULolly argTy resTy) argTy
      Elab pairActual rest pair <- elaborate tables env demand pairTy
        (EPair function argument)
      Refl <- requireSame pairTy pairActual
      pure (Elab expected rest ((UApply :****: UId) :..: pair))
    _ -> bad "apply expects a function; bind one with an annotated let first"
elaborate _ _ _ _ expression = bad ("type mismatch in expression " <> show expression)

-- Closure capture environment: the lambda's free variables are consumed
-- (or implicitly copied, if demanded later) from the ambient context into
-- one right-nested product that becomes the closure's environment.
data SomeCaps where
  SomeCaps :: SUTy c -> Env c -> Expr -> SomeCaps

buildCaps :: [(String, SomeTy)] -> SomeCaps
buildCaps [] = SomeCaps SUUnit Empty EUnit
buildCaps ((name, SomeTy ty) : rest) = case buildCaps rest of
  SomeCaps restTy restEnv restExpr ->
    SomeCaps (SUProd ty restTy) (Bind name ty restEnv)
      (EPair (EVar name) restExpr)

-- | An explicit annotation resolves as written; an omitted one is
-- synthesized from the bound value (bounded synthesis, no unification).
resolveAnnotation
  :: Tables -> Env c -> Maybe Type -> Expr -> Either CompileError SomeTy
resolveAnnotation tables _ (Just annotation) _ = resolveType tables annotation
resolveAnnotation tables env Nothing value = synthType tables env value

-- Minimal type synthesis for apply heads: variables, definition calls, and
-- applications thereof (so chains like @f x y@ elaborate).
synthType :: Tables -> Env c -> Expr -> Either CompileError SomeTy
synthType _ env (EVar name) = envTypeOf name env
synthType tables _ (ECall name _) = do
  SomeDef _ output _ <- lookupDef tables name
  pure (SomeTy output)
synthType tables env (EApply function _) = do
  SomeTy funTy <- synthType tables env function
  case funTy of
    SULolly _ result -> pure (SomeTy result)
    _               -> bad "cannot apply a value that is not a function"
synthType _ _ (ECon name) =
  bad ("constructor " <> name <> " is not a function; enum constructors take no payload")
synthType _ _ EUnit = pure (SomeTy SUUnit)
synthType _ _ (ENat _) = pure (SomeTy SUNat)
synthType _ _ (EText _) = pure (SomeTy (SUList SUNat))
synthType tables env (EPair x y) = do
  SomeTy a <- synthType tables env x
  SomeTy b <- synthType tables env y
  pure (SomeTy (SUProd a b))
synthType _ _ (ESuc _) = pure (SomeTy SUNat)
synthType _ _ (EAdd _) = pure (SomeTy SUNat)
synthType tables env (ECopy value) = do
  SomeTy a <- synthType tables env value
  pure (SomeTy (SUProd a a))
synthType _ _ (EPrepend _ _) = pure (SomeTy (SUList SUNat))
synthType tables env (ECons value _) = do
  SomeTy a <- synthType tables env value
  pure (SomeTy (SUList a))
synthType tables _ (EMap _ mapper) = do
  SomeDef _ output _ <- lookupDef tables mapper
  pure (SomeTy (SUList output))
synthType tables _ (EIter _ _ step) = do
  SomeDef _ output _ <- lookupDef tables step
  pure (SomeTy output)
synthType tables _ (EFold _ _ step) = do
  SomeDef stepIn _ _ <- lookupDef tables step
  case stepIn of
    SUProd accumulator _ -> pure (SomeTy accumulator)
    _                    -> bad "fold step must accept accumulator * element"
synthType tables _ (EWhile _ _ _ step) = do
  SomeDef _ output _ <- lookupDef tables step
  pure (SomeTy output)
synthType tables env (EIterC _ seed _) = synthType tables env seed
synthType tables env (EFoldC _ seed _) = synthType tables env seed
synthType tables env (EWhileC _ seed _ _) = synthType tables env seed
synthType _ _ _ =
  bad "cannot infer a type here; annotate the binding (bind a function with an annotated let and apply the variable)"

envTypeOf :: String -> Env c -> Either CompileError SomeTy
envTypeOf name Empty = bad ("unknown variable " <> name)
envTypeOf name (Bind current ty rest)
  | name == current = Right (SomeTy ty)
  | otherwise = envTypeOf name rest

-- Exact matching consumes the scrutinee once. Failed partitions reconstruct it
-- before trying the next arm; every selected branch may weaken its own context.
-- The scrutinee is elaborated demanding every variable some arm still needs,
-- so a matched variable may be reused inside the arms (priced per path); the
-- match still consumes the whole environment, so nothing survives past it.
elaborateMatches
  :: Tables
  -> Env c
  -> Set.Set String
  -> SUTy out
  -> SUTy keyTy
  -> (key -> UMorph keyTy (keyTy ':++: keyTy))
  -> (literal -> key)
  -> Expr
  -> [(literal, Expr)]
  -> Pattern
  -> Expr
  -> Either CompileError (Elab c)
elaborateMatches tables env demand out keyTy partition convert value arms fallbackPat fallback = do
  let armDemand = Set.unions
        ((freeVars fallback Set.\\ patternNames fallbackPat)
          : fmap (freeVars . snd) arms)
  Elab actual rest input <- elaborate tables env
    (demand `Set.union` armDemand) keyTy value
  Refl <- requireSame keyTy actual
  let branch pat body = do
        Bound branchEnv reshape <- bindPattern pat keyTy rest
        Elab actual' leftovers compiled <- elaborate tables branchEnv
          Set.empty out body
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

-- | Non-consuming lookup: the binding stays in the environment and the
-- projected value is an implicit copy, priced through 'copyMorph'
-- (ultimately the core CopyS, charged sizeVal in the dup grade).
peekVar :: String -> Env c -> Either CompileError (Taken c)
peekVar name Empty = bad ("unknown variable " <> name)
peekVar name env@(Bind current ty rest)
  | name == current =
      Right (Taken ty env (UAssoc :..: (copyMorph ty :****: UId)))
  | otherwise = do
      Taken found remaining morph <- peekVar name rest
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

-- | Copying is total on first-order data and uniformly priced: 'UDup'
-- compiles to the core CopyS, whose dup grade is the copied value's full
-- sizeVal.  Explicit @copy@ and implicit reuse share this one path.
copyMorph :: SUTy a -> UMorph a (a ':**: a)
copyMorph = UDup

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

firstOrderTy :: SUTy a -> Bool
firstOrderTy SUUnit        = True
firstOrderTy SUNat         = True
firstOrderTy (SUProd a b)  = firstOrderTy a && firstOrderTy b
firstOrderTy (SUSum a b)   = firstOrderTy a && firstOrderTy b
firstOrderTy (SUList a)    = firstOrderTy a
firstOrderTy (SULolly _ _) = False

sameTy :: SUTy a -> SUTy b -> Maybe (a :~: b)
sameTy SUUnit SUUnit = Just Refl
sameTy SUNat SUNat = Just Refl
sameTy (SUProd a b) (SUProd c d) = do Refl <- sameTy a c; Refl <- sameTy b d; pure Refl
sameTy (SUSum a b) (SUSum c d) = do Refl <- sameTy a c; Refl <- sameTy b d; pure Refl
sameTy (SUList a) (SUList b) = do Refl <- sameTy a b; pure Refl
sameTy (SULolly a b) (SULolly c d) = do
  Refl <- sameTy a c
  Refl <- sameTy b d
  pure Refl
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

fromDirect :: Either DirectError a -> Either CompileError a
fromDirect = either
  (bad . ("direct compilation failed: " <>) . show) Right
