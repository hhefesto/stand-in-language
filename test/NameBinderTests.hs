{-# LANGUAGE LambdaCase #-}

-- |Tests for 'Telomare.Bind', numbered as in section 10 of
-- @telomare-name-binder-spec.txt@.
module NameBinderTests (nameBinderTests) where

import Data.Bifunctor (first)
import qualified System.IO.Strict as Strict
import Telomare.Bind (BindWarning (..))
import Telomare.Driver (runMain_)
import Telomare.Error (ResolverError (..))
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.IR.Surface (ExpandedSurfaceTerm)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (resolveMainWithWarnings)
import Test.Tasty
import Test.Tasty.HUnit

-- |Modules as the CLI loads them: Prelude, then the given ones.
withPrelude :: [(String, String)] -> IO [(String, String)]
withPrelude sources = (\prelude -> ("Prelude", prelude) : sources) <$> Strict.readFile "Prelude.tel"

-- |Run a program whose entry module is "Main".
run :: [(String, String)] -> IO String
run sources = withPrelude sources >>= \modules -> runMain_ modules "Main"

runMain' :: [String] -> IO String
runMain' mainLines = run [("Main", unlines ("import Prelude" : mainLines))]

bind :: [(String, String)] -> IO (Either ResolverError (ExpandedSurfaceTerm, [(String, BindWarning)]))
bind sources = do
  modules <- withPrelude sources
  let expand (name, src) = case runParseModule name src >>= first renderExpansionError . expandModule of
        Right m -> (name, m)
        Left e  -> error e
  pure $ resolveMainWithWarnings (expand <$> modules) "Main"

bindMain :: [String] -> IO (Either ResolverError (ExpandedSurfaceTerm, [(String, BindWarning)]))
bindMain mainLines = bind [("Main", unlines ("import Prelude" : mainLines))]

expectError :: String -> (ResolverError -> Bool) -> IO (Either ResolverError a) -> Assertion
expectError what isExpected action = action >>= \case
  Left err | isExpected err -> pure ()
  Left err -> assertFailure $ "expected " <> what <> ", got " <> show err
  Right _ -> assertFailure $ "expected " <> what <> ", but it bound"

warningsOf :: IO (Either ResolverError (a, [(String, BindWarning)])) -> IO [BindWarning]
warningsOf action = action >>= \case
  Left err -> assertFailure (show err) >> pure []
  Right (_, ws) -> pure (snd <$> ws)

shadows, unused, passes :: String -> BindWarning -> Bool
shadows name = \case
  Shadows _ n _ -> n == name
  _ -> False
unused name = \case
  UnusedBinding _ n -> n == name
  _ -> False
passes name = \case
  ShadowsRequirement _ n -> n == name
  _ -> False

hasWarning :: String -> (BindWarning -> Bool) -> [BindWarning] -> Assertion
hasWarning what p ws = assertBool ("expected " <> what <> " in " <> show ws) (any p ws)

nameBinderTests :: TestTree
nameBinderTests = testGroup "Name binder"
  [ testCase "T2 basic supply" $ do
      out <- runMain'
        [ "main = \\i -> let f = \\n -> x"
        , "             in let x = \"one\""
        , "                in (f 0, 0)"
        ]
      out @?= "one\ndone"
  , testCase "T3 definition site wins" $ do
      let program =
            [ "main = \\i -> let x = \"outer\""
            , "             in let f = \\n -> x"
            , "                in let x = \"inner\""
            , "                   in (f 0, 0)"
            ]
      out <- runMain' program
      out @?= "outer\ndone"
      ws <- warningsOf (bindMain program)
      hasWarning "x shadowed" (shadows "x") ws
      hasWarning "x unused" (unused "x") ws
  , testCase "T4 propagation" $ do
      out <- runMain'
        [ "main = \\i -> let f = \\n -> x"
        , "                 g = \\n -> f n"
        , "             in let x = \"prop\""
        , "                in (g 0, 0)"
        ]
      out @?= "prop\ndone"
  , testCase "T5 sibling supply" $ do
      out <- runMain'
        [ "main = \\i -> let f = \\n -> x"
        , "                 x = \"sib\""
        , "             in (f 0, 0)"
        ]
      out @?= "sib\ndone"
  , testCase "T6 lambdas do not supply" .
      expectError "unsupplied x" (\case UnsuppliedRequirement "x" _ _ -> True; _ -> False) $ bindMain
        [ "main = \\i -> let f = \\n -> x"
        , "             in (\\x -> (f 0, 0)) \"lam\""
        ]
  , testCase "T6 a variable a requirement passes warns" $ do
      ws <- warningsOf $ bindMain
        [ "f = \\n -> x"
        , "g = \\x -> f 0"
        , "main = \\i -> let x = \"top\" in (g 1, 0)"
        ]
      hasWarning "x passes the lambda" (passes "x") ws
  , testCase "T7 unsupplied requirement reports its chain" .
      expectError "le via h, g, main"
        (\case UnsuppliedRequirement "le" _ via -> fmap fst via == ["h", "g", "main"]; _ -> False)
        $ bindMain
          [ "h = \\n -> le n"
          , "g = \\n -> h n"
          , "main = \\i -> (g 0, 0)"
          ]
  , testCase "T8 cycle through a requirement" .
      expectError "a definition cycle" (\case DefinitionCycle _ -> True; _ -> False) $ bindMain
        [ "main = \\i -> let f = \\n -> x"
        , "             in let x = f 0"
        , "                in (x, 0)"
        ]
  , testCase "T9 open supplier" $ do
      out <- runMain'
        [ "main = \\i -> let f = \\n -> x"
        , "             in let x = y"
        , "                in let y = \"why\""
        , "                   in (f 0, 0)"
        ]
      out @?= "why\ndone"
  , testCase "T10 requirement inside a refinement" $ do
      out <- runMain'
        [ "main = \\i -> let r : chk = \"checked\""
        , "             in let chk = \\v -> 1"
        , "                in (r, 0)"
        ]
      out @?= "checked\ndone"
  , testCase "T11 dictionary style across modules" $ do
      let sortModule = unlines ["pick = \\a b -> if le a b then a else b"]
          mainModule le = unlines
            [ "import Prelude"
            , "import Sort"
            , "main = \\i -> let le = " <> le
            , "             in (pick \"first\" \"second\", 0)"
            ]
      first' <- run [("Sort", sortModule), ("Main", mainModule "\\a b -> 1")]
      first' @?= "first\ndone"
      second' <- run [("Sort", sortModule), ("Main", mainModule "\\a b -> 0")]
      second' @?= "second\ndone"
  , testCase "T12 one open entry, two instantiations" $ do
      out <- runMain'
        [ "f = \\n -> x"
        , "main = \\i -> (listPlus (let x = \"a\" in f 0) (let x = \"b\" in f 0), 0)"
        ]
      out @?= "ab\ndone"
  , testCase "T13 classification is by nearest binder" $ do
      out <- runMain'
        [ "main = \\i -> (listPlus ((\\x -> let x = \"let\" in x) 0)"
        , "                        (let x = \"let\" in (\\x -> x) \"lam\"), 0)"
        ]
      out @?= "letlam\ndone"
  , testCase "T14 supplied arguments are not captured" $ do
      out <- runMain'
        [ "main = \\i -> let f = \\n -> x"
        , "             in let x = \"let\""
        , "                in (\\x -> (listPlus (f 0) x, 0)) \"lam\""
        ]
      out @?= "letlam\ndone"
  , testCase "T15 an annotated parameter does not supply" .
      expectError "unsupplied x" (\case UnsuppliedRequirement "x" _ _ -> True; _ -> False) $ bindMain
        [ "main = \\i -> let f = \\n -> x"
        , "             in (\\(x : Bool) -> (f 0, 0)) 1"
        ]
  , testCase "T16 later imports and own definitions shadow" $ do
      let a = ("A", "k = \"a\"\n")
          b = ("B", "k = \"b\"\n")
          mainWith extra = ("Main", unlines (["import A", "import B"] <> extra <> ["main = \\i -> (k, 0)"]))
      later <- run [a, b, mainWith []]
      later @?= "b\ndone"
      own <- run [a, b, mainWith ["k = \"m\""]]
      own @?= "m\ndone"
      ws <- warningsOf (bind [a, b, mainWith []])
      hasWarning "k shadowed" (shadows "k") ws
  , testCase "T17 a diamond import is bound once" $ do
      let base = ("Base", "v = \"v\"\n")
          mid = ("Mid", "import Base\nw = v\n")
      out <- run [base, mid, ("Main", "import Base\nimport Mid\nmain = \\i -> (w, 0)\n")]
      out @?= "v\ndone"
  , testCase "T18 imports are not re-exported" $ do
      let base = ("Base", "v = \"v\"\n")
          mid = ("Mid", "import Base\nw = v\n")
      expectError "v undefined" (\case MissingDefinitionAt _ "v" -> True; _ -> False) $
        bind [base, mid, ("Main", "import Mid\nmain = \\i -> (v, 0)\n")]
  , testCase "T19 qualified names" $ do
      let base = ("Base", "v = \"qv\"\n")
      out <- run [base, ("Main", "import qualified Base as Q\nmain = \\i -> (Q.v, 0)\n")]
      out @?= "qv\ndone"
      expectError "unbound qualified name" (\case UnboundQualifiedName _ "Q.missing" -> True; _ -> False) $
        bind [base, ("Main", "import qualified Base as Q\nmain = \\i -> (Q.missing, 0)\n")]
  , testCase "T20 a builtin cannot be supplied" $ do
      out <- runMain'
        [ "f = \\p -> left p"
        , "main = \\i -> let left = \\x -> \"fake\""
        , "             in (f (\"real\", 0), 0)"
        ]
      out @?= "real\ndone"
  , testCase "T21 duplicate keys in one block" $ do
      expectError "duplicate a" (\case DuplicateDefinition _ "a" -> True; _ -> False) $ bindMain
        [ "main = \\i -> let a = \"1\""
        , "                 a = \"2\""
        , "             in (a, 0)"
        ]
      expectError "duplicate top-level a" (\case DuplicateDefinition _ "a" -> True; _ -> False) $ bindMain
        [ "a = \"1\""
        , "a = \"2\""
        , "main = \\i -> (a, 0)"
        ]
  , testCase "T22/T23 unsized recursion in an open entry, two instantiations" $ do
      out <- runMain'
        [ "g = \\l -> map (\\c -> sep) l"
        , "main = \\i -> (listPlus (let sep = 65 in g \"ab\") (let sep = 66 in g \"ab\"), 0)"
        ]
      out @?= "AABB\ndone"
  ]
