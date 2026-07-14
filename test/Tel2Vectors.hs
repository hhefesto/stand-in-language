module Tel2Vectors (tel2Vectors) where

import Data.List (isInfixOf)
import System.Directory (doesFileExist)

import Telomare.Compiler.Direct (erasureMatches)
import Telomare.Machine
import Telomare.Tel2

baseDir :: IO FilePath
baseDir = do
  here <- doesFileExist "test/programs/tictactoe.tel2"
  pure (if here then "" else "./")

tel2Vectors :: IO [(String, Bool)]
tel2Vectors = do
  base <- baseDir
  source <- readFile (base <> "test/programs/tictactoe.tel2")
  case compileTel2 source of
    Left _ -> pure [("tel2 tictactoe parses and compiles", False)]
    Right program -> do
      games <- sequence
        [ golden base program "tel2_ttt_win" ["1", "4", "2", "5", "3"]
        , golden base program "tel2_ttt_quit" ["q"]
        , golden base program "tel2_ttt_invalid" ["x", "1", "1", "4", "2", "5", "3"]
        , golden base program "tel2_ttt_tie" ["1", "2", "3", "5", "8", "4", "6", "9", "7"]
        ]
      let compiled = ("tel2 tictactoe parses and compiles",
            length (lines source) < 300
              && not ("telomare-grid-game" `isInfixOf` source)
              && erases program)
          malformed =
            [ rejects "tel2 rejects old grid grammar" "telomare-grid-game 1\nboard 3 3"
            , rejects "tel2 rejects parse errors" "type State = Nat"
            , rejects "tel2 rejects type errors" (small "(\"x\",right \"not a Nat\")")
            , rejects "tel2 rejects implicit duplication" duplicateSource
            , rejects "tel2 rejects cyclic aliases" cyclicAliasSource
            , rejects "tel2 rejects non-exhaustive enum cases" incompleteCaseSource
            , rejects "tel2 rejects duplicate tuple binders" duplicateBinderSource
            ]
          explicit = accepts "tel2 accepts explicit copy" copySource
          namedData = accepts "tel2 accepts named finite data and case" dataSource
          mutation = sourceMutation source
      pure (compiled : explicit : namedData : mutation : malformed <> games)

erases :: Program -> Bool
erases (Program _ initial step _ _) =
  erasureMatches initial == Right True && erasureMatches step == Right True

golden :: FilePath -> Program -> String -> [String] -> IO (String, Bool)
golden base program name inputs = do
  expected <- readFile (base <> "test/golden/" <> name <> ".txt")
  let actual = fst <$> runProgramScript program inputs
  pure (name <> " through UMorph and Morph", actual == Right expected)

rejects :: String -> String -> (String, Bool)
rejects name source = (name, case compileTel2 source of Left _ -> True; Right _ -> False)

accepts :: String -> String -> (String, Bool)
accepts name source = (name, case compileTel2 source of Left _ -> False; Right _ -> True)

sourceMutation :: String -> (String, Bool)
sourceMutation source = ("tel2 source mutation changes denotation", original /= changed)
  where
    original = compileTel2 source >>= script
    changed = compileTel2 (replace "Goodbye.\\n" "Farewell.\\n" source) >>= script
    script program = fst <$> either (Left . CompileError) Right (runProgramScript program ["q"])

replace :: String -> String -> String -> String
replace old new input
  | old `isPrefix` input = new <> drop (length old) input
replace old new (x : xs) = x : replace old new xs
replace _ _ [] = []

isPrefix :: String -> String -> Bool
isPrefix prefix value = take (length prefix) value == prefix

small :: String -> String
small initial = unlines
  [ "type State = Nat;"
  , "def init(u: Unit): Reply State = " <> initial <> ";"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

copySource :: String
copySource = unlines
  [ "type State = Nat * Nat;"
  , "def init(u: Unit): Reply State = let p: Nat * Nat = copy 7 in (\"\",right p);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

duplicateSource :: String
duplicateSource = unlines
  [ "type State = Nat * Nat;"
  , "def init(u: Unit): Reply State = let n: Nat = 7 in (\"\",right (n,n));"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

dataSource :: String
dataSource = unlines
  [ "data Flag = No | Yes;"
  , "type State = Nat;"
  , "def choose(f: Flag): Nat = case f of { No -> 0; Yes -> 1; };"
  , "def init(u: Unit): Reply State = (\"\",right choose(Yes));"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

cyclicAliasSource :: String
cyclicAliasSource = unlines
  [ "type A = B;"
  , "type B = A;"
  , "type State = A;"
  , "def init(u: Unit): Reply State = (\"\",left ());"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

incompleteCaseSource :: String
incompleteCaseSource = unlines
  [ "data Flag = No | Yes;"
  , "type State = Nat;"
  , "def choose(f: Flag): Nat = case f of { No -> 0; };"
  , "def init(u: Unit): Reply State = (\"\",right choose(No));"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

duplicateBinderSource :: String
duplicateBinderSource = unlines
  [ "type State = Nat;"
  , "def bad(p: Nat * Nat): Nat = let (x,x): Nat * Nat = p in x;"
  , "def init(u: Unit): Reply State = (\"\",right 0);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]
