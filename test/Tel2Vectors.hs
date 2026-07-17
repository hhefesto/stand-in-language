module Tel2Vectors (tel2Vectors) where

import Data.List (isInfixOf)
import System.Directory (doesFileExist, getTemporaryDirectory, makeAbsolute,
                         withCurrentDirectory)

import Telomare.Compiler.Direct (eraseMorph, erasureMatches)
import Telomare.Machine
import Telomare.Surface (UShape (..), shapeU)
import Telomare.Tel2
import Telomare.Transport

baseDir :: IO FilePath
baseDir = do
  here <- doesFileExist "test/programs/tictactoe.tel2"
  pure (if here then "" else "./")

tel2Vectors :: IO [(String, Bool)]
tel2Vectors = do
  base <- baseDir
  source <- readFile (base <> "test/programs/tictactoe.tel2")
  prelude <- readFile (base <> "stdlib/Prelude.tel2")
  exampleSource <- readFile (base <> "test/programs/examples.tel2")
  importCycle <- rejectsFile "tel2 rejects import cycles" (base <> "test/programs/CycleA.tel2") "import cycle"
  missing <- rejectsFile "tel2 rejects missing modules" (base <> "test/programs/MissingImport.tel2") "cannot load module NotPresent"
  packagedPrelude <- acceptsFileBehavior "tel2 loads packaged Prelude"
    (base <> "test/programs/PreludeHelpers.tel2") ["check"] "true\n"
  packagedMap <- acceptsFileBehavior "tel2 loads reusable packaged map specialization"
    (base <> "test/programs/PreludeMap.tel2") ["ABC"] "mapped\n"
  cwdIndependent <- acceptsFileAwayFromWorkspace
    "tel2 packaged stdlib resolution is cwd-independent"
    (base <> "test/programs/PreludeHelpers.tel2") ["check"] "true\n"
  localShadow <- acceptsFileBehavior "tel2 sibling module shadows packaged stdlib"
    (base <> "test/programs/shadow/Entry.tel2") ["check"] "local\n"
  headerMismatch <- rejectsFile "tel2 validates shadowing module headers"
    (base <> "test/programs/header-mismatch/Entry.tel2") "declares module Wrong"
  exampleResult <- compileTel2File (base <> "test/programs/examples.tel2")
  compiledFile <- compileTel2File (base <> "test/programs/tictactoe.tel2")
  case compiledFile of
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
            , rejects "tel2 rejects cyclic aliases" cyclicAliasSource
            , rejects "tel2 rejects non-exhaustive enum cases" incompleteCaseSource
            , rejects "tel2 rejects duplicate tuple binders" duplicateBinderSource
            , rejects "tel2 rejects cyclic definitions" cyclicDefinitionSource
            ]
          explicit = accepts "tel2 accepts explicit copy" copySource
          closures =
            [ acceptsBehavior "tel2 lambda with capture applies once"
                makeAdderSource ["go"] "twelve\n"
            , acceptsBehavior "tel2 runtime-selected closure applies"
                chooseOperationSource ["go", "go"] "six\nsix\n"
            , acceptsBehavior "tel2 composed closures apply inside a closure"
                composeSource ["go"] "nine\n"
            , rejectsWith "tel2 rejects implicit closure copy"
                closureReuseSource "cannot be implicitly copied"
            , rejectsWith "tel2 rejects explicit closure copy"
                closureCopySource "cannot copy a function"
            , rejectsWith "tel2 rejects closures in machine state"
                closureStateSource "must be first-order"
            ]
          implicitCopy =
            [ accepts "tel2 accepts implicit duplication of a Nat" duplicateSource
            , accepts "tel2 accepts implicit duplication of a list" implicitListReuseSource
            , acceptsBehavior "tel2 implicit Nat reuse doubles exactly"
                implicitNatReuseSource ["go"] "ten\n"
            , acceptsBehavior "tel2 match scrutinee stays reusable in arms"
                scrutineeReuseSource ["go", "go"] "sum\nsum\n"
            ]
          namedData = accepts "tel2 accepts named finite data and case" dataSource
          forward = accepts "tel2 compiles forward definition references" forwardReferenceSource
          closedBounds = accepts "tel2 accepts closed Nat expressions as recursion bounds"
            closedBoundExpressionSource
          reusableRecursion =
            [ accepts "tel2 compiles reusable iteration helper" helperIterationSource
            , accepts "tel2 compiles reusable fold helper" helperFoldSource
            , accepts "tel2 accepts affine list constructors" listConstructorSource
            , acceptsBehavior "tel2 runtime-bound iteration preserves surface behavior"
                runtimeIterationSource ["go"] "two\n"
            , acceptsBehavior "tel2 runtime-list fold preserves surface behavior"
                runtimeFoldSource ["ABC"] "sum\n"
            , acceptsMapBehavior "tel2 runtime-list map emits MapS and preserves ordinary list order"
                runtimeMapSource ["ABC"] "mapped\n"
            , acceptsBehavior "tel2 runtime-bound while preserves surface behavior"
                runtimeWhileSource ["go"] "three\n"
            ]
          recursion = recursionVectors exampleResult
          addition = acceptsBehavior "tel2 primitive addition is exact"
            additionSource ["check"] "eleven\n"
          needsLegacy = ("tel2 example genuinely depends on LegacyPrelude",
            case compileTel2 (anonymous prelude <> anonymous exampleSource) of
              Left _  -> True
              Right _ -> False)
          illegalRecursion =
             [ rejectsWith "tel2 rejects captured iteration seed" capturedSeedSource "seed cannot capture"
            , rejectsWith "tel2 rejects captured iteration bound" capturedBoundSource "bound cannot capture"
            , rejectsWith "tel2 rejects captured iteration continuation" capturedContinuationSource "continuation cannot capture"
            , rejectsWith "tel2 rejects captured fold input" capturedFoldInputSource "fold input cannot capture"
            , rejectsWith "tel2 rejects captured fold seed" capturedFoldSeedSource "fold seed cannot capture"
            , rejectsWith "tel2 rejects captured while seed" capturedWhileSeedSource "while seed cannot capture"
            , rejectsWith "tel2 rejects nested closed recursion" nestedRecursionSource "cannot capture or contain recursion"
            , rejectsWith "tel2 rejects open recursive seed" openSeedSource "must be closed; open promotion is unavailable"
            , rejectsWith "tel2 rejects live context after recursion" residualContextSource "cannot remain live"
            , rejects "tel2 rejects a map mapper with the wrong result type" wrongMapResultSource
            ]
          needsPrelude = ("tictactoe genuinely depends on imported Prelude",
            case compileTel2 (anonymous source) of Left _ -> True; Right _ -> False)
          mutation = sourceMutation (anonymous prelude <> anonymous source)
      pure (compiled : explicit : namedData : forward : closedBounds : addition : packagedPrelude : packagedMap
        : cwdIndependent : localShadow : headerMismatch
        : needsPrelude : needsLegacy : mutation
        : importCycle : missing : closures <> implicitCopy <> recursion <> reusableRecursion <> illegalRecursion <> malformed <> games)

erases :: Program -> Bool
erases (Program _ initial step _ _) =
  direct initial && direct step
  where
    direct source = erasureMatches source == Right True

recursionVectors :: Either CompileError Program -> [(String, Bool)]
recursionVectors (Left _) = [("tel2 Prelude/LegacyPrelude example compiles", False)]
recursionVectors (Right program) =
  [ ("tel2 Prelude/LegacyPrelude example compiles", True)
  , ("tel2 recursion emits IterS", programHasIter program)
  , ("tel2 recursion emits FoldS", programHasFold program)
  , ("tel2 recursion emits WhileS", programHasWhile program)
  , ("tel2 primitive addition emits AddS", programHasAdd program)
  , ("tel2 closed recursion has exact core depth", programDepth program == 1)
  , ("tel2 closed recursion has exact modal shape", modalShape program)
  , ("tel2 recursion has exact surface/core behavior",
      case runProgramScript program ["show"] of
        Right (output, spent) -> output ==
          exampleIntroduction <> "Verified: all four typed-core results are exact.\n"
          && spent >= 5
        Left _ -> False)
  , ("tel2 closed recursion has exact formal work",
      runProgramScript program [] == Right
        (exampleIntroduction, 21))
  ]

modalShape :: Program -> Bool
modalShape program =
  count isBoxVal == 4
    && count isIter == 1
    && count isFold == 1
    && count isWhile == 1
    && count isMerge == 3
    && count isBox == 1
    && count isDup == 0
  where
    initial = artifactNode (programArtifactInitial (exportProgram program))
    count predicate = length (filter predicate (nodeTree initial))
    isBoxVal NBoxVal {} = True
    isBoxVal _          = False
    isIter NIter {} = True
    isIter _        = False
    isFold NFold {} = True
    isFold _        = False
    isWhile NWhile {} = True
    isWhile _         = False
    isMerge NMerge = True
    isMerge _      = False
    isBox NBox {} = True
    isBox _       = False
    isDup NDup {} = True
    isDup _       = False

nodeTree :: Node -> [Node]
nodeTree node = node : case node of
  NCompose left right -> nodeTree left <> nodeTree right
  NProduct left right -> nodeTree left <> nodeTree right
  NCase left right    -> nodeTree left <> nodeTree right
  NGuard _ child      -> nodeTree child
  NBox child          -> nodeTree child
  NBoxVal child       -> nodeTree child
  NMap child          -> nodeTree child
  NIter child         -> nodeTree child
  NFold child         -> nodeTree child
  NWhile _ test step  -> nodeTree test <> nodeTree step
  _                   -> []

exampleIntroduction :: String
exampleIntroduction =
  "Telomare typed-core tour:\n"
  <> "- iterate: increment 0 five times = 5\n"
  <> "- fold: sum the code points in ABC = 198\n"
  <> "- while: increment until 3, with fuel 10 = 3\n"
  <> "- add: explicitly copy 5, then add 10 = 15\n"
  <> "Enter anything to verify the stored results, or q to stop.\n"

programHasIter :: Program -> Bool
programHasIter = programHasShape isIter
  where
    isIter ShIter {} = True
    isIter _         = False

programHasAdd :: Program -> Bool
programHasAdd = programHasShape (== ShAdd)

programHasMap :: Program -> Bool
programHasMap = programHasShape isMap
  where
    isMap ShMap {} = True
    isMap _        = False

programHasFold :: Program -> Bool
programHasFold = programHasShape isFold
  where
    isFold ShFold {} = True
    isFold _         = False

programHasWhile :: Program -> Bool
programHasWhile = programHasShape isWhile
  where
    isWhile ShWhile {} = True
    isWhile _          = False

programHasShape :: (UShape -> Bool) -> Program -> Bool
programHasShape predicate (Program _ _ _ initial step) =
  entryHasShape initial || entryHasShape step
  where
    entryHasShape (CoreEntry _ _ _ core) = go (shapeU (eraseMorph core))
    go shape = predicate shape || case shape of
      ShComp x y   -> go x || go y
      ShTensor x y -> go x || go y
      ShCase x y   -> go x || go y
      ShGuard x    -> go x
      ShMap x      -> go x
      ShIter x     -> go x
      ShFold x     -> go x
      ShWhile x y  -> go x || go y
      _            -> False

acceptsBehavior :: String -> String -> [String] -> String -> (String, Bool)
acceptsBehavior name source inputs expected = (name, case compileTel2 source of
  Left _ -> False
  Right program -> case runProgramScript program inputs of
    Right (output, _) -> output == expected
    Left _            -> False)

acceptsMapBehavior :: String -> String -> [String] -> String -> (String, Bool)
acceptsMapBehavior name source inputs expected = (name, case compileTel2 source of
  Left _ -> False
  Right program -> programHasMap program && case runProgramScript program inputs of
    Right (output, _) -> output == expected
    Left _            -> False)

golden :: FilePath -> Program -> String -> [String] -> IO (String, Bool)
golden base program name inputs = do
  expected <- readFile (base <> "test/golden/" <> name <> ".txt")
  let actual = fst <$> runProgramScript program inputs
  pure (name <> " through UMorph and Morph", actual == Right expected)

rejects :: String -> String -> (String, Bool)
rejects name source = (name, case compileTel2 source of Left _ -> True; Right _ -> False)

rejectsWith :: String -> String -> String -> (String, Bool)
rejectsWith name source expected = (name, case compileTel2 source of
  Left (CompileError message) -> expected `isInfixOf` message
  Right _                     -> False)

accepts :: String -> String -> (String, Bool)
accepts name source = (name, case compileTel2 source of Left _ -> False; Right _ -> True)

rejectsFile :: String -> FilePath -> String -> IO (String, Bool)
rejectsFile name path expected = do
  result <- compileTel2File path
  pure (name, case result of
    Left (CompileError message) -> expected `isInfixOf` message
    Right _                     -> False)

acceptsFileBehavior :: String -> FilePath -> [String] -> String -> IO (String, Bool)
acceptsFileBehavior name path inputs expected = do
  result <- compileTel2File path
  pure (name, case result of
    Left _ -> False
    Right program -> case runProgramScript program inputs of
      Left _            -> False
      Right (output, _) -> output == expected)

acceptsFileAwayFromWorkspace
  :: String -> FilePath -> [String] -> String -> IO (String, Bool)
acceptsFileAwayFromWorkspace name path inputs expected = do
  absolute <- makeAbsolute path
  temporary <- getTemporaryDirectory
  withCurrentDirectory temporary
    (acceptsFileBehavior name absolute inputs expected)

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

anonymous :: String -> String
anonymous = unlines . filter (not . header) . lines
  where
    header line = "module " `isPrefix` line || "import " `isPrefix` line

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

implicitListReuseSource :: String
implicitListReuseSource = unlines
  [ "type State = List Nat * List Nat;"
  , "def dupList(xs: List Nat): List Nat * List Nat = (xs, xs);"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right dupList(cons 1 onto []));"
  , "def step(request: Text * State): Reply State = let (input,state): Text * State = request in let _: Text = input in let _: State = state in (\"\",left ());"
  ]

implicitNatReuseSource :: String
implicitNatReuseSource = unlines
  [ "type State = Nat;"
  , "def double(n: Nat): Nat = add (n,n);"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right 5);"
  , "def step(request: Text * State): Reply State = let (input,n): Text * State = request in let _: Text = input in matchNat double(n) of { 10 -> (\"ten\\n\",left ()); m -> (\"bad\\n\",left ()); };"
  ]

makeAdderSource :: String
makeAdderSource = unlines
  [ "type State = Nat;"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right 5);"
  , "def step(request: Text * State): Reply State = let (input,amount): Text * State = request in let _: Text = input in let adder: Nat -o Nat = \\value -> add (amount,value) in matchNat apply(adder, 7) of { 12 -> (\"twelve\\n\",left ()); m -> (\"bad\\n\",left ()); };"
  ]

chooseOperationSource :: String
chooseOperationSource = unlines
  [ "type State = Nat;"
  , "def pick(flag: Nat): Nat -o Nat = matchNat flag of { 0 -> \\n -> suc n; _ -> \\n -> add (n,n) };"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right 3);"
  , "def step(request: Text * State): Reply State = let (input,n): Text * State = request in let _: Text = input in let f: Nat -o Nat = pick(n) in matchNat apply(f, n) of { 6 -> (\"six\\n\",right n); m -> (\"bad\\n\",left ()); };"
  ]

composeSource :: String
composeSource = unlines
  [ "type State = Nat;"
  , "def compose(fs: (Nat -o Nat) * (Nat -o Nat)): Nat -o Nat = let (first,second): (Nat -o Nat) * (Nat -o Nat) = fs in \\value -> apply(second, apply(first, value));"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right 7);"
  , "def step(request: Text * State): Reply State = let (input,n): Text * State = request in let _: Text = input in let f: Nat -o Nat = compose((\\a -> suc a, \\b -> suc b)) in matchNat apply(f, n) of { 9 -> (\"nine\\n\",left ()); m -> (\"bad\\n\",left ()); };"
  ]

closureReuseSource :: String
closureReuseSource = unlines
  [ "type State = Nat;"
  , "def init(u: Unit): Reply State = let _: Unit = u in let f: Nat -o Nat = \\n -> suc n in (\"\",right add (apply(f, 1), apply(f, 2)));"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

closureCopySource :: String
closureCopySource = unlines
  [ "type State = Nat;"
  , "def init(u: Unit): Reply State = let _: Unit = u in let f: Nat -o Nat = \\n -> suc n in let (g,h): (Nat -o Nat) * (Nat -o Nat) = copy f in (\"\",right add (apply(g, 1), apply(h, 2)));"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

closureStateSource :: String
closureStateSource = unlines
  [ "type State = Nat -o Nat;"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right \\n -> suc n);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

scrutineeReuseSource :: String
scrutineeReuseSource = unlines
  [ "type State = Nat;"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right 3);"
  , "def step(request: Text * State): Reply State = let (input,n): Text * State = request in let _: Text = input in matchNat n of { 0 -> (\"zero\\n\",left ()); _ -> (\"sum\\n\",right add (n,n)); };"
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

forwardReferenceSource :: String
forwardReferenceSource = unlines
  [ "type State = Later;"
  , "def init(u: Unit): Reply State = (\"\",right make(u));"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  , "def make(u: Unit): Later = 7;"
  , "type Later = Nat;"
  ]

cyclicDefinitionSource :: String
cyclicDefinitionSource = unlines
  [ "type State = Nat;"
  , "def a(n: Nat): Nat = b(n);"
  , "def b(n: Nat): Nat = a(n);"
  , "def init(u: Unit): Reply State = (\"\",right 0);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

capturedSeedSource :: String
capturedSeedSource = unlines
  [ "type State = Nat;"
  , "def keepUnit(x: Unit): Unit = x;"
  , "def init(u: Unit): Reply State = let x: Unit = iterate 1 from u with keepUnit in (\"\",right 0);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

capturedBoundSource :: String
capturedBoundSource = unlines
  [ "type State = Nat;"
  , "def increment(n: Nat): Nat = suc n;"
  , "def init(u: Unit): Reply State = let n: Nat = iterate let z: Unit = u in 1 from 0 with increment in (\"\",right n);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

capturedContinuationSource :: String
capturedContinuationSource = unlines
  [ "type State = Nat;"
  , "def increment(n: Nat): Nat = suc n;"
  , "def init(u: Unit): Reply State = let n: Nat = iterate 1 from 0 with increment in let z: Unit = u in (\"\",right n);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

helperIterationSource :: String
helperIterationSource = unlines
  [ "type State = Nat;"
  , "def increment(n: Nat): Nat = suc n;"
  , "def count(u: Unit): Reply State = let n: Nat = iterate 2 from 0 with increment in (\"\",right n);"
  , "def init(u: Unit): Reply State = count(u);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

capturedFoldInputSource :: String
capturedFoldInputSource = unlines
  [ "type State = Nat;"
  , "def sum(p: Nat * Nat): Nat = add p;"
  , "def init(u: Unit): Reply State = let n: Nat = fold let z: Unit = u in \"A\" from 0 with sum in (\"\",right n);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

capturedFoldSeedSource :: String
capturedFoldSeedSource = unlines
  [ "type State = Nat;"
  , "def sum(p: Nat * Nat): Nat = add p;"
  , "def init(u: Unit): Reply State = let n: Nat = fold \"A\" from let z: Unit = u in 0 with sum in (\"\",right n);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

capturedWhileSeedSource :: String
capturedWhileSeedSource = unlines
  [ "type State = Nat;"
  , "def stop(n: Nat): Unit + Unit = left ();"
  , "def inc(n: Nat): Nat = suc n;"
  , "def init(u: Unit): Reply State = let n: Nat = while 2 from let z: Unit = u in 0 testing stop stepping inc in (\"\",right n);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

nestedRecursionSource :: String
nestedRecursionSource = unlines
  [ "type State = Nat;"
  , "def sum(p: Nat * Nat): Nat = add p;"
  , "def inc(n: Nat): Nat = suc n;"
  , "def init(u: Unit): Reply State = let n: Nat = iterate 1 from fold \"A\" from 0 with sum with inc in (\"\",right n);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

helperFoldSource :: String
helperFoldSource = unlines
  [ "type State = Nat;"
  , "def sum(p: Nat * Nat): Nat = add p;"
  , "def folded(u: Unit): Reply State = let n: Nat = fold \"A\" from 0 with sum in (\"\",right n);"
  , "def init(u: Unit): Reply State = folded(u);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

additionSource :: String
additionSource = unlines
  [ "type State = Nat;"
  , "def init(u: Unit): Reply State = (\"\",right add (4,7));"
  , "def step(x: Text * State): Reply State = let (input,state): Text * State = x in matchNat state of { 11 -> (\"eleven\\n\",left ()); n -> (\"wrong\\n\",left ()) };"
  ]

closedBoundExpressionSource :: String
closedBoundExpressionSource = unlines
  [ "type State = Nat;"
  , "def increment(n: Nat): Nat = suc n;"
  , "def init(u: Unit): Reply State = let n: Nat = iterate add (2,3) from 0 with increment in (\"\",right n);"
  , "def step(x: Text * State): Reply State = (\"\",left ());"
  ]

runtimeIterationSource :: String
runtimeIterationSource = unlines
  [ "type State = Nat;"
  , "def increment(n: Nat): Nat = suc n;"
  , "def repeat(n: Nat): Nat = iterate n from 0 with increment;"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right 2);"
  , "def step(request: Text * State): Reply State = let (input,fuel): Text * State = request in let _: Text = input in let result: Nat = repeat(fuel) in matchNat result of { 2 -> (\"two\\n\",left ()); n -> (\"bad\\n\",left ()); };"
  ]

runtimeFoldSource :: String
runtimeFoldSource = unlines
  [ "type State = Unit;"
  , "def sum(pair: Nat * Nat): Nat = add pair;"
  , "def sumText(input: Text): Nat = fold input from 0 with sum;"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right ());"
  , "def step(request: Text * State): Reply State = let (input,state): Text * State = request in let _: State = state in let result: Nat = sumText(input) in matchNat result of { 198 -> (\"sum\\n\",left ()); n -> (\"bad\\n\",left ()); };"
  ]

listConstructorSource :: String
listConstructorSource = unlines
  [ "type State = List Nat;"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right cons 1 onto cons 2 onto []);"
  , "def step(request: Text * State): Reply State = let (input,state): Text * State = request in let _: Text = input in let _: State = state in (\"\",left ());"
  ]

runtimeMapSource :: String
runtimeMapSource = unlines
  [ "type State = Unit;"
  , "def increment(n: Nat): Nat = suc n;"
  , "def incrementText(input: Text): Text = map input with increment;"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right ());"
  , "def step(request: Text * State): Reply State = let (input,state): Text * State = request in let _: State = state in let result: Text = incrementText(input) in matchText result of { \"BCD\" -> (\"mapped\\n\",left ()); other -> (\"bad\\n\",left ()); };"
  ]

wrongMapResultSource :: String
wrongMapResultSource = unlines
  [ "type State = Unit;"
  , "def discardNat(n: Nat): Unit = let _: Nat = n in ();"
  , "def bad(input: Text): Text = map input with discardNat;"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right ());"
  , "def step(request: Text * State): Reply State = let (input,state): Text * State = request in let _: Text = input in let _: State = state in (\"\",left ());"
  ]

runtimeWhileSource :: String
runtimeWhileSource = unlines
  [ "type State = Nat;"
  , "def increment(n: Nat): Nat = suc n;"
  , "def reachedThree(n: Nat): Unit + Unit = matchNat n of { 3 -> left (); n -> right (); };"
  , "def capped(fuel: Nat): Nat = while fuel from 0 testing reachedThree stepping increment;"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right 10);"
  , "def step(request: Text * State): Reply State = let (input,fuel): Text * State = request in let _: Text = input in let result: Nat = capped(fuel) in matchNat result of { 3 -> (\"three\\n\",left ()); n -> (\"bad\\n\",left ()); };"
  ]

openSeedSource :: String
openSeedSource = unlines
  [ "type State = Nat;"
  , "def increment(n: Nat): Nat = suc n;"
  , "def bad(request: Text * State): Reply State = let (input,state): Text * State = request in let _: Text = input in let (fuel,seed): Nat * Nat = copy state in let result: Nat = iterate fuel from seed with increment in (\"\",right result);"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right 0);"
  , "def step(request: Text * State): Reply State = bad(request);"
  ]

residualContextSource :: String
residualContextSource = unlines
  [ "type State = Nat;"
  , "def increment(n: Nat): Nat = suc n;"
  , "def bad(request: Text * State): Reply State = let (input,state): Text * State = request in let _: Text = input in let (fuel,extra): Nat * Nat = copy state in let result: Nat = iterate fuel from 0 with increment in (\"\",right add (result,extra));"
  , "def init(u: Unit): Reply State = let _: Unit = u in (\"\",right 0);"
  , "def step(request: Text * State): Reply State = bad(request);"
  ]
