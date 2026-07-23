module Tel2Vectors (tel2Vectors) where

import BoundVectors (tictactoeBoundVectors)
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
            , acceptsMapCBehavior "tel2 mapc runtime-selected mapper emits MapCS"
                mapcDemoSource ["ABC"] "chosen\n"
            , ("tel2 Prelude composeNat composes closures",
                preludeBehavior prelude composeNatUseSource "nine\n")
            , ("tel2 Prelude flipNat swaps closure arguments",
                preludeBehavior prelude flipNatUseSource "seven\n")
            , ("tel2 Prelude constNat captures and returns",
                preludeBehavior prelude constNatUseSource "five\n")
            , rejectsWith "tel2 rejects an open lambda as a reusable mapper"
                mapcOpenLambdaSource "must select among closed lambdas"
            ]
          syntaxSugar =
            [ accepts "tel2 accepts dash and block comments" commentSource
            , acceptsBehavior "tel2 if over a nonzero Nat takes the then branch"
                (ifNatSource "2") ["go"] "yes\n"
            , acceptsBehavior "tel2 if over zero takes the else branch"
                (ifNatSource "0") ["go"] "no\n"
            , acceptsBehavior "tel2 if over a data enum uses declaration tags"
                ifBoolSource ["go"] "true\n"
            , acceptsBehavior "tel2 list literal folds like its cons chain"
                listLiteralSource ["go"] "six\n"
            , acceptsBehavior "tel2 multi-argument lambda curries"
                multiArgLambdaSource ["go"] "five\n"
            , acceptsBehavior "tel2 multi-binding let nests"
                multiLetSource ["go"] "five\n"
            , rejects "tel2 rejects if without else"
                (small "if 1 then (\"\",left ()) ")
            , rejects "tel2 rejects legacy hash comments"
                "type State = Nat\n# legacy comment\nmain : Text * State -o Reply State = \\io -> io"
            , rejects "tel2 rejects the legacy apply keyword"
                (small "let f: Nat -o Nat = \\x -> x in apply(f, (\"\",left ()))")
            ]
          legacyRejections =
            [ rejects "tel2 rejects the legacy def keyword"
                "type State = Nat\ndef f(x: Nat): Nat = x\nmain : Text * State -o Reply State = \\io -> io"
            , rejects "tel2 rejects the matchNat keyword"
                (small "matchNat s of { 0 -> (\"\", left ()); k -> (\"\", left ()) }")
            , rejects "tel2 rejects the matchText keyword"
                (small "matchText input of { \"q\" -> (\"\", left ()); other -> (\"\", left ()) }")
            , rejects "tel2 rejects a semicolon declaration terminator"
                "type State = Nat;\nmain : Text * State -o Reply State = \\io -> io"
            , rejects "tel2 rejects braced case arms"
                (small "case s of { 0 -> (\"\", left ()); k -> (\"\", left ()) }")
            , rejects "tel2 rejects the cons-onto keyword form"
                (small "let xs : List Nat = cons 1 onto [] in let _ = xs in (\"\", left ())")
            , rejects "tel2 rejects the suc keyword builtin"
                (small "let m : Nat = suc 5 in let _ = m in (\"\", left ())")
            , rejectsWith "tel2 rejects a direct init/step entry"
                ("type State = Nat\n"
                  <> "init : Unit -o Reply State = \\u -> let _ = u in (\"\", left ())\n"
                  <> "step : Text * State -o Reply State = \\x -> let _ = x in (\"\", left ())")
                "declare main"
            , rejectsWith "tel2 requires a main entry"
                "type State = Nat\nhelper : Nat -o Nat = \\n -> n"
                "declare a main entry"
            ]
          syntaxApp =
            [ acceptsBehavior "tel2 juxtaposition calls a definition"
                chainDefSource ["go"] "ten\n"
            , acceptsBehavior "tel2 juxtaposition chains through a curried closure"
                chainClosureSource ["go"] "five\n"
            , acceptsBehavior "tel2 nested apply heads synthesize"
                nestedApplySource ["go"] "five\n"
            , acceptsBehavior "tel2 local closure shadows a definition in call position"
                shadowClosureSource ["go"] "local\n"
            , acceptsBehavior "tel2 call syntax applies a closure parameter"
                paramCallSource ["go"] "four\n"
            , acceptsBehavior "tel2 application chain stops at keywords"
                keywordBoundarySource ["go"] "three\n"
            , rejectsWith "tel2 rejects applying an enum constructor"
                conApplySource "take no payload"
            , rejects "tel2 rejects a keyword as an identifier"
                (small "let in: Nat = 1 in (\"\",left ())")
            ]
          syntaxInfer =
            [ acceptsBehavior "tel2 let infers a literal binding"
                inferLiteralSource ["go"] "seven\n"
            , acceptsBehavior "tel2 let infers a call-chain binding"
                inferCallSource ["go"] "ten\n"
            , acceptsBehavior "tel2 let infers a tuple split"
                inferTupleSource ["go"] "five\n"
            , acceptsBehavior "tel2 let infers a fold binding through placement"
                inferFoldSource ["go"] "three\n"
            , rejectsWith "tel2 asks for an annotation on an unannotated lambda"
                (small "let f = \\x -> x in (\"\",left ())") "annotate the binding"
            ]
          openSeeds =
            [ acceptsBehavior "tel2 promotes an open iteration seed (R2)"
                openSeedSource ["go"] "six\n"
            , acceptsBehavior "tel2 promotes an open fold seed (R2)"
                openFoldSeedSource ["go"] "eight\n"
            , acceptsBehavior "tel2 multiplies via an open pair seed (R2)"
                multiplySource ["go"] "twelve\n"
            ]
          closureLoops =
            [ acceptsBehavior "tel2 iterc runs a closure-bodied iteration"
                itercSource ["go"] "five\n"
            , acceptsBehavior "tel2 foldc folds with a closure body"
                foldcSource ["go"] "eight\n"
            , acceptsBehavior "tel2 whilec loops with closure test and step"
                whilecSource ["go"] "zero\n"
            , acceptsBehavior "tel2 mapc dispatches a mapper by matchText"
                mapcTextSource ["ABC"] "picked\n"
            , rejectsWith "tel2 rejects an open whilec stepping selector"
                whilecOpenStepSource "stepping selector must be closed"
            ]
          syntaxMain =
            [ acceptsBehavior "tel2 main entry synthesizes init and step"
                mainCounterSource ["go"] "start\ndone\n"
            , acceptsBehavior "tel2 main entry supports recursion through placement"
                mainFoldSource [] "three\n"
            , rejectsWith "tel2 rejects main alongside init/step"
                mainAndInitSource "pick one entry style"
            ]
          convergence =
            [ acceptsBehavior "tel2 signature-style definition compiles"
                sigDefSource [] "six\n"
            , acceptsBehavior "tel2 signature-style tuple lambda destructures"
                sigTupleSource [] "five\n"
            , acceptsBehavior "tel2 case over a Nat scrutinee matches literals"
                caseNatSource [] "two\n"
            , acceptsBehavior "tel2 case over a Text scrutinee matches strings"
                caseTextSource ["A"] "ask\nhit\n"
            , rejects "tel2 rejects a case with only a default arm"
                (small "case 1 of w -> (\"\", left ())")
            , acceptsBehavior "tel2 succ builtin applies by juxtaposition"
                succBuiltinSource [] "five\n"
            , acceptsBehavior "tel2 cons builtin builds a foldable list"
                consBuiltinSource [] "three\n"
            , acceptsBehavior "tel2 prepend builtin joins a literal onto text"
                prependBuiltinSource [] "abc\n"
            , acceptsBehavior "tel2 Reply main runs with a default Nat state"
                mainReplySource ["go"] "start\ndone\n"
            , acceptsBehavior "tel2 Reply main threads a structured state from start"
                mainStartSource ["go"] "first\nsecond\n"
            , rejectsWith "tel2 rejects Reply main without start for a structured state"
                mainNoStartSource "needs start"
            , acceptsBehavior "tel2 layout program parses without semicolons or braces"
                layoutSource ["go"] "start\ndone\n"
            , acceptsBehavior "tel2 layout enum case aligns its arms"
                layoutEnumSource [] "five\n"
            , acceptsBehavior "tel2 layout nested case ends at the outer arm column"
                layoutNestedSource [] "two\n"
            , acceptsBehavior "tel2 recursion triple stops immediately via last"
                tripleIdSource [] "seven\n"
            , acceptsBehavior "tel2 recursion triple recurses one level"
                tripleOneStepSource [] "one\n"
            , acceptsBehavior "tel2 structural deconstructors: succ and cons"
                deconSource [] "eleven\n"
            , acceptsBehavior "tel2 sum deconstructor picks left and right"
                deconSumSource [] "both\n"
            , acceptsBehavior "tel2 nat-driven recursion peels via succ, fuel = value"
                natRecSource [] "five\n"
            , rejectsWith "tel2 rejects a list-state triple (fuel not measurable)"
                listStateRejectSource "cannot calculate recursion fuel"
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
            , rejectsWith "tel2 rejects an open closure-typed seed"
                closureSeedSource "closures cannot be promoted"
            , rejectsWith "tel2 rejects live context after recursion" residualContextSource "cannot remain live"
            , rejects "tel2 rejects a map mapper with the wrong result type" wrongMapResultSource
            ]
          needsPrelude = ("tictactoe genuinely depends on imported Prelude",
            case compileTel2 (anonymous source) of Left _ -> True; Right _ -> False)
          mutation = sourceMutation (anonymous prelude <> anonymous source)
          bounds = tictactoeBoundVectors program
      pure (compiled : explicit : namedData : forward : closedBounds : addition : packagedPrelude : packagedMap
        : cwdIndependent : localShadow : headerMismatch
        : needsPrelude : needsLegacy : mutation
        : importCycle : missing : bounds <> closures <> syntaxSugar <> legacyRejections <> syntaxApp <> syntaxInfer <> syntaxMain <> convergence <> openSeeds <> closureLoops <> implicitCopy <> recursion <> reusableRecursion <> illegalRecursion <> malformed <> games)

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
        (exampleIntroduction, 22))
  ]

modalShape :: Program -> Bool
modalShape program =
  count isBoxVal == 4
    && count isIter == 1
    && count isFold == 1
    && count isWhile == 1
    && count isMerge == 3
    && count isBox == 2
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

programHasMapC :: Program -> Bool
programHasMapC = programHasShape isMapC
  where
    isMapC ShMapC = True
    isMapC _      = False

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

acceptsMapCBehavior :: String -> String -> [String] -> String -> (String, Bool)
acceptsMapCBehavior name source inputs expected = (name, case compileTel2 source of
  Left _ -> False
  Right program -> programHasMapC program && case runProgramScript program inputs of
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
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in " <> initial
  ]

copySource :: String
copySource = unlines
  [ "type State = Nat * Nat"
  , "start : Unit -o State = \\u -> let p : Nat * Nat = copy 7 in p"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", left ())"
  ]

duplicateSource :: String
duplicateSource = unlines
  [ "type State = Nat * Nat"
  , "start : Unit -o State = \\u -> let n : Nat = 7 in (n, n)"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", left ())"
  ]

implicitListReuseSource :: String
implicitListReuseSource = unlines
  [ "type State = List Nat * List Nat"
  , "dupList : List Nat -o List Nat * List Nat = \\xs -> (xs, xs)"
  , "start : Unit -o State = \\u -> dupList (cons 1 [])"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", left ())"
  ]

implicitNatReuseSource :: String
implicitNatReuseSource = unlines
  [ "type State = Nat"
  , "double : Nat -o Nat = \\n -> add (n, n)"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 5)"
  , "        n -> let _ = input in"
  , "             case double n of"
  , "               10 -> (\"ten\\n\", left ())"
  , "               m -> (\"bad\\n\", left ())"
  ]

commentSource :: String
commentSource = unlines
  [ "-- dash comment before declarations"
  , "{- block comment {- nested -} still a comment -}"
  , "type State = Nat"
  , "main : Text * State -o Reply State = \\x -> {- inline -} let (t, s) = x in let _ = t in let _ = s in (\"\", left ()) -- trailing dash comment"
  ]

ifNatSource :: String -> String
ifNatSource seed = unlines
  [ "type State = Nat * Nat"
  , "start : Unit -o State = \\u -> (0, " <> seed <> ")"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, st) = x"
  , "      (flag, n) = st"
  , "   in case flag of"
  , "        0 -> let _ = input in (\"\", right (1, n))"
  , "        k -> let _ = k in let _ = input in (if n then \"yes\\n\" else \"no\\n\", left ())"
  ]

ifBoolSource :: String
ifBoolSource = unlines
  [ "data Bool = False | True"
  , "type State = Nat"
  , "toBool : Nat -o Bool = \\n ->"
  , "  case n of"
  , "    0 -> False"
  , "    _ -> True"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in (if toBool n then \"true\\n\" else \"false\\n\", left ())"
  ]

listLiteralSource :: String
listLiteralSource = unlines
  [ "type State = Nat"
  , "plus : Nat * Nat -o Nat = \\p -> add p"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in let _ = n in"
  , "             let total : Nat = fold [1, 2, 3] from 0 with plus"
  , "              in case total of"
  , "                   6 -> (\"six\\n\", left ())"
  , "                   m -> let _ = m in (\"bad\\n\", left ())"
  ]

multiArgLambdaSource :: String
multiArgLambdaSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in let _ = n in"
  , "             let f : Nat -o Nat -o Nat = \\a b -> add (a, b)"
  , "                 g : Nat -o Nat = f 2"
  , "              in case g 3 of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   m -> let _ = m in (\"bad\\n\", left ())"
  ]

multiLetSource :: String
multiLetSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input"
  , "                 _ = n"
  , "                 a : Nat = 2"
  , "                 b : Nat = 3"
  , "              in case add (a, b) of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   m -> let _ = m in (\"bad\\n\", left ())"
  ]

chainDefSource :: String
chainDefSource = unlines
  [ "type State = Nat"
  , "double : Nat -o Nat = \\n -> add (n, n)"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 5)"
  , "        n -> let _ = input in"
  , "             case double n of"
  , "               10 -> (\"ten\\n\", left ())"
  , "               m -> let _ = m in (\"bad\\n\", left ())"
  ]

chainClosureSource :: String
chainClosureSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in let _ = n in"
  , "             let f : Nat -o Nat -o Nat = \\a b -> add (a, b)"
  , "              in case f 2 3 of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   m -> let _ = m in (\"bad\\n\", left ())"
  ]

nestedApplySource :: String
nestedApplySource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in let _ = n in"
  , "             let f : Nat -o Nat -o Nat = \\a b -> add (a, b)"
  , "              in case (f 2) 3 of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   m -> let _ = m in (\"bad\\n\", left ())"
  ]

shadowClosureSource :: String
shadowClosureSource = unlines
  [ "type State = Nat"
  , "inc : Nat -o Nat = \\n -> succ n"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in let _ = n in"
  , "             let inc : Nat -o Nat = \\a -> add (a, a)"
  , "              in case inc 4 of"
  , "                   8 -> (\"local\\n\", left ())"
  , "                   m -> let _ = m in (\"bad\\n\", left ())"
  ]

paramCallSource :: String
paramCallSource = unlines
  [ "type State = Nat"
  , "useIt : (Nat -o Nat) -o Nat = \\f -> f(3)"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in let _ = n in"
  , "             case useIt(\\a -> succ a) of"
  , "               4 -> (\"four\\n\", left ())"
  , "               m -> let _ = m in (\"bad\\n\", left ())"
  ]

keywordBoundarySource :: String
keywordBoundarySource = unlines
  [ "type State = Nat"
  , "double : Nat -o Nat = \\n -> add (n, n)"
  , "plus : Nat * Nat -o Nat = \\p -> add p"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in let _ = n in"
  , "             let total : Nat = fold [1, 2] from double 0 with plus"
  , "              in case total of"
  , "                   3 -> (\"three\\n\", left ())"
  , "                   m -> let _ = m in (\"bad\\n\", left ())"
  ]

inferLiteralSource :: String
inferLiteralSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 7)"
  , "        n -> let _ = input in"
  , "             let m = n"
  , "              in case m of"
  , "                   7 -> (\"seven\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  ]

inferCallSource :: String
inferCallSource = unlines
  [ "type State = Nat"
  , "double : Nat -o Nat = \\n -> add (n, n)"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in let _ = n in"
  , "             let d = double 5"
  , "              in case d of"
  , "                   10 -> (\"ten\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  ]

inferTupleSource :: String
inferTupleSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, n) = x"
  , "   in case n of"
  , "        0 -> let _ = input in (\"\", right 5)"
  , "        m -> let _ = input in"
  , "             case m of"
  , "               5 -> (\"five\\n\", left ())"
  , "               k -> let _ = k in (\"bad\\n\", left ())"
  ]

inferFoldSource :: String
inferFoldSource = unlines
  [ "type State = Nat"
  , "plus : Nat * Nat -o Nat = \\p -> add p"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = input in let _ = n in"
  , "             let total = fold [1, 2] from 0 with plus"
  , "              in case total of"
  , "                   3 -> (\"three\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  ]

mainCounterSource :: String
mainCounterSource = unlines
  [ "main : Text * Nat -o Text * Nat = \\io ->"
  , "  let (input, count) = io"
  , "      _ = input"
  , "   in case count of"
  , "        0 -> (\"start\\n\", 1)"
  , "        1 -> (\"done\\n\", 0)"
  , "        k -> let _ = k in (\"bad\\n\", 0)"
  ]

mainFoldSource :: String
mainFoldSource = unlines
  [ "plus : Nat * Nat -o Nat = \\p -> add p"
  , "main : Text * Nat -o Text * Nat = \\io ->"
  , "  let (input, count) = io"
  , "      _ = input"
  , "      _ = count"
  , "      total = fold [1, 2] from 0 with plus"
  , "   in case total of"
  , "        3 -> (\"three\\n\", 0)"
  , "        k -> let _ = k in (\"bad\\n\", 0)"
  ]

sigDefSource :: String
sigDefSource = unlines
  [ "type State = Nat"
  , "double : Nat -o Nat = \\n -> add (n, n)"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (t, s) = x"
  , "   in case s of"
  , "        0 -> let _ = t in"
  , "             let m = double 3"
  , "              in case m of"
  , "                   6 -> (\"six\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = t in let _ = n in (\"\", left ())"
  ]

sigTupleSource :: String
sigTupleSource = unlines
  [ "type State = Nat"
  , "plus : Nat * Nat -o Nat = \\(a, b) -> add (a, b)"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (t, s) = x"
  , "   in case s of"
  , "        0 -> let _ = t in"
  , "             let m = plus (2, 3)"
  , "              in case m of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = t in let _ = n in (\"\", left ())"
  ]

caseNatSource :: String
caseNatSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (t, s) = x"
  , "   in case s of"
  , "        0 -> let _ = t in"
  , "             case 2 of"
  , "               0 -> (\"zero\\n\", left ())"
  , "               w -> let _ = w in (\"two\\n\", left ())"
  , "        n -> let _ = t in let _ = n in (\"\", left ())"
  ]

caseTextSource :: String
caseTextSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"ask\\n\", right 1)"
  , "        n -> let _ = n in"
  , "             case input of"
  , "               \"A\" -> (\"hit\\n\", left ())"
  , "               _ -> (\"miss\\n\", left ())"
  ]

succBuiltinSource :: String
succBuiltinSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (t, s) = x"
  , "   in case s of"
  , "        0 -> let _ = t in"
  , "             let m = succ 4"
  , "              in case m of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = t in let _ = n in (\"\", left ())"
  ]

consBuiltinSource :: String
consBuiltinSource = unlines
  [ "type State = Nat"
  , "plus : Nat * Nat -o Nat = \\p -> add p"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (t, s) = x"
  , "   in case s of"
  , "        0 -> let _ = t in"
  , "             let xs : List Nat = cons 1 (cons 2 [])"
  , "                 total = fold xs from 0 with plus"
  , "              in case total of"
  , "                   3 -> (\"three\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = t in let _ = n in (\"\", left ())"
  ]

prependBuiltinSource :: String
prependBuiltinSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in"
  , "             let t = prepend \"ab\" \"c\\n\""
  , "              in (t, left ())"
  , "        n -> let _ = input in let _ = n in (\"\", left ())"
  ]

mainReplySource :: String
mainReplySource = unlines
  [ "main : Text * State -o Reply State = \\io ->"
  , "  let (input, count) = io"
  , "      _ = input"
  , "   in case count of"
  , "        0 -> (\"start\\n\", right 1)"
  , "        k -> let _ = k in (\"done\\n\", left ())"
  ]

mainStartSource :: String
mainStartSource = unlines
  [ "type State = Nat * Nat"
  , "start : Unit -o State = \\u -> (0, 7)"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, st) = io"
  , "      _ = input"
  , "      (flag, kept) = st"
  , "   in case flag of"
  , "        0 -> (\"first\\n\", right (1, kept))"
  , "        k -> let _ = k in let _ = kept in (\"second\\n\", left ())"
  ]

mainNoStartSource :: String
mainNoStartSource = unlines
  [ "type State = Nat * Nat"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, st) = io"
  , "      _ = input"
  , "      (flag, kept) = st"
  , "   in case flag of"
  , "        0 -> (\"first\\n\", right (1, kept))"
  , "        k -> let _ = k in let _ = kept in (\"second\\n\", left ())"
  ]

layoutSource :: String
layoutSource = unlines
  [ "type State = Nat"
  , ""
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, count) = io"
  , "      _ = input"
  , "   in case count of"
  , "        0 -> (\"start\\n\", right 1)"
  , "        k -> let _ = k in (\"done\\n\", left ())"
  ]

layoutEnumSource :: String
layoutEnumSource = unlines
  [ "data Answer = No | Yes"
  , "type State = Nat"
  , ""
  , "pick : Answer -o Nat = \\a ->"
  , "  case a of"
  , "    No -> 3"
  , "    Yes -> 5"
  , ""
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let m = pick Yes"
  , "              in case m of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = n in (\"\", left ())"
  ]

layoutNestedSource :: String
layoutNestedSource = unlines
  [ "type State = Nat"
  , ""
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> case 2 of"
  , "               0 -> (\"zero\\n\", left ())"
  , "               j -> case j of"
  , "                      2 -> (\"two\\n\", left ())"
  , "                      k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = n in (\"\", left ())"
  ]

-- RT2 closed-slot recursion triple: test stops at once, last returns the
-- value (identity). No captures, no decrement.
tripleIdSource :: String
tripleIdSource = unlines
  [ "type State = Nat"
  , "stopNow : Nat -o Unit + Unit = \\m -> let _ = m in left ()"
  , "idRec : Nat -o Nat = \\n ->"
  , "  let f : Nat -o Nat = { \\m -> stopNow m, \\recur m -> succ (recur m), \\m -> m }"
  , "   in f n"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let r = idRec 7"
  , "              in case r of"
  , "                   7 -> (\"seven\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = n in (\"\", left ())"
  ]

-- One genuine recursion level: test continues once, rec applies recur to a
-- state whose next test stops, then wraps the base result in succ.
tripleOneStepSource :: String
tripleOneStepSource = unlines
  [ "type State = Nat"
  , "isNonzero : Nat -o Unit + Unit = \\m ->"
  , "  case m of"
  , "    0 -> left ()"
  , "    w -> let _ = w in right ()"
  , "oneStep : Nat -o Nat = \\n ->"
  , "  let f : Nat -o Nat = { \\m -> isNonzero m, \\recur m -> let _ = m in succ (recur 0), \\m -> m }"
  , "   in f n"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let r = oneStep 5"
  , "              in case r of"
  , "                   1 -> (\"one\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = n in (\"\", left ())"
  ]

-- Structural deconstructors: predecessor (succ k) and uncons (cons h t).
deconSource :: String
deconSource = unlines
  [ "type State = Nat"
  , "predOr0 : Nat -o Nat = \\n ->"
  , "  case n of"
  , "    0 -> 0"
  , "    succ k -> k"
  , "headOr0 : List Nat -o Nat = \\xs ->"
  , "  case xs of"
  , "    [] -> 0"
  , "    cons h t -> let _ = t in h"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let a = predOr0 5"
  , "                 b = headOr0 (cons 7 (cons 8 []))"
  , "              in case add (a, b) of"
  , "                   11 -> (\"eleven\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = n in (\"\", left ())"
  ]

-- Sum deconstructor: left/right elimination.
deconSumSource :: String
deconSumSource = unlines
  [ "type State = Nat"
  , "pick : Nat + Nat -o Nat = \\s ->"
  , "  case s of"
  , "    left l -> l"
  , "    right r -> r"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let a = pick (left 3)"
  , "                 b = pick (right 4)"
  , "              in case add (a, b) of"
  , "                   7 -> (\"both\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = n in (\"\", left ())"
  ]

-- Nat-driven recursion: peels the state nat via succ; the calculated fuel
-- is the nat's own value, so it reaches the base exactly.
natRecSource :: String
natRecSource = unlines
  [ "type State = Nat"
  , "isNonzero : Nat -o Unit + Unit = \\m ->"
  , "  case m of"
  , "    0 -> left ()"
  , "    w -> let _ = w in right ()"
  , "countId : Nat -o Nat = \\n ->"
  , "  let f : Nat -o Nat ="
  , "        { \\m -> isNonzero m"
  , "        , \\recur m -> case m of"
  , "                        0 -> 0"
  , "                        succ k -> succ (recur k)"
  , "        , \\m -> let _ = m in 0 }"
  , "   in f n"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let r = countId 5"
  , "              in case r of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = n in (\"\", left ())"
  ]

-- A list-state triple cannot have its fuel measured directly (list length
-- needs a fold); the compiler rejects it with guidance to use fold/map.
listStateRejectSource :: String
listStateRejectSource = unlines
  [ "type State = Nat"
  , "isEmpty : List Nat -o Unit + Unit = \\l ->"
  , "  case l of"
  , "    [] -> left ()"
  , "    cons h t -> let _ = h in let _ = t in right ()"
  , "listLen : List Nat -o Nat = \\xs ->"
  , "  let f : List Nat -o Nat ="
  , "        { \\l -> isEmpty l"
  , "        , \\recur l -> case l of"
  , "                        [] -> 0"
  , "                        cons h t -> let _ = h in succ (recur t)"
  , "        , \\l -> let _ = l in 0 }"
  , "   in f xs"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let r = listLen (cons 7 [])"
  , "              in case r of"
  , "                   1 -> (\"one\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  , "        n -> let _ = n in (\"\", left ())"
  ]

mainAndInitSource :: String
mainAndInitSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Text * State = \\io -> io"
  , "init : Unit -o Reply State = \\u -> let _ = u in (\"\", left ())"
  , "step : Text * State -o Reply State = \\x -> let _ = x in (\"\", left ())"
  ]

conApplySource :: String
conApplySource = unlines
  [ "data Answer = No | Yes"
  , "type State = Nat"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in let b : Nat = Yes 5 in let _ : Nat = b in (\"\", left ())"
  ]

preludeBehavior :: String -> String -> String -> Bool
preludeBehavior prelude source expected =
  case compileTel2 (anonymous prelude <> source) of
    Left _ -> False
    Right program -> case runProgramScript program ["go"] of
      Right (output, _) -> output == expected
      Left _            -> False

flipNatUseSource :: String
flipNatUseSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 7)"
  , "        n -> let _ = input in"
  , "             let f : Nat * Nat -o Nat = flipNat(\\p -> let (a, b) : Nat * Nat = p in a)"
  , "              in case f (0, n) of"
  , "                   7 -> (\"seven\\n\", left ())"
  , "                   m -> (\"bad\\n\", left ())"
  ]

constNatUseSource :: String
constNatUseSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 9)"
  , "        n -> let _ = input in let _ = n in"
  , "             let f : Nat -o Nat = constNat(5)"
  , "              in case f 0 of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   m -> (\"bad\\n\", left ())"
  ]

composeNatUseSource :: String
composeNatUseSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 7)"
  , "        n -> let _ = input in"
  , "             let f : Nat -o Nat = composeNat((\\a -> succ a, \\b -> succ b))"
  , "              in case f n of"
  , "                   9 -> (\"nine\\n\", left ())"
  , "                   m -> (\"bad\\n\", left ())"
  ]

mapcDemoSource :: String
mapcDemoSource = unlines
  [ "type State = Nat"
  , "transform : Nat * Text -o Text = \\input ->"
  , "  let (flag, text) = input"
  , "   in mapc text with"
  , "        case flag of"
  , "          0 -> \\n -> succ n"
  , "          _ -> \\n -> add (n, n)"
  , "main : Text * State -o Reply State = \\request ->"
  , "  let (input, s) = request"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = n in"
  , "             let result : Text = transform (0, input)"
  , "              in case result of"
  , "                   \"BCD\" -> (\"chosen\\n\", left ())"
  , "                   other -> (\"bad\\n\", left ())"
  ]

mapcOpenLambdaSource :: String
mapcOpenLambdaSource = unlines
  [ "type State = Nat"
  , "addToAll : Nat * Text -o Text = \\input ->"
  , "  let (amount, text) = input"
  , "   in mapc text with \\n -> add (amount, n)"
  , "main : Text * State -o Reply State = \\x -> let (input, s) = x in let _ = s in let result : Text = addToAll (1, input) in (\"done\\n\", left ())"
  ]

makeAdderSource :: String
makeAdderSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 5)"
  , "        amount -> let _ = input in"
  , "                  let adder : Nat -o Nat = \\value -> add (amount, value)"
  , "                   in case adder 7 of"
  , "                        12 -> (\"twelve\\n\", left ())"
  , "                        m -> (\"bad\\n\", left ())"
  ]

chooseOperationSource :: String
chooseOperationSource = unlines
  [ "type State = Nat"
  , "pick : Nat -o Nat -o Nat = \\flag ->"
  , "  case flag of"
  , "    0 -> \\n -> succ n"
  , "    _ -> \\n -> add (n, n)"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 3)"
  , "        n -> let _ = input in"
  , "             let f : Nat -o Nat = pick n"
  , "              in case f n of"
  , "                   6 -> (\"six\\n\", right n)"
  , "                   m -> (\"bad\\n\", left ())"
  ]

composeSource :: String
composeSource = unlines
  [ "type State = Nat"
  , "compose : (Nat -o Nat) * (Nat -o Nat) -o Nat -o Nat = \\fs ->"
  , "  let (first, second) : (Nat -o Nat) * (Nat -o Nat) = fs"
  , "   in \\value -> second (first value)"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 7)"
  , "        n -> let _ = input in"
  , "             let f : Nat -o Nat = compose((\\a -> succ a, \\b -> succ b))"
  , "              in case f n of"
  , "                   9 -> (\"nine\\n\", left ())"
  , "                   m -> (\"bad\\n\", left ())"
  ]

closureReuseSource :: String
closureReuseSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in let f : Nat -o Nat = \\n -> succ n in (\"\", right add (f 1, f 2))"
  ]

closureCopySource :: String
closureCopySource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in let f : Nat -o Nat = \\n -> succ n in let (g, h) : (Nat -o Nat) * (Nat -o Nat) = copy f in (\"\", right add (g 1, h 2))"
  ]

closureStateSource :: String
closureStateSource = unlines
  [ "type State = Nat -o Nat"
  , "start : Unit -o State = \\u -> \\n -> succ n"
  , "main : Text * State -o Reply State = \\io -> let (input, f) = io in let _ = input in (\"\", right f)"
  ]

scrutineeReuseSource :: String
scrutineeReuseSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 3)"
  , "        n -> let _ = input in"
  , "             case n of"
  , "               0 -> (\"zero\\n\", left ())"
  , "               _ -> (\"sum\\n\", right add (n, n))"
  ]

dataSource :: String
dataSource = unlines
  [ "data Flag = No | Yes"
  , "type State = Nat"
  , "choose : Flag -o Nat = \\f ->"
  , "  case f of"
  , "    No -> 0"
  , "    Yes -> 1"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", right (choose Yes))"
  ]

cyclicAliasSource :: String
cyclicAliasSource = unlines
  [ "type A = B"
  , "type B = A"
  , "type State = Nat"
  , "useA : A -o Nat = \\x -> let _ = x in 0"
  , "main : Text * State -o Reply State = \\io -> let (input, s) = io in let _ = input in let _ = s in (\"\", left ())"
  ]

incompleteCaseSource :: String
incompleteCaseSource = unlines
  [ "data Flag = No | Yes"
  , "type State = Nat"
  , "choose : Flag -o Nat = \\f ->"
  , "  case f of"
  , "    No -> 0"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", right (choose No))"
  ]

duplicateBinderSource :: String
duplicateBinderSource = unlines
  [ "type State = Nat"
  , "bad : Nat * Nat -o Nat = \\p -> let (x, x) : Nat * Nat = p in x"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", left ())"
  ]

forwardReferenceSource :: String
forwardReferenceSource = unlines
  [ "type State = Later"
  , "start : Unit -o State = \\u -> make u"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", left ())"
  , "make : Unit -o Later = \\u -> let _ = u in 7"
  , "type Later = Nat"
  ]

cyclicDefinitionSource :: String
cyclicDefinitionSource = unlines
  [ "type State = Nat"
  , "a : Nat -o Nat = \\n -> b n"
  , "b : Nat -o Nat = \\n -> a n"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", left ())"
  ]

-- A main whose fresh arm runs a two-binding closed-loop chain. That chain
-- is the path that still requires every bound, seed, and input to be
-- closed (compileClosedLoop); a lone open Ground seed is instead promoted
-- (M4), so the chain is where an offending first loop is rejected. `k` is
-- an in-scope Nat the offending loop can capture.
closedChainMain :: String -> String
closedChainMain offending = unlines
  [ "type State = Nat"
  , "inc : Nat -o Nat = \\n -> succ n"
  , "sum : Nat * Nat -o Nat = \\p -> add p"
  , "stop : Nat -o Unit + Unit = \\n -> let _ = n in left ()"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let k : Nat = 5"
  , "              in let a : Nat = " <> offending
  , "                     b : Nat = iterate 1 from 0 with inc"
  , "                     _ = a"
  , "                     _ = b"
  , "                  in (\"\", right 1)"
  , "        n -> let _ = n in (\"\", left ())"
  ]

capturedSeedSource :: String
capturedSeedSource = closedChainMain "iterate 1 from k with inc"

capturedBoundSource :: String
capturedBoundSource = closedChainMain "iterate k from 0 with inc"

capturedContinuationSource :: String
capturedContinuationSource = unlines
  [ "type State = Nat"
  , "inc : Nat -o Nat = \\n -> succ n"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let k : Nat = 5"
  , "              in let a : Nat = iterate 1 from 0 with inc"
  , "                     b : Nat = iterate 1 from 0 with inc"
  , "                     _ = a"
  , "                     _ = b"
  , "                  in (\"\", right k)"
  , "        n -> let _ = n in (\"\", left ())"
  ]

helperIterationSource :: String
helperIterationSource = unlines
  [ "type State = Nat"
  , "increment : Nat -o Nat = \\n -> succ n"
  , "count : Unit -o Reply State = \\u -> let _ = u in let n : Nat = iterate 2 from 0 with increment in (\"\", right n)"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in count ()"
  ]

capturedFoldInputSource :: String
capturedFoldInputSource = closedChainMain "fold (cons k []) from 0 with sum"

capturedFoldSeedSource :: String
capturedFoldSeedSource = closedChainMain "fold \"A\" from k with sum"

capturedWhileSeedSource :: String
capturedWhileSeedSource = closedChainMain "while 1 from k testing stop stepping inc"

nestedRecursionSource :: String
nestedRecursionSource = unlines
  [ "type State = Nat"
  , "sum : Nat * Nat -o Nat = \\p -> add p"
  , "inc : Nat -o Nat = \\n -> succ n"
  , "main : Text * State -o Reply State = \\io ->"
  , "  let (input, s) = io"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> let a : Nat = iterate 1 from fold \"A\" from 0 with sum with inc"
  , "                 b : Nat = iterate 1 from 0 with inc"
  , "                 _ = a"
  , "                 _ = b"
  , "              in (\"\", right 1)"
  , "        n -> let _ = n in (\"\", left ())"
  ]

helperFoldSource :: String
helperFoldSource = unlines
  [ "type State = Nat"
  , "sum : Nat * Nat -o Nat = \\p -> add p"
  , "folded : Unit -o Reply State = \\u -> let _ = u in let n : Nat = fold \"A\" from 0 with sum in (\"\", right n)"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in folded ()"
  ]

additionSource :: String
additionSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> (\"\", right add (4, 7))"
  , "        11 -> (\"eleven\\n\", left ())"
  , "        n -> let _ = n in (\"wrong\\n\", left ())"
  ]

closedBoundExpressionSource :: String
closedBoundExpressionSource = unlines
  [ "type State = Nat"
  , "increment : Nat -o Nat = \\n -> succ n"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in let n : Nat = iterate add (2, 3) from 0 with increment in (\"\", right n)"
  ]

runtimeIterationSource :: String
runtimeIterationSource = unlines
  [ "type State = Nat"
  , "increment : Nat -o Nat = \\n -> succ n"
  , "repeat : Nat -o Nat = \\n -> iterate n from 0 with increment"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 2)"
  , "        fuel -> let _ = input in"
  , "                let result : Nat = repeat fuel"
  , "                 in case result of"
  , "                      2 -> (\"two\\n\", left ())"
  , "                      n -> (\"bad\\n\", left ())"
  ]

runtimeFoldSource :: String
runtimeFoldSource = unlines
  [ "type State = Nat"
  , "sum : Nat * Nat -o Nat = \\pair -> add pair"
  , "sumText : Text -o Nat = \\input -> fold input from 0 with sum"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = n in"
  , "             let result : Nat = sumText input"
  , "              in case result of"
  , "                   198 -> (\"sum\\n\", left ())"
  , "                   m -> (\"bad\\n\", left ())"
  ]

listConstructorSource :: String
listConstructorSource = unlines
  [ "type State = List Nat"
  , "start : Unit -o State = \\u -> cons 1 (cons 2 [])"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", left ())"
  ]

runtimeMapSource :: String
runtimeMapSource = unlines
  [ "type State = Nat"
  , "increment : Nat -o Nat = \\n -> succ n"
  , "incrementText : Text -o Text = \\input -> map input with increment"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = n in"
  , "             let result : Text = incrementText input"
  , "              in case result of"
  , "                   \"BCD\" -> (\"mapped\\n\", left ())"
  , "                   other -> (\"bad\\n\", left ())"
  ]

wrongMapResultSource :: String
wrongMapResultSource = unlines
  [ "type State = Nat"
  , "discardNat : Nat -o Unit = \\n -> let _ : Nat = n in ()"
  , "bad : Text -o Text = \\input -> map input with discardNat"
  , "main : Text * State -o Reply State = \\x -> let (t, s) = x in let _ = t in let _ = s in (\"\", left ())"
  ]

runtimeWhileSource :: String
runtimeWhileSource = unlines
  [ "type State = Nat"
  , "increment : Nat -o Nat = \\n -> succ n"
  , "reachedThree : Nat -o Unit + Unit = \\n ->"
  , "  case n of"
  , "    3 -> left ()"
  , "    _ -> right ()"
  , "capped : Nat -o Nat = \\fuel -> while fuel from 0 testing reachedThree stepping increment"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 10)"
  , "        fuel -> let _ = input in"
  , "                let result : Nat = capped fuel"
  , "                 in case result of"
  , "                      3 -> (\"three\\n\", left ())"
  , "                      n -> (\"bad\\n\", left ())"
  ]

openSeedSource :: String
openSeedSource = unlines
  [ "type State = Nat"
  , "increment : Nat -o Nat = \\n -> succ n"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 3)"
  , "        n -> let _ = input in"
  , "             let (fuel, seed) = copy n"
  , "                 result = iterate fuel from seed with increment"
  , "              in case result of"
  , "                   6 -> (\"six\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  ]

openFoldSeedSource :: String
openFoldSeedSource = unlines
  [ "type State = Nat"
  , "double : Nat -o Nat = \\n -> add (n, n)"
  , "plus : Nat * Nat -o Nat = \\p -> add p"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        seed -> let _ = input in"
  , "                let total = fold [1, 2, 3] from double seed with plus"
  , "                 in case total of"
  , "                      8 -> (\"eight\\n\", left ())"
  , "                      k -> let _ = k in (\"bad\\n\", left ())"
  ]

multiplySource :: String
multiplySource = unlines
  [ "type State = Nat"
  , "timesStep : Nat * Nat -o Nat * Nat = \\p ->"
  , "  let (acc, a) = p"
  , "      (a1, a2) = copy a"
  , "   in (add (acc, a1), a2)"
  , "main : Text * State -o Reply State = \\x ->"
  , "  let (input, s) = x"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 4)"
  , "        n -> let _ = input in"
  , "             let pair = iterate 3 from (0, n) with timesStep"
  , "                 (result, rest) = pair"
  , "                 _ = rest"
  , "              in case result of"
  , "                   12 -> (\"twelve\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  ]

itercSource :: String
itercSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\request ->"
  , "  let (input, s) = request"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 5)"
  , "        n -> let _ = input in"
  , "             let total = iterc n from 0 with \\y -> succ y"
  , "              in case total of"
  , "                   5 -> (\"five\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  ]

foldcSource :: String
foldcSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\request ->"
  , "  let (input, s) = request"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 2)"
  , "        n -> let _ = input in"
  , "             let total = foldc [1, 2, 3] from n with \\(acc, y) -> add (acc, y)"
  , "              in case total of"
  , "                   8 -> (\"eight\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  ]

whilecSource :: String
whilecSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\request ->"
  , "  let (input, s) = request"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 3)"
  , "        n -> let _ = input in"
  , "             let total = whilec 9 from n"
  , "                           testing \\y ->"
  , "                             case y of"
  , "                               0 -> left ()"
  , "                               k -> let _ = k in right ()"
  , "                           stepping \\y -> let _ = y in 0"
  , "              in case total of"
  , "                   0 -> (\"zero\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  ]

mapcTextSource :: String
mapcTextSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\request ->"
  , "  let (input, s) = request"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 1)"
  , "        n -> let _ = n in"
  , "             let ys : List Nat = mapc (cons 65 []) with"
  , "                                   case input of"
  , "                                     \"ABC\" -> \\y -> succ y"
  , "                                     _ -> \\y -> y"
  , "              in case ys of"
  , "                   \"B\" -> (\"picked\\n\", left ())"
  , "                   k -> let _ = k in (\"bad\\n\", left ())"
  ]

whilecOpenStepSource :: String
whilecOpenStepSource = unlines
  [ "type State = Nat"
  , "main : Text * State -o Reply State = \\request ->"
  , "  let (input, s) = request"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 3)"
  , "        n -> let _ = input in"
  , "             let (a, b) = copy n"
  , "                 total = whilec 9 from a"
  , "                           testing \\y ->"
  , "                             case y of"
  , "                               0 -> left ()"
  , "                               k -> let _ = k in right ()"
  , "                           stepping \\y -> let _ = y in b"
  , "              in let _ = total in (\"done\\n\", left ())"
  ]

closureSeedSource :: String
closureSeedSource = unlines
  [ "type State = Nat"
  , "stepc : (Nat -o Nat) -o Nat -o Nat = \\f -> f"
  , "main : Text * State -o Reply State = \\request ->"
  , "  let (input, s) = request"
  , "   in case s of"
  , "        0 -> let _ = input in (\"\", right 0)"
  , "        n -> let _ = input in"
  , "             let f : Nat -o Nat = \\y -> add (y, n)"
  , "                 g = iterate 2 from f with stepc"
  , "              in let _ = g 1 in (\"done\\n\", left ())"
  ]

residualContextSource :: String
residualContextSource = unlines
  [ "type State = Nat"
  , "increment : Nat -o Nat = \\n -> succ n"
  , "main : Text * State -o Reply State = \\request ->"
  , "  let (input, s) = request"
  , "      _ = input"
  , "   in case s of"
  , "        0 -> (\"\", right 3)"
  , "        n -> let (fuel, extra) = copy n"
  , "              in let result : Nat = iterate fuel from 0 with increment"
  , "                  in (\"\", right add (result, extra))"
  ]
