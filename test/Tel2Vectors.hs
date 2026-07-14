module Tel2Vectors (tel2Vectors) where

import Data.List (isInfixOf)
import System.Directory (doesFileExist)

import Telomare.CoreMachine

baseDir :: IO FilePath
baseDir = do
  here <- doesFileExist "test/programs/tictactoe.tel2"
  pure (if here then "" else "./")

tel2Vectors :: IO [(String, Bool)]
tel2Vectors = do
  base <- baseDir
  source <- readFile (base <> "test/programs/tictactoe.tel2")
  case compileMachine source of
    Left _ -> pure [("tel2 tictactoe parses and compiles", False)]
    Right machine -> do
      games <- sequence
        [ golden base machine "tel2_ttt_win" ["1", "4", "2", "5", "3"]
        , golden base machine "tel2_ttt_quit" ["q"]
        , golden base machine "tel2_ttt_invalid" ["x", "1", "1", "4", "2", "5", "3"]
        , golden base machine "tel2_ttt_tie" ["1", "2", "3", "5", "8", "4", "6", "9", "7"]
        ]
      let compiled =
            ("tel2 tictactoe parses and compiles",
             length (lines source) < 150
               && machineStateCount machine > 4000
               && machineRuleCount machine > 40000
               && not ("state \"" `isInfixOf` source))
          malformed =
            [ rejects "tel2 rejects filename builtin" "main = tictactoe"
            , rejects "tel2 rejects missing cells" (tinySource "A" "" "cells 1")
            , rejects "tel2 rejects wrong move count" wrongMoveCount
            , rejects "tel2 rejects out-of-range winning line"
                (tinySource "A" "winning 2" "winning 1")
            ]
          mutation = sourceMutation
      pure (compiled : mutation : malformed <> games)

golden :: FilePath -> Machine -> String -> [String] -> IO (String, Bool)
golden base machine name inputs = do
  expected <- readFile (base <> "test/golden/" <> name <> ".txt")
  let actual = fst <$> runMachineScript machine inputs
  pure (name <> " through Morph", actual == Right expected)

rejects :: String -> String -> (String, Bool)
rejects name source =
  (name, case compileMachine source of Left _ -> True; Right _ -> False)

sourceMutation :: (String, Bool)
sourceMutation = ("tel2 source mutation changes denotation", result "A" /= result "B")
  where
    result mark = do
      machine <- either (Left . show) Right (compileMachine (tinySource mark "" ""))
      fst <$> runMachineScript machine ["go"]

wrongMoveCount :: String
wrongMoveCount = unlines (fmap replaceMoves (lines (tinySource "A" "" "")))
  where
    replaceMoves "moves \"go\"" = "moves \"go\" \"other\""
    replaceMoves line           = line

tinySource :: String -> String -> String -> String
tinySource mark extra remove = unlines . filter (/= remove) $
  [ "telomare-grid-game 1"
  , "board 1 1"
  , "cells 1"
  , "player \"First\" " <> show mark
  , "player \"Second\" \"Z\""
  , "moves \"go\""
  , "quit \"stop\" \"bye\\n\""
  , "winning 1"
  , "cell-separator \"\""
  , "row-separator \"\""
  , "turn-message \"{mark} turn\\n\""
  , "prompt \"? \""
  , "invalid-message \"invalid\\n\""
  , "occupied-message \"occupied\\n\""
  , "win-message \"{mark} won\\n\""
  , "tie-message \"tie\\n\""
  , extra
  ]
