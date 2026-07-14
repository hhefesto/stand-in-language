module Tel2Vectors (tel2Vectors) where

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
             machineStateCount machine > 4000 && machineRuleCount machine > 40000)
          rejectsFallback =
            ("tel2 rejects non-machine source",
             case compileMachine "main = tictactoe" of Left _ -> True; Right _ -> False)
      pure (compiled : rejectsFallback : games)

golden :: FilePath -> Machine -> String -> [String] -> IO (String, Bool)
golden base machine name inputs = do
  expected <- readFile (base <> "test/golden/" <> name <> ".txt")
  let actual = fst <$> runMachineScript machine inputs
  pure (name <> " through Morph", actual == Right expected)
