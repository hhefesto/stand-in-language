{-# LANGUAGE LambdaCase #-}

-- | .tel parity suite (M-tel): telomare3's Tier-2 runtime against
-- telomare1-captured transcripts.
--
-- The tictactoe goldens were captured from the telomare1 binary
-- (@printf \<moves\> | nix run . -- tictactoe.tel@, 2026-07-13); the four
-- scripted games came out BYTE-IDENTICAL on first run, so the comparisons
-- here are exact even though the acceptance bar is spirit-level.  The
-- simpleplus\/tc_ultra_minimal expectations were captured the same way
-- (2026-07-14).
--
-- Program sources are frozen copies under test\/programs\/ (of the
-- on-hold telomare1 root files) so the suite runs inside the nix sandbox.
--
-- Also asserts the documented improvement: @sizing_fail5.tel@ (rejected by
-- telomare1's sizing with RecursionLimitError) runs on telomare3.
module ParityTel (parityVectors) where

import System.Directory (doesFileExist)

import Telomare3.Tel.Frontend (compileTel, loadModulesFor)
import Telomare3.Tel.Loop (runTelWithInput)

-- cabal test may run with cwd = the package dir or the repo root.
baseDir :: IO FilePath
baseDir = do
  here <- doesFileExist "test/programs/tictactoe.tel"
  pure (if here then "" else "telomare3/")

transcript :: FilePath -> [String] -> IO (Either String String)
transcript telFile inputs = loadModulesFor telFile >>= \case
  Left e -> pure (Left (show e))
  Right (entry, modules) -> case compileTel modules entry of
    Left e -> pure (Left (show e))
    Right prog -> case fst (runTelWithInput Nothing prog inputs) of
      Left e     -> pure (Left (show e))
      Right outs -> pure (Right (unlines outs))

goldenGame :: FilePath -> String -> [String] -> IO (String, Bool)
goldenGame base name inputs = do
  expected <- readFile (base <> "test/golden/" <> name <> ".txt")
  actual <- transcript (base <> "test/programs/tictactoe.tel") inputs
  pure ("tictactoe " <> name, actual == Right expected)

expecting :: FilePath -> String -> [String] -> String -> IO (String, Bool)
expecting base prog inputs expected = do
  actual <- transcript (base <> "test/programs/" <> prog <> ".tel") inputs
  pure (prog, actual == Right expected)

parityVectors :: IO [(String, Bool)]
parityVectors = do
  base <- baseDir
  games <- sequence
    [ goldenGame base "ttt_win"     ["1", "4", "2", "5", "3"]
    , goldenGame base "ttt_quit"    ["q"]
    , goldenGame base "ttt_invalid" ["x", "1", "1", "4", "2", "5", "3"]
    , goldenGame base "ttt_tie"     ["1", "2", "3", "5", "4", "6", "8", "7", "9"]
    ]
  others <- sequence
    [ -- telomare1 (2026-07-14): prompt, then the abort of the "1" line
      -- failing the two-digit refinement — the abort VALUE from the
      -- first (Zero-input) iteration is discarded, exactly as telomare1
      -- discards it
      expecting base "simpleplus" ["1", "2"]
        "enter two digits separated by a space\n\
        \runtime error:\nAborted, user abort: invalid input\n"
    , -- telomare1 (2026-07-14): single output, state Zero
      expecting base "tc_ultra_minimal" ["1"] "O\n"
    ]
  -- the never-reject improvement: telomare1's sizing rejects this program
  -- (RecursionLimitError); telomare3 runs it
  unsizable <- transcript (base <> "test/programs/sizing_fail5.tel") ["1"]
  let improvement =
        ("sizing_fail5 runs (telomare1 rejects it)",
         either (const False) (not . null) unsizable)
  pure (games <> others <> [improvement])
