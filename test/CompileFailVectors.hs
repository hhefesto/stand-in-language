module CompileFailVectors (compileFailVectors) where

import Data.List (isInfixOf)
import System.Directory (doesFileExist)
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)

compileFailVectors :: IO [(String, Bool)]
compileFailVectors = mapM rejects
  [ ("linear-reject-reuse", "test/compile-fail/Reuse.hs", "multiplicity of")
  , ("linear-reject-drop", "test/compile-fail/Drop.hs", "non-linear pattern")
  , ("linear-reject-copy-without-evidence", "test/compile-fail/CopyList.hs",
      "Couldn't match type")
  ]

rejects :: (String, FilePath, String) -> IO (String, Bool)
rejects (name, path, expected) = do
  exists <- doesFileExist path
  if not exists
    then pure (name, False)
    else do
      (status, _, stderr) <- readProcessWithExitCode "ghc"
        ["-fforce-recomp", "-fno-code", "-isrc", path] ""
      pure (name, case status of
        ExitFailure _ -> expected `isInfixOf` stderr
        ExitSuccess   -> False)
