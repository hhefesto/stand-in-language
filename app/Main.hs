{-# LANGUAGE LambdaCase #-}

-- | Telomare CLI: run .tel programs on the Telomare Tier-2 runtime.
--
--   telomare game.tel                 interactive transcript loop
--   telomare --certificate game.tel   print the structural levels report first
--   telomare --meter game.tel         work-meter report on stderr at exit
--   telomare --max-steps N game.tel   metered fuel cap (Tier-2 "never
--                                     reject": exhaustion is a runtime
--                                     error, not a compile rejection)
module Main (main) where

import Control.Monad (when)
import Options.Applicative
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Telomare.Compat.Levels (levelsReport)
import Telomare.Tel.Eval (renderMeter)
import Telomare.Tel.Frontend (compileTel, loadModulesFor, renderTel3Error)
import Telomare.Tel.Loop (runTelLoop)

data Opts = Opts
  { optFile        :: FilePath
  , optCertificate :: Bool
  , optMeter       :: Bool
  , optMaxSteps    :: Maybe Int
  }

opts :: Parser Opts
opts = Opts
  <$> argument str (metavar "TELOMARE-FILE" <> help ".tel program to run")
  <*> switch (long "certificate"
              <> help "print the structural EAL levels report before running")
  <*> switch (long "meter"
              <> help "print the Tier-2 work meter to stderr on exit")
  <*> optional (option auto (long "max-steps" <> metavar "N"
              <> help "abort evaluation after N metered steps"))

main :: IO ()
main = run =<< execParser
  (info (opts <**> helper)
    (fullDesc <> progDesc "telomare: run .tel programs on the Tier-2 metered runtime"))

run :: Opts -> IO ()
run o = loadModulesFor (optFile o) >>= \case
  Left e -> hPutStrLn stderr (renderTel3Error e) >> exitFailure
  Right (entry, modules) -> do
    when (optCertificate o) $ putStr (levelsReport modules entry)
    case compileTel modules entry of
      Left e -> hPutStrLn stderr (renderTel3Error e) >> exitFailure
      Right prog -> do
        meter <- runTelLoop (optMaxSteps o) prog
        when (optMeter o) $ hPutStrLn stderr (renderMeter meter)
