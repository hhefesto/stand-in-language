-- | Telomare CLI: compile and run typed-core .tel2 programs.
--
--   telomare program.tel2              interactive machine driver
--   telomare --certificate program.tel2  print typed core summary first
--   telomare --meter program.tel2        print formal work on stderr at exit
--   telomare --max-work N program.tel2   cap global formal work
module Main (main) where

import Control.Monad (when)
import Numeric.Natural (Natural)
import Options.Applicative
import System.Exit (exitFailure)
import System.FilePath (takeExtension)
import System.IO (hPutStrLn, stderr)

import Telomare.Machine
import Telomare.Tel2

data Opts = Opts
  { optFile        :: FilePath
  , optCertificate :: Bool
  , optMeter       :: Bool
  , optMaxWork     :: Maybe Natural
  }

opts :: Parser Opts
opts = Opts
  <$> argument str (metavar "TELOMARE-FILE" <> help "typed-core .tel2 program to run")
  <*> switch (long "certificate"
              <> help "print the compiled Morph summary before running")
  <*> switch (long "meter"
              <> help "print formal core work to stderr on exit")
  <*> optional (option auto (long "max-work" <> metavar "N"
              <> help "stop after N units of formal core work"))

main :: IO ()
main = run =<< execParser
  (info (opts <**> helper)
    (fullDesc <> progDesc "telomare: compile and run a .tel2 program through Morph"))

run :: Opts -> IO ()
run o
  | takeExtension (optFile o) == ".tel2" = runTel2 o
  | otherwise = do
      hPutStrLn stderr "only typed-core .tel2 programs are executable"
      exitFailure

runTel2 :: Opts -> IO ()
runTel2 o = do
  source <- readFile (optFile o)
  case compileTel2 source of
    Left (CompileError err) -> hPutStrLn stderr err >> exitFailure
    Right program -> do
      when (optCertificate o) $ putStrLn
        ("typed affine program: core depth " <> show (programDepth program))
      result <- runProgramIO (optMaxWork o) (optMeter o) program
      case result of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right () -> pure ()
