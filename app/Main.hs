-- | Telomare CLI: compile and run typed-core .tel2 programs.
--
--   telomare program.tel2              interactive machine driver
--   telomare --certificate program.tel2  print typed core summary first
--   telomare --emit-transport init program.tel2  print one core entry
--   telomare --meter program.tel2        print formal work on stderr at exit
--   telomare --max-work N program.tel2   cap global formal work
--   telomare --assume-shape text<=N program.tel2  refine certified step
--     bounds to inputs with at most N characters (validated at runtime)
module Main (main) where

import Control.Monad (when)
import Numeric.Natural (Natural)
import Options.Applicative
import System.Exit (exitFailure)
import System.FilePath (takeExtension)
import System.IO (hPutStrLn, stderr)

import Telomare.Machine
import Telomare.Tel2
import Telomare.Transport

data Opts = Opts
  { optFile        :: FilePath
  , optCertificate :: Bool
  , optTransport   :: Maybe String
  , optMeter       :: Bool
  , optMaxWork     :: Maybe Natural
  , optAssume      :: Maybe String
  }

opts :: Parser Opts
opts = Opts
  <$> argument str (metavar "TELOMARE-FILE" <> help "typed-core .tel2 program to run")
  <*> switch (long "certificate"
              <> help "print the compiled Morph summary before running")
  <*> optional (strOption (long "emit-transport" <> metavar "init|step"
              <> help "print one backend-neutral core entry and exit"))
  <*> switch (long "meter"
              <> help "print formal core work to stderr on exit")
  <*> optional (option auto (long "max-work" <> metavar "N"
              <> help "stop after N units of formal core work"))
  <*> optional (strOption (long "assume-shape" <> metavar "text<=N"
              <> help "refine the certified step bounds to inputs whose text component has at most N characters; inputs are validated at runtime"))

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
  compiled <- compileTel2File (optFile o)
  case compiled of
    Left (CompileError err) -> hPutStrLn stderr err >> exitFailure
    Right program -> case optTransport o of
      Just entry -> emitTransport entry program
      Nothing -> case traverse parseAssume (optAssume o) of
        Left err -> hPutStrLn stderr err >> exitFailure
        Right assume -> do
          when (optCertificate o)
            (putStrLn (programCertificateSummary assume program))
          result <- runProgramIO (optMaxWork o) (optMeter o) assume program
          case result of
            Left err -> hPutStrLn stderr err >> exitFailure
            Right () -> pure ()

emitTransport :: String -> Program -> IO ()
emitTransport entry program = case entry of
  "init" -> putStrLn (renderArtifact (programArtifactInitial artifact))
  "step" -> putStrLn (renderArtifact (programArtifactStep artifact))
  _ -> hPutStrLn stderr "--emit-transport expects init or step" >> exitFailure
  where
    artifact = exportProgram program
