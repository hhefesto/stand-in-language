{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Data.Maybe (mapMaybe)
import qualified Options.Applicative as O
import System.FilePath (takeBaseName)
import Telomare.Eval (runMain, runMainCore)
import Telomare.HvmBackend (emitProgram)
import Telomare.HvmBackendCcc (emitProgramCcc)
import Telomare.Levels (levelsReport)
import Telomare.T2Backend (T2Mode (..), emitProgramT2)

data TelomareOpts
  = TelomareOpts { telomareFile  :: String
                 , emitHvm       :: Bool
                 , emitHvmCcc    :: Bool
                 , emitLevels    :: Bool
                 , emitT2        :: Bool
                 , emitT2Lazy    :: Bool
                 , emitT2LetOnly :: Bool
                 }
  deriving Show

telomareOpts :: O.Parser TelomareOpts
telomareOpts = TelomareOpts
  <$> O.argument O.str (O.metavar "TELOMARE-FILE")
  <*> O.switch (O.long "emit-hvm"
                <> O.help "compile (parse, resolve, size recursion) and print a Bend/HVM2 program instead of evaluating")
  <*> O.switch (O.long "emit-hvm-ccc"
                <> O.help "like --emit-hvm, but via the experimental ConCat-style combinator backend (native closures, no defunctionalization)")
  <*> O.switch (O.long "emit-levels"
                <> O.help "print the structural EAL box-level assignment of every {test,step,base} recursion site reachable from main (prototype; see design/VALIDATION.md)")
  <*> O.switch (O.long "emit-t2"
                <> O.help "like --emit-hvm, but under the Telomare 2 affine discipline: contracted computed lets and iteration step closures are normalized at their box sites (src/Telomare/T2Backend.hs)")
  <*> O.switch (O.long "emit-t2-lazy"
                <> O.help "the --emit-t2 emitter with the discipline disabled (baseline for A/B measurement)")
  <*> O.switch (O.long "emit-t2-letonly"
                <> O.help "the --emit-t2 emitter with only the let-binding (dupS) rule, no iteration-entry boxing")

-- | Recursively load only the modules reachable from the entry file.
getModulesFor :: String -> IO [(String, String)]
getModulesFor entryModule = go [entryModule] []
  where
    go [] loaded = return loaded
    go (m:queue) loaded
      | m `elem` fmap fst loaded = go queue loaded
      | otherwise = do
          let filePath = m <> ".tel"
          content <- readFile filePath
          let imports = extractImports content
          go (queue <> imports) ((m, content) : loaded)

    extractImports :: String -> [String]
    extractImports = mapMaybe parseImportLine . lines

    parseImportLine :: String -> Maybe String
    parseImportLine line = case words line of
      ("import":"qualified":name:_) -> Just name
      ("import":name:_)             -> Just name
      _                             -> Nothing

main :: IO ()
main = do
  let opts = O.info (telomareOpts O.<**> O.helper)
        ( O.fullDesc
          <> O.progDesc "A simple but robust virtual machine" )
  topts <- O.execParser opts
  let entryModule = takeBaseName (telomareFile topts)
  allModules <- getModulesFor entryModule
  if | emitHvmCcc topts -> runMainCore allModules entryModule (putStr . emitProgramCcc)
     | emitHvm topts -> runMainCore allModules entryModule (putStr . emitProgram)
     | emitT2 topts -> runMainCore allModules entryModule (putStr . emitProgramT2 T2Eager)
     | emitT2Lazy topts -> runMainCore allModules entryModule (putStr . emitProgramT2 T2Lazy)
     | emitT2LetOnly topts -> runMainCore allModules entryModule (putStr . emitProgramT2 T2LetOnly)
     | emitLevels topts -> putStr (levelsReport allModules entryModule)
     | otherwise -> runMain allModules entryModule
