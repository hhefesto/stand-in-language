module BendVectors (bendVectors) where

import Data.Either (isLeft, isRight, rights)
import Data.List (isInfixOf, nub)
import System.Directory (getTemporaryDirectory, removeFile)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Telomare.Backend.Bend
import Telomare.Transport
import TransportVectors (constructorNodes)

bendVectors :: IO [(String, Bool)]
bendVectors = do
  external <- externalRuntimeVectors
  pure $
    [ ("bend-emits-every-node-constructor", all (isRight . validatedSource) constructorNodes)
    , ("bend-source-snapshot-suc", sucSnapshot == expectedSucSnapshot)
    , ("bend-first-order-named-functions", all namedFirstOrder emittedCorpus)
    , ("bend-input-check-and-result-protocol", protocolProperty)
    , ("bend-box-metadata-without-eal-claim", boxProperty)
    , ("bend-recursion-order-and-stop-comments", recursionProperty)
    , ("bend-rejects-oversized-u24-constant", oversizedConstantRejected)
    ] <> external

validatedSource :: Artifact -> Either String String
validatedSource artifact = do
  validated <- either (Left . validationMessage) Right (validateArtifact artifact)
  either (Left . bendErrorMessage) Right (emitBend validated)

emittedCorpus :: [String]
emittedCorpus = rights (fmap validatedSource constructorNodes)

namedFirstOrder :: String -> Bool
namedFirstOrder source =
  not ("lambda" `isInfixOf` source)
    && not ("morph =" `isInfixOf` source)
    && allUnique [takeWhile (/= '(') line | line <- lines source, "def node_" `isInfixOf` line]
  where
    allUnique values = length values == length (nub values)

sucSnapshot :: String
sucSnapshot = case validatedSource (Artifact 1 TNat TNat NSuc) of
  Left err -> err
  Right source -> unlines (take 15 (dropWhile (/= "# NSuc") (lines source)))

expectedSucSnapshot :: String
expectedSucSnapshot = unlines
  [ "# NSuc"
  , "def node_0(x):"
  , "  match x:"
  , "    case Value/DomainError:"
  , "      return x"
  , "    case _:"
  , "      match x:"
  , "        case Value/Nat:"
  , "          switch x.value == 16777215:"
  , "            case 0:"
  , "              return Value/Nat(x.value + 1)"
  , "            case _:"
  , "              return Value/DomainError"
  , "        case _:"
  , "          return Value/DomainError"
  ]

protocolProperty :: Bool
protocolProperty = case validatedSource (Artifact 1 (TList TNat) (TList TNat) NId) of
  Left _ -> False
  Right source -> all (`isInfixOf` source)
    [ "# encoded input check for List Nat[u24 checked]"
    , "case Value/Cons:"
    , "return Run/InvalidInput"
    , "return Run/Ok(result)"
    , "return Run/DomainError"
    ]

boxProperty :: Bool
boxProperty = case validatedSource (constructorNodes !! 25) of
  Left _ -> False
  Right source -> all (`isInfixOf` source)
    [ "NBox (value-transparent metadata; no EAL enforcement claim)"
    , "Value semantics only: no work, fuel, duplication-grade, or EAL claim."
    ]

recursionProperty :: Bool
recursionProperty = all (`anySourceContains` emittedCorpus)
  [ "NIter helper: exactly n body calls, seed remains second"
  , "NFold helper: head-to-tail, body input is (accumulator, element)"
  , "NWhile helper: bounded pre-test; Inl stops and Inr steps"
  , "NWhile Nat[u24 checked] (value order is (limit, seed))"
  ]
  where
    anySourceContains needle = any (needle `isInfixOf`)

oversizedConstantRejected :: Bool
oversizedConstantRejected = case validateArtifact
    (Artifact 1 TUnit TNat (NConst (bendU24Max + 1))) of
  Left _ -> False
  Right validated -> isLeft (emitBend validated)

externalRuntimeVectors :: IO [(String, Bool)]
externalRuntimeVectors = do
  configured <- lookupEnv "TELOMARE_BEND"
  case configured of
    Nothing -> pure [("bend-external-runtime [SKIP: set TELOMARE_BEND to a Bend executable]", True)]
    Just bend -> do
      temporary <- getTemporaryDirectory
      let primitivePath = temporary </> "telomare-bend-primitive.bend"
          iterPath = temporary </> "telomare-bend-iter.bend"
          duplicatePath = temporary </> "telomare-bend-duplicate.bend"
          primitive = Artifact 1 TNat TNat NSuc
          iteration = Artifact 1 (TProd TNat (TBang TNat)) (TBang TNat) (NIter NSuc)
          duplicate = Artifact 1 TNat (TProd TNat TNat) NDupNat
      case (validatedSource primitive, validatedSource iteration, validatedSource duplicate) of
        (Right primitiveSource, Right iterSource, Right duplicateSource) -> do
          writeFile primitivePath (withMain "Value/Nat(2)" primitiveSource)
          writeFile iterPath (withMain
            "Value/Prod(Value/Nat(3), Value/Nat(0))" iterSource)
          writeFile duplicatePath (withMain "Value/Nat(4)" duplicateSource)
          primitiveRun <- runBend bend primitivePath
          iterRun <- runBend bend iterPath
          duplicateRun <- runBend bend duplicatePath
          removeFile primitivePath
          removeFile iterPath
          removeFile duplicatePath
          pure
            [ ("bend-external-runtime-primitive", successfulWith "3" primitiveRun)
            , ("bend-external-runtime-iteration", successfulWith "3" iterRun)
            , ("bend-external-runtime-duplicate", successfulWith "4" duplicateRun)
            ]
        _ -> pure [("bend-external-runtime-emission", False)]

withMain :: String -> String -> String
withMain input source = source <> unlines
  [ ""
  , "def main():"
  , "  return telomare_run(" <> input <> ")"
  ]

runBend :: FilePath -> FilePath -> IO (ExitCode, String, String)
runBend bend source =
  readProcessWithExitCode "timeout" ["30s", bend, "run-c", source] ""

successfulWith :: String -> (ExitCode, String, String) -> Bool
successfulWith expected (ExitSuccess, stdout, _) =
  "Run/Ok" `isInfixOf` stdout && expected `isInfixOf` stdout
successfulWith _ _ = False
