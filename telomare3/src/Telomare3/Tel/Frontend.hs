{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

-- | .tel frontend for telomare3: module loading, parse\/resolve\/typecheck
-- via the telomare1 library (reused unmodified — user decision), then
-- conversion to the telomare3 runtime IR.
--
-- Mirrors telomare1's @compileMain@ two-track quirk exactly
-- (src\/Telomare\/Eval.hs:112-119): the type check runs on the
-- @main2Term3@ elaboration, execution uses the @main2Term3let@ one.
-- NO Possible.hs: where telomare1 sizes recursion and installs church
-- towers, 'term3ToTel' installs the native 'TUnbounded' node
-- (@Term3Unsized@ sits exactly where the tower would go — see
-- src\/Telomare.hs unsizedRepeater\/i2CB).
--
-- Everything returns 'Either' — telomare1's frontend @error@ escape
-- hatches (unknown imports, parse-flattening) are made unreachable by
-- pre-validation here.
module Telomare3.Tel.Frontend
  ( Tel3Error (..)
  , renderTel3Error
  , loadModulesFor
  , compileTel
  , term3ToTel
  ) where

import qualified Control.Comonad.Trans.Cofree as CofreeT
import Control.Exception (IOException, try)
import Data.Bifunctor (bimap, second)
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import Data.List (isPrefixOf, nub)
import System.FilePath (takeBaseName, takeDirectory, (<.>), (</>))

import qualified Telomare
import Telomare (AbortableF (..), BasicExprF (..), StuckF (..), Term3,
                 Term3F (..), unAnnotatedUPT)
import Telomare.Parser (parseModule)
import Telomare.Resolver (main2Term3, main2Term3let)
import Telomare.TypeChecker (typeCheck)

import Telomare3.Tel.Eval (TelExpr (..))

data Tel3Error
  = ModuleLoadError String
  | ParseError String String    -- ^ module name, parser message
  | ResolveError String
  | TypeError String
  | ConvError String
  deriving (Eq, Show)

renderTel3Error :: Tel3Error -> String
renderTel3Error = \case
  ModuleLoadError m -> "module loading failed: " <> m
  ParseError m e    -> "parse error in module " <> m <> ":\n" <> e
  ResolveError e    -> "resolver error: " <> e
  TypeError e       -> "type error: " <> e
  ConvError e       -> "internal conversion error: " <> e

-- | Load the entry module and its transitive imports (telomare1's
-- app\/Main.hs getModulesFor, done properly: file-relative paths, IO
-- errors as values, imports pre-validated).
loadModulesFor :: FilePath -> IO (Either Tel3Error (String, [(String, String)]))
loadModulesFor path =
  let dir = takeDirectory path
      entry = takeBaseName path
      importsOf :: String -> [String]
      importsOf src = nub
        [ name
        | l <- lines src
        , Just rest <- [stripPrefixMaybe "import " l]
        , let name = case words rest of
                ("qualified" : n : _) -> n
                (n : _)               -> n
                []                    -> ""
        , not (null name)
        ]
      stripPrefixMaybe p s = if p `isPrefixOf` s
        then Just (drop (length p) s) else Nothing
      go :: [(String, String)] -> [String] -> IO (Either Tel3Error [(String, String)])
      go acc [] = pure (Right (reverse acc))
      go acc (m : rest)
        | m `elem` fmap fst acc = go acc rest
        | otherwise = do
            r <- try (readFile (dir </> m <.> "tel"))
              :: IO (Either IOException String)
            case r of
              Left e -> pure (Left (ModuleLoadError
                (m <> ".tel: " <> show e)))
              Right src -> go ((m, src) : acc) (rest <> importsOf src)
  in do
       r <- go [] [entry]
       pure (fmap (entry,) r)

-- | Compile loaded modules to the telomare3 runtime IR.
compileTel :: [(String, String)] -> String -> Either Tel3Error TelExpr
compileTel moduleSrcs entry = do
  parsed <- traverse
    (\(n, src) -> either (Left . ParseError n) (Right . (,) n) (parseModule src))
    moduleSrcs
  -- unwrap the parser's AnnotatedUPT newtype for the resolver (telomare1
  -- compileMain does the same)
  let modules =
        second (fmap (bimap unAnnotatedUPT (second unAnnotatedUPT))) <$> parsed
  t3tc <- either (Left . ResolveError . show) Right (main2Term3 modules entry)
  case typeCheck mainType t3tc of
    Just e  -> Left (TypeError (show e))
    Nothing -> Right ()
  t3 <- either (Left . ResolveError . show) Right (main2Term3let modules entry)
  term3ToTel t3
  where
    -- verbatim from telomare1 Eval.hs: main :: (Zero -> Zero, Any)
    mainType = Fix (Telomare.PairTypeP
      (Fix (Telomare.ArrTypeP (Fix Telomare.ZeroTypeP) (Fix Telomare.ZeroTypeP)))
      (Fix Telomare.AnyType))

-- | Term3 → runtime IR, mirroring telomare1's convertPT
-- (src\/Telomare\/Eval.hs:61-73) except: no sizing — @Term3Unsized@
-- becomes 'TUnbounded'; the refinement wrapper emits the exact
-- @removeRefinementWrappers@ runtime shape (checks RUN at runtime, as in
-- telomare1).
term3ToTel :: Term3 -> Either Tel3Error TelExpr
term3ToTel = cata go
  where
    go (_ CofreeT.:< t) = case t of
      Term3B ZeroSF               -> Right TZero
      Term3B (PairSF a b)         -> TPair <$> a <*> b
      Term3S EnvSF                -> Right TEnv
      Term3S (SetEnvSF x)         -> TSetEnv <$> x
      Term3S (DeferSF _ x)        -> TDefer <$> x
      Term3S (GateSF l r)         -> TGate <$> l <*> r
      Term3S (LeftSF x)           -> TLeft <$> x
      Term3S (RightSF x)          -> TRight <$> x
      Term3A AbortF               -> Right TAbort
      Term3A (AbortedF _)         -> Left (ConvError "AbortedF in source term")
      Term3Unsized tok            -> Right (TUnbounded tok)
      Term3CheckingWrapper _ tc c -> checkingWrapper <$> tc <*> c

    -- SetEnv (Pair performTC (Pair tc c)) with
    -- performTC = Defer (SetEnv (Pair (SetEnv (Pair Abort (tc `app` c)))
    --                           (Right Env)))
    -- — telomare1's removeRefinementWrappers/convertPT encoding: run the
    -- check on the value; nonzero result aborts with it as message; zero
    -- yields Abort·0 = identity, applied to the value.
    checkingWrapper tc c = TSetEnv (TPair performTC (TPair tc c))
      where
        performTC = TDefer
          (TSetEnv (TPair (TSetEnv (TPair TAbort innerTC)) (TRight TEnv)))
        innerTC = app (TLeft TEnv) (TRight TEnv)

    -- application (telomare1 appS/twiddle)
    app c i = TSetEnv (TSetEnv (TPair twiddle (TPair i c)))
    twiddle = TDefer (TPair (TLeft (TRight TEnv))
                            (TPair (TLeft TEnv) (TRight (TRight TEnv))))
