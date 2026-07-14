{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

-- | .tel frontend for Telomare: module loading, parse\/resolve\/typecheck
-- via the compatibility frontend, then
-- conversion to the Telomare runtime IR.
--
-- The compatibility frontend keeps the historical two-track elaboration: the
-- type check runs on @main2Term3@, execution uses @main2Term3let@. Telomare
-- does not run the old static sizing pass; 'term3ToTel' installs the native
-- 'TUnbounded' node where that pass used to insert a pre-sized tower.
--
-- Everything returns 'Either'; compatibility frontend errors are caught before
-- they escape as runtime exceptions.
module Telomare.Tel.Frontend
  ( Tel3Error (..)
  , renderTel3Error
  , loadModulesFor
  , compileTel
  , term3ToTel
  ) where

import Control.Comonad.Cofree (Cofree ((:<)))
import qualified Control.Comonad.Trans.Cofree as CofreeT
import Control.Exception (IOException, try)
import Data.Bifunctor (bimap, second)
import Data.Fix (Fix (..))
import Data.Functor.Foldable (cata)
import Data.List (isPrefixOf, nub)
import Data.Map (Map)
import qualified Data.Map as Map
import System.FilePath (takeBaseName, takeDirectory, (<.>), (</>))

import Telomare.Compat.Parser (parseModuleNamed)
import Telomare.Compat.Resolver (main2Term3, main2Term3let)
import qualified Telomare.Compat.Syntax as Compat
import Telomare.Compat.Syntax (AbortableF (..), AnnotatedUPT (..),
                               BasicExprF (..), LocTag (..),
                               SourcePosition (..), SourceSpan (..),
                               StuckF (..), Term3, Term3F (..), unAnnotatedUPT)
import Telomare.Compat.TypeChecker (typeCheck)

import Telomare.Tel.Eval (RecursionSite (..), TelExpr (..))

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

-- | Load the entry module and its transitive imports with file-relative paths,
-- IO errors as values, and pre-validated imports.
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

-- | Compile loaded modules to the Telomare runtime IR.
compileTel :: [(String, String)] -> String -> Either Tel3Error TelExpr
compileTel moduleSrcs entry = do
  parsed <- traverse
    (\(n, src) -> either (Left . ParseError n) (Right . (,) n) (parseModuleNamed (n <> ".tel") src))
    moduleSrcs
  -- unwrap the parser's AnnotatedUPT newtype for the resolver
  let modules =
        second (fmap (bimap unAnnotatedUPT (second unAnnotatedUPT))) <$> parsed
  t3tc <- either (Left . ResolveError . show) Right (main2Term3 modules entry)
  case typeCheck mainType t3tc of
    Just e  -> Left (TypeError (show e))
    Nothing -> Right ()
  t3 <- either (Left . ResolveError . show) Right (main2Term3let modules entry)
  term3ToTelWithOwners (ownerMap parsed) t3
  where
    -- main :: (Zero -> Zero, Any), the .tel transcript entry type
    mainType = Fix (Compat.PairTypeP
      (Fix (Compat.ArrTypeP (Fix Compat.ZeroTypeP) (Fix Compat.ZeroTypeP)))
      (Fix Compat.AnyType))

-- | Term3 → runtime IR. There is no static sizing here: @Term3Unsized@
-- becomes 'TUnbounded'; the refinement wrapper emits the compatibility
-- runtime shape and runs checks at runtime.
term3ToTel :: Term3 -> Either Tel3Error TelExpr
term3ToTel = term3ToTelWithOwners Map.empty

type LocKey = (Maybe FilePath, Int)

term3ToTelWithOwners :: Map LocKey String -> Term3 -> Either Tel3Error TelExpr
term3ToTelWithOwners owners = cata go
  where
    go (anno CofreeT.:< t) = case t of
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
      Term3Unsized tok            -> Right (TUnbounded (RecursionSite tok anno (ownerFor anno)))
      Term3CheckingWrapper _ tc c -> checkingWrapper <$> tc <*> c

    ownerFor loc = locKey loc >>= (`Map.lookup` owners)

    -- SetEnv (Pair performTC (Pair tc c)) with
    -- performTC = Defer (SetEnv (Pair (SetEnv (Pair Abort (tc `app` c)))
    --                           (Right Env)))
    -- — compatibility wrapper encoding: run the
    -- check on the value; nonzero result aborts with it as message; zero
    -- yields Abort·0 = identity, applied to the value.
    checkingWrapper tc c = TSetEnv (TPair performTC (TPair tc c))
      where
        performTC = TDefer
          (TSetEnv (TPair (TSetEnv (TPair TAbort innerTC)) (TRight TEnv)))
        innerTC = app (TLeft TEnv) (TRight TEnv)

    -- application shape from the compatibility frontend
    app c i = TSetEnv (TSetEnv (TPair twiddle (TPair i c)))
    twiddle = TDefer (TPair (TLeft (TRight TEnv))
                            (TPair (TLeft TEnv) (TRight (TRight TEnv))))

ownerMap :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])] -> Map LocKey String
ownerMap parsed = Map.fromListWith keepExisting
  [ (key, moduleName <> "." <> defName)
  | (moduleName, entries) <- parsed
  , Right (defName, AnnotatedUPT body) <- entries
  , (key, _) <- ownerEntries body
  ]
  where
    keepExisting _ old = old

ownerEntries :: Compat.AUPT -> [(LocKey, ())]
ownerEntries (loc :< term) = here <> foldMap ownerEntries term
  where
    here = case locKey loc of
      Just key -> [(key, ())]
      Nothing  -> []

locKey :: LocTag -> Maybe LocKey
locKey = \case
  SourceLoc span' -> Just
    ( sourceSpanFile span'
    , sourcePositionOffset (sourceSpanStart span')
    )
  GeneratedLoc _ parent -> parent >>= locKey
  _ -> Nothing
