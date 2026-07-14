{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

-- | Compatibility structural placement report for legacy .tel syntax.
--
-- The report is intentionally explicit about its scope: it is a static,
-- compatibility-frontend approximation over parsed @{test, step, base}@
-- recursion triples. It is not a runtime meter, a termination proof, or the
-- formal typed-core placement theorem.
module Telomare.Compat.Levels (levelsReport) where

import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Foldable (toList)
import Data.List (foldl', intercalate, sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import System.FilePath ((<.>))

import Telomare.Compat.Parser (parseModuleNamed)
import Telomare.Compat.Syntax (AUPT, AnnotatedUPT (..), HighTermF (..),
                               LamTermF (..), LocTag (..), LocatedName (..),
                               SourcePosition (..), SourceSpan (..),
                               UnprocessedParsedTermF (..), unAnnotatedUPT)

-- ── identities and report model ─────────────────────────────────────────────

data DefId = DefId
  { defModule :: !String
  , defName   :: !String
  }
  deriving (Eq, Ord, Show)

data SourceRef = SourceRef
  { srcFile     :: !(Maybe FilePath)
  , srcLine     :: !(Maybe Int)
  , srcColumn   :: !(Maybe Int)
  , srcOffset   :: !(Maybe Int)
  , srcFallback :: !(Maybe String)
  }
  deriving (Eq, Ord, Show)

data SiteKey = SiteKey
  { siteOwner  :: !DefId
  , siteSource :: !SourceRef
  }
  deriving (Eq, Ord, Show)

data Observation = Observation
  { obsSite  :: !SiteKey
  , obsLevel :: !Int
  , obsPath  :: ![DefId]
  }
  deriving (Eq, Show)

data BindingKey = BindingKey
  { bindingOwner :: !DefId
  , bindingName  :: !String
  }
  deriving (Eq, Ord, Show)

data DefInfo = DefInfo
  { diId   :: !DefId
  , diBody :: !AUPT
  }

type GlobalEnv = Map String DefInfo

data LocalInfo = LocalInfo
  { liId   :: !DefId
  , liBody :: !AUPT
  }

type LocalEnv = Map String LocalInfo

type AEnv = Map String AUPT

type Binds = Map String (BindingKey, Int)

data St = St
  { stVisited      :: !(Set (DefId, Int))
  , stObservations :: ![Observation]
  , stBangs        :: !(Map BindingKey Int)
  }

emptySt :: St
emptySt = St Set.empty [] Map.empty

-- ── small syntax utilities ──────────────────────────────────────────────────

collectLams :: AUPT -> ([String], AUPT)
collectLams (_ :< UnprocessedParsedTermL (LamF (LocatedName (_, n)) b)) =
  let (ps, body) = collectLams b in (n : ps, body)
collectLams x = ([], x)

spine :: AUPT -> (AUPT, [AUPT])
spine (_ :< UnprocessedParsedTermL (AppF f x)) =
  let (h, args) = spine f in (h, args <> [x])
spine x = (x, [])

varName :: AUPT -> Maybe String
varName (_ :< UnprocessedParsedTermL (VarF v)) = Just v
varName _                                      = Nothing

maximumOr :: Int -> [Int] -> Int
maximumOr z [] = z
maximumOr _ xs = maximum xs

-- ── parameter-offset summaries ──────────────────────────────────────────────

-- | For each leading lambda parameter of a definition: the maximum inferred
-- box-offset of that parameter's occurrences inside the body. Unknown
-- higher-order heads intentionally still default to offset 0; the report calls
-- this out as an approximation.
paramOffsets :: AEnv -> Set String -> AUPT -> [Int]
paramOffsets env guard def =
  let (params, body) = collectLams def
  in fmap (\p -> occDepth env guard p 0 body) params

occDepth :: AEnv -> Set String -> String -> Int -> AUPT -> Int
occDepth env guard p d t@(_ :< node) = case node of
  UnprocessedParsedTermL (VarF v) -> if v == p then d else 0
  UnprocessedParsedTermL (LamF (LocatedName (_, n)) b)
    | n == p    -> 0
    | otherwise -> occDepth env guard p d b
  UnprocessedParsedTermL (AppF _ _) ->
    let (h, args) = spine t
        offs = headOffsets env guard h
        argD (j, arg) = occDepth env guard p (d + offAt offs j) arg
    in maximumOr 0 (occDepth env guard p d h : fmap argD (zip [0 ..] args))
  UnprocessedParsedTermH (RecursionF a b c) ->
    maximumOr 0 (fmap (occDepth env guard p (d + 1)) [a, b, c])
  LetUPF bs body
    | p `elem` [n | (LocatedName (_, n), _) <- bs] -> 0
    | otherwise ->
        maximumOr 0 (occDepth env guard p d body
                      : fmap (occDepth env guard p d . snd) bs)
  other -> maximumOr 0 (fmap (occDepth env guard p d) (toList other))

headOffsets :: AEnv -> Set String -> AUPT -> [Int]
headOffsets env guard h = case varName h of
  Just v | v `Set.notMember` guard
         , Just def <- Map.lookup v env ->
             paramOffsets env (Set.insert v guard) def
  _ -> []

offAt :: [Int] -> Int -> Int
offAt offs j = if j < length offs then offs !! j else 0

-- ── the walk ────────────────────────────────────────────────────────────────

walk :: GlobalEnv -> LocalEnv -> Binds -> DefId -> [DefId] -> Int -> AUPT -> St -> St
walk gs ls bn owner path d t@(ann :< node) st = case node of
  UnprocessedParsedTermH (RecursionF a b c) ->
    let site = SiteKey owner (sourceRef ann)
        obs = Observation site d path
        st1 = st { stObservations = obs : stObservations st }
    in foldl' (flip (walk gs ls bn owner path (d + 1))) st1 [a, b, c]
  UnprocessedParsedTermL (AppF _ _) ->
    let (h, args) = spine t
        offs = headOffsets (auptEnv gs ls) Set.empty h
        st1 = walk gs ls bn owner path d h st
    in foldl' (\s (j, arg) -> walk gs ls bn owner path (d + offAt offs j) arg s)
              st1
              (zip [0 ..] args)
  UnprocessedParsedTermL (VarF v) -> enterVar v (bang v st)
  UnprocessedParsedTermL (LamF (LocatedName (_, n)) b) ->
    let bn' = Map.insert n (BindingKey owner n, d) bn
    in walk gs (Map.delete n ls) bn' owner path d b st
  LetUPF bs body ->
    let localInfo (LocatedName (_, n), rhs) = (n, LocalInfo (localDef owner n) rhs)
        ls' = foldl' (\m b -> uncurry Map.insert (localInfo b) m) ls bs
        bn' = foldl' (\m (LocatedName (_, n), _) ->
                        Map.insert n (BindingKey owner n, d) m)
                     bn bs
    in walk gs ls' bn' owner path d body st
  other -> foldl' (flip (walk gs ls bn owner path d)) st (toList other)
  where
    bang v s = case Map.lookup v bn of
      Nothing -> s
      Just (binding, bd) ->
        s { stBangs = Map.insertWith max binding (d - bd) (stBangs s) }
    enterVar v s
      | Set.member (nextOwner v, d) (stVisited s) = s
      | Just local <- Map.lookup v ls =
          let owner' = liId local
          in walk gs ls bn owner' (path <> [owner']) d (liBody local) (mark owner' s)
      | Just global <- Map.lookup v gs =
          let owner' = diId global
          in walk gs Map.empty Map.empty owner' (path <> [owner']) d (diBody global)
               (mark owner' s)
      | otherwise = s
    nextOwner v = maybe (maybe owner diId (Map.lookup v gs)) liId (Map.lookup v ls)
    mark owner' s = s { stVisited = Set.insert (owner', d) (stVisited s) }

auptEnv :: GlobalEnv -> LocalEnv -> AEnv
auptEnv gs ls = Map.map liBody ls `Map.union` Map.map diBody gs

localDef :: DefId -> String -> DefId
localDef owner name = owner { defName = defName owner <> "." <> name }

-- ── public report ───────────────────────────────────────────────────────────

levelsReport :: [(String, String)] -> String -> String
levelsReport moduleSrcs entry =
  case parseModules moduleSrcs of
    Left err -> "certificate parse error: " <> err <> "\n"
    Right parsed ->
      let globals = globalEnv parsed
          entryId = DefId entry "main"
      in case lookupEntry entryId parsed of
           Nothing -> "certificate error: no entry definition " <> renderDef entryId <> "\n"
           Just mainDef ->
             renderReport entryId (analyze globals entryId mainDef)

parseModules
  :: [(String, String)]
  -> Either String [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])]
parseModules = traverse parseOne
  where
    parseOne (name, src) =
      either (Left . ((name <> ": ") <>)) (Right . (name,))
        (parseModuleNamed (name <.> "tel") src)

lookupEntry
  :: DefId
  -> [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])]
  -> Maybe AUPT
lookupEntry entryId parsed =
  unAnnotatedUPT <$> lookup (defName entryId)
    [ (name, def)
    | (moduleName, entries) <- parsed
    , moduleName == defModule entryId
    , Right (name, def) <- entries
    ]

globalEnv :: [(String, [Either AnnotatedUPT (String, AnnotatedUPT)])] -> GlobalEnv
globalEnv = foldl' addModule Map.empty
  where
    addModule env (moduleName, entries) = foldl' (addDef moduleName) env entries
    addDef moduleName env = \case
      Right (name, def) -> Map.insertWith keepExisting name
        (DefInfo (DefId moduleName name) (unAnnotatedUPT def)) env
      Left _ -> env
    keepExisting _ old = old

analyze :: GlobalEnv -> DefId -> AUPT -> St
analyze gs entryId mainDef =
  walk gs Map.empty Map.empty entryId [entryId] 0 mainDef emptySt

-- ── rendering ───────────────────────────────────────────────────────────────

renderReport :: DefId -> St -> String
renderReport entryId st = unlines $
  [ "-- Telomare structural placement certificate"
  , "entry: " <> renderDef entryId
  , "analysis: static compatibility approximation; the program has not run"
  , ""
  , "This report groups source {test, step, base} recursion sites and shows"
  , "the inferred box levels at which each site is observed. Use --meter for"
  , "runtime function applications, gate selections, and recursion unrolls."
  , ""
  , "Summary"
  , "  source recursion sites:               " <> show (length siteRows)
  , "  contextual placements:                " <> show (length observations)
  , "  maximum inferred recursion-box depth: " <> show maxDepth
  , "  bindings crossing box boundaries:     " <> show (length bangRows)
  , ""
  , "Recursion sites"
  ] <> siteTable
    <> [ ""
       , "How to read a level"
       , "  level d means the recursion site is orchestrated at inferred box depth d;"
       , "  its test, step, and base are analyzed one level deeper at d + 1."
       , "  Multiple levels for one site are different static contexts, not runtime"
       , "  recursion depths or unroll counts."
       , ""
       , "Placement witnesses"
       ]
    <> witnessRows
    <> [ ""
       , "Binding depth pressure"
       ]
    <> bangTable
    <> [ ""
       , "Notes"
       , "  - Paths are static dependency witnesses, not runtime call traces."
       , "  - A depth delta of k means an observed use occurs k inferred box levels"
       , "    below its binding; ! notation is a structural hint, not a proved type."
       , "  - Unknown higher-order parameter offsets currently default to 0, so this"
       , "    compatibility estimate can be incomplete."
       , "  - This is not a termination proof, runtime budget, or formal EAL typing."
       , ""
       , "-- End certificate; program output follows"
       , "" ]
  where
    observations = sortOn obsSort (reverse (stObservations st))
    obsSort o = (siteSource (obsSite o), siteOwner (obsSite o), obsLevel o, obsPath o)
    maxDepth = maximumOr 0 (fmap ((+ 1) . obsLevel) observations)
    grouped = Map.toList $ Map.fromListWith Set.union
      [ (obsSite obs, Set.singleton (obsLevel obs)) | obs <- observations ]
    siteRows = zip [0 :: Int ..] (sortOn (\(site, _) -> (siteSource site, siteOwner site)) grouped)
    siteNumbers = Map.fromList [(site, n) | (n, (site, _)) <- siteRows]
    bangRows = sortOn (\(binding, k) -> (negate k, bindingOwner binding, bindingName binding))
      [ row | row@(_, k) <- Map.toList (stBangs st), k > 0 ]
    sourceWidth = maximum (length "source" : [length (renderSource (siteSource s)) | (_, (s, _)) <- siteRows])
    ownerWidth = maximum (length "owner" : [length (renderDef (siteOwner s)) | (_, (s, _)) <- siteRows])
    siteTable
      | null siteRows = ["  no {test, step, base} recursion sites observed from entry"]
      | otherwise =
          [ "  " <> padRight 5 "site" <> " "
              <> padRight sourceWidth "source" <> "  "
              <> padRight ownerWidth "owner" <> "  observed levels"
          ] <> [ "  " <> padRight 5 (siteName n) <> " "
                 <> padRight sourceWidth (renderSource (siteSource site)) <> "  "
                 <> padRight ownerWidth (renderDef (siteOwner site)) <> "  "
                 <> renderLevels levels
               | (n, (site, levels)) <- siteRows
               ]
    witnessRows
      | null observations = ["  none"]
      | otherwise = concatMap renderWitness observations
    renderWitness obs =
      let n = fromMaybe 0 (Map.lookup (obsSite obs) siteNumbers)
      in [ "  " <> siteName n <> "  level " <> show (obsLevel obs)
             <> ", spans " <> show (obsLevel obs) <> " -> " <> show (obsLevel obs + 1)
         , "      static path:"
         ] <> fmap ("        " <>) (pathChunks (fmap renderDef (obsPath obs)))
    bangTable
      | null bangRows = ["  none"]
      | otherwise =
          let bindingWidth = maximum (length "binding" : [length (renderBinding b) | (b, _) <- bangRows])
          in [ "  " <> padRight bindingWidth "binding" <> "  depth delta  notation" ]
             <> [ "  " <> padRight bindingWidth (renderBinding binding) <> "  "
                    <> padRight 11 (show k) <> "  " <> bangs k
                | (binding, k) <- bangRows
                ]

renderLevels :: Set Int -> String
renderLevels = intercalate ", " . fmap show . Set.toAscList

pathChunks :: [String] -> [String]
pathChunks xs = case fmap (intercalate " > ") (chunksOf 4 xs) of
  []     -> []
  y : ys -> y : fmap ("> " <>) ys

chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)

siteName :: Int -> String
siteName n = "#" <> show n

renderBinding :: BindingKey -> String
renderBinding b = renderDef (bindingOwner b) <> "." <> bindingName b

renderDef :: DefId -> String
renderDef d = defModule d <> "." <> defName d

bangs :: Int -> String
bangs k = replicate k '!'

padRight :: Int -> String -> String
padRight width s = s <> replicate (max 0 (width - length s)) ' '

sourceRef :: LocTag -> SourceRef
sourceRef = \case
  SourceLoc span' -> fromSpan span'
  GeneratedLoc _ (Just parent) -> sourceRef parent
  GeneratedLoc reason Nothing -> fallback ("generated " <> reason)
  BuiltinLoc name -> fallback ("builtin " <> name)
  RuntimeLoc -> fallback "runtime"
  DecompiledLoc -> fallback "decompiled"
  UnknownLoc -> fallback "unknown"
  where
    fallback label = SourceRef Nothing Nothing Nothing Nothing (Just label)

fromSpan :: SourceSpan -> SourceRef
fromSpan span' = SourceRef
  { srcFile = sourceSpanFile span'
  , srcLine = Just line
  , srcColumn = Just column
  , srcOffset = Just offset
  , srcFallback = Nothing
  }
  where
    SourcePosition line column offset = sourceSpanStart span'

renderSource :: SourceRef -> String
renderSource ref = case (srcFile ref, srcLine ref, srcColumn ref, srcFallback ref) of
  (Just file, Just line, Just column, _) -> file <> ":" <> show line <> ":" <> show column
  (_, Just line, Just column, _)         -> "<source>:" <> show line <> ":" <> show column
  (_, _, _, Just label)                  -> label
  _                                      -> "unknown"
