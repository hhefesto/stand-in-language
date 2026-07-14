-- | Structural EAL box-placement prototype (design/TELOMARE2-DESIGN.md §8,
-- validated in design/VALIDATION.md).
--
-- Assigns every reachable @{test, step, base}@ recursion site an EAL level:
-- the number of enclosing boxes at its orchestration point. One box per
-- site; a site at level d spans d -> d+1 (its test/step/base contents run
-- one level deeper, duplicated by the site's church numeral).
--
-- Purely structural — no evaluation, no search. Two ingredients:
--
--  1. syntactic containment: contents of a site's test/step/base are one
--     level deeper than the site;
--  2. parameter-offset summaries: a definition's parameter that occurs k
--     boxes deep inside the definition's body pulls the corresponding call
--     argument k levels deeper at every call site (this is how
--     @d2c b (dTimes a) 0@ places @dTimes a@'s own recursion one level
--     below d2c's — the step function is duplicated by the numeral).
--
-- Known approximations (prototype): parameters applied as functions with
-- unknown summaries (church numerals, higher-order args) contribute offset
-- 0 to their arguments; Case patterns don't bind for the free-variable
-- report; locals resolve against the scope at their use site.
module Telomare.Levels (levelsReport) where

import Control.Comonad.Cofree (Cofree ((:<)))
import Data.Foldable (toList)
import Data.List (foldl', intercalate, sortOn)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Telomare (AUPT, HighTermF (..), LamTermF (..), LocatedName (..),
                 UnprocessedParsedTermF (..), locStartLineColumn,
                 unAnnotatedUPT)
import Telomare.Parser (parseModule)

type Env = Map String AUPT

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

-- | For each leading lambda parameter of a definition: the max box-offset of
-- its occurrences inside the body (0 = orchestration level / scrutinee
-- position; >=1 = duplicated by some site's numeral). The guard breaks
-- (impossible-by-construction, but cheap) summary cycles.
paramOffsets :: Env -> Set String -> AUPT -> [Int]
paramOffsets env guard def =
  let (params, body) = collectLams def
  in fmap (\p -> occDepth env guard p 0 body) params

occDepth :: Env -> Set String -> String -> Int -> AUPT -> Int
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

headOffsets :: Env -> Set String -> AUPT -> [Int]
headOffsets env guard h = case varName h of
  Just v | v `Set.notMember` guard
         , Just def <- Map.lookup v env ->
             paramOffsets env (Set.insert v guard) def
  _ -> []

offAt :: [Int] -> Int -> Int
offAt offs j = if j < length offs then offs !! j else 0

-- ── the walk ────────────────────────────────────────────────────────────────

data RSite = RSite
  { rDef   :: String
  , rLoc   :: Maybe (Int, Int)
  , rLevel :: Int
  , rPath  :: [String]
  }

-- | Binds: lexically visible lambda/let binders -> (owning def, bind level).
-- A variable occurring k levels below its binding needs !^k — it is copied
-- wholesale by every intervening site's numeral.
type Binds = Map String (String, Int)

data St = St
  { stVisited :: Set (String, Int)
  , stSites   :: [RSite]
  , stBangs   :: Map (String, String) Int -- (def, var) -> max (use − bind)
  }

walk :: Env -> Env -> Binds -> String -> [String] -> Int -> AUPT -> St -> St
walk gs ls bn dn path d t@(ann :< node) st = case node of
  UnprocessedParsedTermH (RecursionF a b c) ->
    let site = RSite dn (locStartLineColumn ann) d path
        st1 = st { stSites = site : stSites st }
    in foldl' (flip (walk gs ls bn dn path (d + 1))) st1 [a, b, c]
  UnprocessedParsedTermL (AppF _ _) ->
    let (h, args) = spine t
        offs = headOffsets (Map.union ls gs) Set.empty h
        st1 = walk gs ls bn dn path d h st
    in foldl' (\s (j, arg) -> walk gs ls bn dn path (d + offAt offs j) arg s)
              st1
              (zip [0 ..] args)
  UnprocessedParsedTermL (VarF v) -> enterVar v (bang v st)
  UnprocessedParsedTermL (LamF (LocatedName (_, n)) b) ->
    walk gs (Map.delete n ls) (Map.insert n (dn, d) bn) dn path d b st
  LetUPF bs body ->
    let names = [n | (LocatedName (_, n), _) <- bs]
        ls' = foldl' (\m (LocatedName (_, n), rhs) -> Map.insert n rhs m)
                     ls bs
        bn' = foldl' (\m n -> Map.insert n (dn, d) m) bn names
    in walk gs ls' bn' dn path d body st
  other -> foldl' (flip (walk gs ls bn dn path d)) st (toList other)
  where
    bang v s = case Map.lookup v bn of
      Nothing -> s
      Just (owner, bd) ->
        s { stBangs = Map.insertWith max (owner, v) (d - bd) (stBangs s) }
    enterVar v s
      | Set.member (v, d) (stVisited s) = s
      | Just def <- Map.lookup v ls =
          walk gs ls bn v (path <> [v]) d def (mark v s)
      | Just def <- Map.lookup v gs =
          walk gs Map.empty Map.empty v (path <> [v]) d def (mark v s)
      | otherwise = s
    mark v s = s { stVisited = Set.insert (v, d) (stVisited s) }

-- ── report ──────────────────────────────────────────────────────────────────

levelsReport :: [(String, String)] -> String -> String
levelsReport modulesStrings _entry =
  case traverse (parseModule . snd) modulesStrings of
    Left err -> "levelsReport: parse error: " <> err <> "\n"
    Right parsed ->
      let gs = Map.fromList
                 [ (n, unAnnotatedUPT d)
                 | items <- parsed, Right (n, d) <- items ]
      in case Map.lookup "main" gs of
           Nothing -> "levelsReport: no main definition found\n"
           Just mainDef ->
             let st = walk gs Map.empty Map.empty "main" ["main"] 0 mainDef
                        (St Set.empty [] Map.empty)
                 ss = sortOn (\r -> (rLevel r, rDef r))
                        (reverse (stSites st))
                 depth = maximumOr 0 (fmap ((+ 1) . rLevel) ss)
                 bangs = [ e | e@(_, k) <- Map.toList (stBangs st), k > 0 ]
             in unlines $
                  [ "-- structural EAL box placement (prototype;"
                    <> " see design/VALIDATION.md)"
                  , "-- one box per {test,step,base} site;"
                    <> " a site at level d spans d -> d+1"
                  , "" ]
                  <> (if null ss
                        then ["no {t,s,b} sites reachable from main"]
                        else fmap fmt ss)
                  <> (if null bangs
                        then []
                        else "" : "variables used below their binding"
                               <> " (forced under !):"
                             : fmap fmtBang (sortOn (negate . snd) bangs))
                  <> [ ""
                     , "max box depth (towerHeight): " <> show depth ]
  where
    fmt r =
      "level " <> show (rLevel r)
        <> "  {t,s,b} in " <> rDef r
        <> maybe "" (\(l, c) -> " (line " <> show l
                                  <> ", col " <> show c <> ")")
                 (rLoc r)
        <> "  via " <> intercalate " > " (rPath r)
    fmtBang ((owner, v), k) =
      "  " <> owner <> "." <> v <> " : "
        <> concat (replicate k "!")
        <> " (copied " <> show k <> " level"
        <> (if k == 1 then "" else "s") <> " down)"
