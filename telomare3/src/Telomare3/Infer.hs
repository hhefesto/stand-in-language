-- | Level inference — the placement half of the Possible-successor.
--
-- Two layers, mirroring @telomare3\/spec\/T3\/Place.agda@:
--
--   1. The spec mirror: 'Skel'\/'Deco'\/'place'\/'solves'\/'meetD',
--      constructor-for-constructor with the Agda (which PROVES
--      place-solves, place-least, solves-meet, core-dominates; the
--      test suite re-checks the mirror by QuickCheck).
--
--   2. The named-definition layer: the @src\/Telomare\/Levels.hs@ recipe
--      (telomare1's @--emit-levels@ prototype, validated in
--      design\/VALIDATION.md) reimplemented over a mini-AST — syntactic
--      containment (a recursion site's contents live one level deeper)
--      plus parameter-offset summaries (an argument is pulled k levels
--      deeper when the callee uses the parameter k boxes down).  One
--      structural walk, no evaluation, no search: by place-least this
--      computes the LEAST stratification on the fragment.
--
-- test\/InferOracle.hs gates this against telomare1's actual
-- @--emit-levels@ output on the VALIDATION probe shapes.
module Telomare3.Infer
  ( -- * Spec mirror (T3.Place)
    Skel (..)
  , Deco (..)
  , place
  , solves
  , meetD
  , decoLE
    -- * Named-definition layer (Levels.hs recipe)
  , Expr (..)
  , Def (..)
  , Program
  , Levels (..)
  , inferLevels
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Numeric.Natural (Natural)

-- ── spec mirror ─────────────────────────────────────────────────────────────

-- | Recursion skeleton (spec: @T3.Place.Skel@).
data Skel = Tip | Bin Skel Skel | Rec Skel | Call Natural Skel
  deriving (Eq, Show)

-- | A decoration: one level per recursion site (spec: @T3.Place.Deco@).
data Deco = TipD | BinD Deco Deco | RecD Natural Deco | CallD Natural Deco
  deriving (Eq, Show)

-- | The structural walk (spec: @T3.Place.place@) — assign every site its
-- ambient depth.
place :: Natural -> Skel -> Deco
place _ Tip        = TipD
place d (Bin x y)  = BinD (place d x) (place d y)
place d (Rec s)    = RecD d (place (d + 1) s)
place d (Call k s) = CallD k (place (d + k) s)

-- | Stratification at ambient depth d (spec: @T3.Place.Solves@).
solves :: Natural -> Deco -> Bool
solves _ TipD        = True
solves d (BinD x y)  = solves d x && solves d y
solves d (RecD l x)  = d <= l && solves (l + 1) x
solves d (CallD k x) = solves (d + k) x

-- | Pointwise meet (spec: @T3.Place.meet@); requires same shape.
meetD :: Deco -> Deco -> Maybe Deco
meetD TipD TipD               = Just TipD
meetD (BinD x y) (BinD u v)   = BinD <$> meetD x u <*> meetD y v
meetD (RecD l x) (RecD l' y)  = RecD (min l l') <$> meetD x y
meetD (CallD k x) (CallD k' y)
  | k == k'                   = CallD k <$> meetD x y
meetD _ _                     = Nothing

-- | Pointwise order (spec: @T3.Place._⊑_@); Nothing = shape mismatch.
decoLE :: Deco -> Deco -> Maybe Bool
decoLE TipD TipD              = Just True
decoLE (BinD x y) (BinD u v)  = (&&) <$> decoLE x u <*> decoLE y v
decoLE (RecD l x) (RecD l' y) = ((l <= l') &&) <$> decoLE x y
decoLE (CallD k x) (CallD k' y)
  | k == k'                   = decoLE x y
decoLE _ _                    = Nothing

-- ── named-definition layer ──────────────────────────────────────────────────

-- | Mini-AST: just enough structure to carry the level-relevant shape of
-- real programs (the VALIDATION probe ports live in test\/InferOracle.hs).
data Expr
  = Leaf                       -- ^ level-irrelevant content
  | Var String                 -- ^ variable\/definition use
  | App String [Expr]          -- ^ call a definition with arguments
  | RecT Expr Expr Expr        -- ^ a @{test, step, base}@ recursion site
  | Lam String Expr            -- ^ binder
  | Let [(String, Expr)] Expr
  | Node [Expr]                -- ^ same-level grouping
  deriving (Eq, Show)

data Def = Def
  { defParams :: [String]
  , defBody   :: Expr
  }
  deriving (Eq, Show)

type Program = Map String Def

data Levels = Levels
  { lvSites       :: [(String, Natural)]        -- ^ (owning def, site level)
  , lvBangs       :: Map (String, String) Natural
    -- ^ (def, binding) ↦ k: used k iteration-levels below its binding (!^k)
  , lvTowerHeight :: Natural
  }
  deriving (Eq, Show)

-- Parameter-offset summaries: for each parameter of a definition, the max
-- box-offset of its occurrences in the body (Levels.hs paramOffsets).
paramOffsets :: Program -> Set String -> Def -> [Natural]
paramOffsets gs guard (Def params body) =
  fmap (\p -> occDepth gs guard p 0 body) params

occDepth :: Program -> Set String -> String -> Natural -> Expr -> Natural
occDepth _ _ _ _ Leaf = 0
occDepth _ _ p d (Var v) = if v == p then d else 0
occDepth gs guard p d (App h args) =
  let offs = headOffsets gs guard h
      argD (j, arg) = occDepth gs guard p (d + offAt offs j) arg
      headD = if h == p then d else 0
  in maximum (0 : headD : fmap argD (zip [0 ..] args))
occDepth gs guard p d (RecT a b c) =
  maximum (fmap (occDepth gs guard p (d + 1)) [a, b, c])
occDepth gs guard p d (Lam n b)
  | n == p    = 0
  | otherwise = occDepth gs guard p d b
occDepth gs guard p d (Let bs body)
  | p `elem` fmap fst bs = 0
  | otherwise =
      maximum (occDepth gs guard p d body : fmap (occDepth gs guard p d . snd) bs)
occDepth gs guard p d (Node xs) =
  maximum (0 : fmap (occDepth gs guard p d) xs)

headOffsets :: Program -> Set String -> String -> [Natural]
headOffsets gs guard h
  | h `Set.notMember` guard
  , Just def <- Map.lookup h gs = paramOffsets gs (Set.insert h guard) def
  | otherwise = []

offAt :: [Natural] -> Int -> Natural
offAt offs j = if j < length offs then offs !! j else 0

-- Walk state (Levels.hs St): visited (def, level) pairs, collected sites,
-- max (use − bind) per binding.
data St = St
  { stVisited :: Set (String, Natural)
  , stSites   :: [(String, Natural)]
  , stBangs   :: Map (String, String) Natural
  }

type Binds = Map String (String, Natural)

walk :: Program -> Map String Expr -> Binds -> String -> Natural -> Expr
     -> St -> St
walk _ _ _ _ _ Leaf st = st
walk gs ls bn dn d (RecT a b c) st =
  let st1 = st { stSites = (dn, d) : stSites st }
  in foldl (flip (walk gs ls bn dn (d + 1))) st1 [a, b, c]
walk gs ls bn dn d (App h args) st =
  let offs = headOffsets gs Set.empty h
      st1 = walk gs ls bn dn d (Var h) st
      argW s (j, arg) = walk gs ls bn dn (d + offAt offs j) arg s
  in foldl argW st1 (zip [0 ..] args)
walk gs ls bn dn d (Var v) st = enterVar (bang st)
  where
    bang s = case Map.lookup v bn of
      Nothing -> s
      Just (owner, bd) ->
        s { stBangs = Map.insertWith max (owner, v) (d - bd) (stBangs s) }
    enterVar s
      | Set.member (v, d) (stVisited s) = s
      | Just body <- Map.lookup v ls =
          walk gs ls bn v d body (mark s)
      | Just (Def ps body) <- Map.lookup v gs =
          let bn' = Map.fromList [(p, (v, d)) | p <- ps]
          in walk gs Map.empty bn' v d body (mark s)
      | otherwise = s
    mark s = s { stVisited = Set.insert (v, d) (stVisited s) }
walk gs ls bn dn d (Lam n b) st =
  walk gs (Map.delete n ls) (Map.insert n (dn, d) bn) dn d b st
walk gs ls bn dn d (Let bs body) st =
  let ls' = foldl (\m (n, rhs) -> Map.insert n rhs m) ls bs
      bn' = foldl (\m n -> Map.insert n (dn, d) m) bn (fmap fst bs)
  in walk gs ls' bn' dn d body st
walk gs ls bn dn d (Node xs) st =
  foldl (flip (walk gs ls bn dn d)) st xs

-- | Structural level inference from @main@ (Levels.hs levelsReport).
inferLevels :: Program -> Levels
inferLevels gs = case Map.lookup "main" gs of
  Nothing -> Levels [] Map.empty 0
  Just (Def ps body) ->
    let bn0 = Map.fromList [(p, ("main", 0)) | p <- ps]
        st  = walk gs Map.empty bn0 "main" 0 body (St Set.empty [] Map.empty)
        ss  = reverse (stSites st)
        h   = maximum (0 : fmap ((+ 1) . snd) ss)
        bs  = Map.filter (> 0) (stBangs st)
    in Levels ss bs h
