{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}

-- | Budget inference — Haskell mirror of @spec\/T3\/Abstract.agda@ (M4).
--
-- The Possible-successor: because Telomare fuel is data, recursion
-- budgets are value-range analysis.  'ShapeH' mirrors the Agda @Shape@
-- (untyped here — the GADT's index does the typing; shapes are checked
-- dynamically), 'transferB' mirrors @transfer@ (fuel-bounded abstract
-- unrolling: budgets joined over every unrolling by
-- construction), and the Agda proves soundness (@sound@) and stability
-- (@while-stable@).  test\/BudgetOracle.hs transcribes the
-- Examples.Budgets refl facts 1:1 and records the churchK oracle mapping
-- compatibility oracle mapping.
module Telomare.Budget
  ( ShapeH (..)
  , BudgetT (..)
  , joinShape
  , transferB
  ) where

import Numeric.Natural (Natural)

import Telomare.Core

-- | Shapes (spec: @T3.Abstract.Shape@), dynamically typed.
data ShapeH
  = TopS
  | UnitS
  | NatLE Natural
  | PairSh ShapeH ShapeH
  | SumSh (Maybe ShapeH) (Maybe ShapeH)
  | ListSh Natural ShapeH
  | BangSh ShapeH
  deriving (Eq, Show)

-- | Budget trees over the recursion skeleton (spec: @T3.Abstract.BudgetD@;
-- 'Nothing' at a site = unsizable ⊤ — a Tier-2 notice, never a rejection).
data BudgetT
  = TipT
  | BinT BudgetT BudgetT
  | RecT (Maybe Natural) BudgetT
  deriving (Eq, Show)

joinMB :: Maybe Natural -> Maybe Natural -> Maybe Natural
joinMB (Just a) (Just b) = Just (max a b)
joinMB _ _               = Nothing

joinB :: BudgetT -> BudgetT -> BudgetT
joinB TipT TipT             = TipT
joinB (BinT a b) (BinT c d) = BinT (joinB a c) (joinB b d)
joinB (RecT m a) (RecT n b) = RecT (joinMB m n) (joinB a b)
joinB a _                   = a   -- shape mismatch cannot happen on mirrored skeletons

joinM :: Maybe ShapeH -> Maybe ShapeH -> Maybe ShapeH
joinM (Just x) (Just y) = Just (joinShape x y)
joinM (Just x) Nothing  = Just x
joinM Nothing  y        = y

-- | Sound join (spec: @_⊔S_@).
joinShape :: ShapeH -> ShapeH -> ShapeH
joinShape TopS _                    = TopS
joinShape _ TopS                    = TopS
joinShape UnitS UnitS               = UnitS
joinShape (NatLE a) (NatLE b)       = NatLE (max a b)
joinShape (PairSh a b) (PairSh c d) = PairSh (joinShape a c) (joinShape b d)
joinShape (SumSh l r) (SumSh l' r') = SumSh (joinM l l') (joinM r r')
joinShape (ListSh n a) (ListSh m b) = ListSh (max n m) (joinShape a b)
joinShape (BangSh a) (BangSh b)     = BangSh (joinShape a b)
joinShape _ _                       = TopS

splitP :: ShapeH -> (ShapeH, ShapeH)
splitP (PairSh a b) = (a, b)
splitP _            = (TopS, TopS)

splitE :: ShapeH -> (Maybe ShapeH, Maybe ShapeH)
splitE (SumSh l r) = (l, r)
splitE _           = (Just TopS, Just TopS)

unbangS :: ShapeH -> ShapeH
unbangS (BangSh s) = s
unbangS _          = TopS

skelBot :: Morph a b -> BudgetT
skelBot = skelWith (Just 0)

skelTop :: Morph a b -> BudgetT
skelTop = skelWith Nothing

-- budget tree matching a morphism's recursion skeleton (spec: botBD/topBD
-- over skelOf ∘ ε)
skelWith :: Maybe Natural -> Morph a b -> BudgetT
skelWith v = go
  where
    go :: Morph a b -> BudgetT
    go (g :.: f)      = BinT (go g) (go f)
    go (f :***: g)    = BinT (go f) (go g)
    go (CaseS l r)    = BinT (go l) (go r)
    go (GuardS _ t)   = go t
    go (BoxS f)       = go f
    go (BoxValS f)    = go f
    go (MapS f)       = RecT v (go f)
    go (IterS f)      = RecT v (go f)
    go (FoldS f)      = RecT v (go f)
    go (WhileS _ t s) = RecT v (BinT (go t) (go s))
    go _              = TipT

-- fuel-bounded abstract unrolling (spec: aiter)
aiterB :: BudgetT -> (ShapeH -> (BudgetT, ShapeH)) -> Natural -> ShapeH
       -> (BudgetT, ShapeH)
aiterB bot _ 0 s = (bot, s)
aiterB bot f n s =
  let (b1, s1) = f s
      (bn, sn) = aiterB bot f (n - 1) s1
  in (joinB b1 bn, joinShape s sn)

-- | Transfer with budget collection (spec: @T3.Abstract.transfer@).
transferB :: Morph a b -> ShapeH -> (BudgetT, ShapeH)
transferB IdS s = (TipT, s)
transferB (g :.: f) s =
  let (bf, sf) = transferB f s
      (bg, sg) = transferB g sf
  in (BinT bg bf, sg)
transferB (f :***: g) s =
  let (sa, sc) = splitP s
      (bf, sb) = transferB f sa
      (bg, sd) = transferB g sc
  in (BinT bf bg, PairSh sb sd)
transferB SwapS s = let (a, b) = splitP s in (TipT, PairSh b a)
transferB AssocS s =
  let (ab, c) = splitP s; (a, b) = splitP ab
  in (TipT, PairSh a (PairSh b c))
transferB UnassocS s =
  let (a, bc) = splitP s; (b, c) = splitP bc
  in (TipT, PairSh (PairSh a b) c)
transferB ExlS s = (TipT, fst (splitP s))
transferB ExrS s = (TipT, snd (splitP s))
transferB WeakS _ = (TipT, UnitS)
transferB RunitS s = (TipT, PairSh s UnitS)
transferB LunitS s = (TipT, PairSh UnitS s)
transferB InlS s = (TipT, SumSh (Just s) Nothing)
transferB InrS s = (TipT, SumSh Nothing (Just s))
transferB (CaseS l r) s =
  let (ml, mr) = splitE s
      resL = fmap (transferB l) ml
      resR = fmap (transferB r) mr
      budget side fallback = maybe fallback fst side
      shape = case (resL, resR) of
        (Just (_, x), Just (_, y)) -> joinShape x y
        (Just (_, x), Nothing)     -> x
        (Nothing, Just (_, y))     -> y
        (Nothing, Nothing)         -> TopS
  in (BinT (budget resL (skelBot l)) (budget resR (skelBot r)), shape)
transferB DistlS s =
  let (a, bc) = splitP s
      (mb, mc) = splitE bc
  in (TipT, SumSh (PairSh a <$> mb) (PairSh a <$> mc))
transferB NilS _ = (TipT, ListSh 0 TopS)
transferB ConsS s =
  let (e, l) = splitP s
  in (TipT, case l of
       ListSh n es -> ListSh (n + 1) (joinShape e es)
       _           -> TopS)
transferB UnconsS s = (TipT, SumSh (Just UnitS) (Just rest))
  where
    rest = case s of
      ListSh n es -> PairSh es (ListSh (predN n) es)
      _           -> PairSh TopS TopS
transferB NatOutS s = (TipT, case s of
  NatLE n -> SumSh (Just UnitS) (Just (NatLE (predN n)))
  _       -> SumSh (Just UnitS) (Just TopS))
transferB SucS s = (TipT, case s of
  NatLE n -> NatLE (n + 1)
  _       -> TopS)
transferB AddS s =
  let (a, b) = splitP s
  in (TipT, case (a, b) of
       (NatLE n, NatLE m) -> NatLE (n + m)
       _                  -> TopS)
transferB (ConstS k) _ = (TipT, NatLE k)
transferB DupNatS s = (TipT, PairSh s s)
transferB (CopyS _) s = (TipT, PairSh s s)
transferB (GuardS _ t) s =
  let (bt, _) = transferB t s
  in (bt, SumSh (Just s) (Just UnitS))
transferB (DupS _) s = (TipT, PairSh s s)
transferB (BoxS f) s = let (b, r) = transferB f (unbangS s) in (b, BangSh r)
transferB (BoxValS f) s = let (b, r) = transferB f s in (b, BangSh r)
transferB MergeS s =
  let (a, b) = splitP s
  in (TipT, BangSh (PairSh (unbangS a) (unbangS b)))
transferB (MapS f) _ = (RecT Nothing (skelTop f), TopS)
transferB (IterS f) s =
  let (fu, a0) = splitP s
  in case fu of
       NatLE n ->
         let (b, r) = aiterB (skelBot f) (transferB f) n (unbangS a0)
         in (RecT (Just n) b, BangSh r)
       _ -> (RecT Nothing (skelTop f), TopS)
transferB (FoldS f) s =
  let (ls, b0) = splitP s
  in case ls of
       ListSh n es ->
         let (b, r) = aiterB (skelBot f)
                        (\x -> transferB f (PairSh x es)) n (unbangS b0)
         in (RecT (Just n) b, BangSh r)
       _ -> (RecT Nothing (skelTop f), TopS)
transferB (WhileS _ t st) s =
  let (fu, a0) = splitP s
      stepB x = let (bt, _) = transferB t x
                    (bs, r) = transferB st x
                in (BinT bt bs, r)
  in case fu of
       NatLE n ->
         let (b, r) = aiterB (BinT (skelBot t) (skelBot st)) stepB n (unbangS a0)
         in (RecT (Just n) b, BangSh r)
       _ -> (RecT Nothing (BinT (skelTop t) (skelTop st)), TopS)

predN :: Natural -> Natural
predN 0 = 0
predN n = n - 1
