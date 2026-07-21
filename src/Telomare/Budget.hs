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
  , sizeS
  , sizeR
  , TyR (..)
  , tyROf
  , costW
  , costD
  , costSp
  , coversValue
  , shapeOfSTy
  ) where

import Numeric.Natural (Natural)

import Telomare.Core
import Telomare.Surface (SUTy (..), UVal)

-- | Shapes (spec: @T3.Abstract.Shape@), dynamically typed.
data ShapeH
  = TopS
  | UnitS
  | NatLE Natural
  | PairSh ShapeH ShapeH
  | SumSh (Maybe ShapeH) (Maybe ShapeH)
  | ListSh Natural ShapeH
  | BangSh ShapeH
  | LollySh (Maybe Natural)
    -- ^ Applying this closure costs at most n in the current analysis.
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
joinShape (LollySh a) (LollySh b)   = LollySh (joinMB a b)
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
    go (CurryS _ f)   = go f
    go MapCS          = RecT v TipT
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
transferB (CurryS _ f) _ = (fst (transferB f TopS), TopS)
transferB ApplyS _ = (TipT, TopS)
transferB MapCS _ = (RecT Nothing TipT, TopS)
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

-- | Static work bound (spec: @T3.Bound.costW@, mirrored 1:1): an
-- a-priori upper bound on the work grade of any covered input;
-- 'Nothing' = unbounded.  By @T3.Bound.costW-sound@ and adequacy, a
-- 'Just' bound is a machine fuel bound.
lollyCostOf :: ShapeH -> Maybe Natural
lollyCostOf (LollySh mc) = mc
lollyCostOf _            = Nothing

addC :: Maybe Natural -> Maybe Natural -> Maybe Natural
addC (Just a) (Just b) = Just (a + b)
addC _ _               = Nothing

mulC :: Maybe Natural -> Maybe Natural -> Maybe Natural
mulC (Just a) (Just b) = Just (a * b)
mulC _ _               = Nothing

-- | Type-sensitive static word-size bound (spec: @T3.Bound.sizeS@).
-- The witness distinguishes fixed-size unknown values such as Nat from
-- genuinely unbounded values such as lists.
sizeS :: STy a -> ShapeH -> Maybe Natural
sizeS SUnit TopS = Just 1
sizeS SNat TopS = Just 1
sizeS (SLolly _ _) TopS = Just 1
sizeS (SProd _ _) TopS = Nothing
sizeS (SSum _ _) TopS = Nothing
sizeS (SList _) TopS = Nothing
sizeS (SBang _) TopS = Nothing
sizeS SUnit UnitS = Just 1
sizeS SNat (NatLE _) = Just 1
sizeS (SProd a b) (PairSh sa sb) = addC (sizeS a sa) (sizeS b sb)
sizeS (SSum a b) (SumSh sa sb) =
  addC (Just 1) (joinMB (maybe (Just 0) (sizeS a) sa) (maybe (Just 0) (sizeS b) sb))
sizeS (SList a) (ListSh n sa) = listSize n
  where
    listSize 0 = Just 1
    listSize k = addC (Just 1) (addC (sizeS a sa) (listSize (k - 1)))
sizeS (SBang a) (BangSh sa) = sizeS a sa
sizeS (SLolly _ _) (LollySh _) = Just 1
sizeS _ _ = Nothing

aiterC :: (ShapeH -> (Maybe Natural, ShapeH)) -> Natural -> ShapeH
       -> (Maybe Natural, ShapeH)
aiterC _ 0 s = (Just 0, s)
aiterC f n s =
  let (c1, s1) = f s
      (cn, sn) = aiterC f (n - 1) s1
  in (addC (Just 1) (addC c1 cn), joinShape s sn)

costW :: Morph a b -> ShapeH -> (Maybe Natural, ShapeH)
costW IdS s = (Just 0, s)
costW (g :.: f) s =
  let (cf, sf) = costW f s
      (cg, sg) = costW g sf
  in (addC cf cg, sg)
costW (f :***: g) s =
  let (sa, sc) = splitP s
      (cf, sb) = costW f sa
      (cg, sd) = costW g sc
  in (addC cf cg, PairSh sb sd)
costW SwapS s = let (a, b) = splitP s in (Just 0, PairSh b a)
costW AssocS s =
  let (ab, c) = splitP s; (a, b) = splitP ab
  in (Just 0, PairSh a (PairSh b c))
costW UnassocS s =
  let (a, bc) = splitP s; (b, c) = splitP bc
  in (Just 0, PairSh (PairSh a b) c)
costW ExlS s = (Just 0, fst (splitP s))
costW ExrS s = (Just 0, snd (splitP s))
costW WeakS _ = (Just 0, UnitS)
costW RunitS s = (Just 0, PairSh s UnitS)
costW LunitS s = (Just 0, PairSh UnitS s)
costW InlS s = (Just 0, SumSh (Just s) Nothing)
costW InrS s = (Just 0, SumSh Nothing (Just s))
costW (CaseS l r) s =
  let (ml, mr) = splitE s
      resL = fmap (costW l) ml
      resR = fmap (costW r) mr
      costOf = maybe (Just 0) fst
      shape = case (resL, resR) of
        (Just (_, x), Just (_, y)) -> joinShape x y
        (Just (_, x), Nothing)     -> x
        (Nothing, Just (_, y))     -> y
        (Nothing, Nothing)         -> TopS
  in (joinMB (costOf resL) (costOf resR), shape)
costW DistlS s =
  let (a, bc) = splitP s
      (mb, mc) = splitE bc
  in (Just 0, SumSh (PairSh a <$> mb) (PairSh a <$> mc))
costW NilS _ = (Just 0, ListSh 0 TopS)
costW ConsS s =
  let (e, l) = splitP s
  in (Just 0, case l of
       ListSh n es -> ListSh (n + 1) (joinShape e es)
       _           -> TopS)
costW UnconsS s = (Just 0, SumSh (Just UnitS) (Just rest))
  where
    rest = case s of
      ListSh n es -> PairSh es (ListSh (predN n) es)
      _           -> PairSh TopS TopS
costW NatOutS s = (Just 1, case s of
  NatLE n -> SumSh (Just UnitS) (Just (NatLE (predN n)))
  _       -> SumSh (Just UnitS) (Just TopS))
costW SucS s = (Just 0, case s of
  NatLE n -> NatLE (n + 1)
  _       -> TopS)
costW AddS s =
  let (a, b) = splitP s
  in (Just 0, case (a, b) of
       (NatLE n, NatLE m) -> NatLE (n + m)
       _                  -> TopS)
costW (ConstS k) _ = (Just 0, NatLE k)
costW DupNatS s = (Just 0, PairSh s s)
costW (CopyS _) s = (Just 0, PairSh s s)
costW (CurryS _ f) s = (Just 0, LollySh (fst (costW f (PairSh s TopS))))
costW ApplyS s = (addC (Just 1) (lollyCostOf (fst (splitP s))), TopS)
costW MapCS s =
  let (sbf, sl) = splitP s
  in (mulC (lenOfS sl) (addC (Just 1) (lollyCostOf (unbangS sbf))), TopS)
costW (GuardS _ t) s = (fst (costW t s), SumSh (Just s) (Just UnitS))
costW (DupS _) s = (Just 0, PairSh s s)
costW (BoxS f) s = let (c, r) = costW f (unbangS s) in (c, BangSh r)
costW (BoxValS f) s = let (c, r) = costW f s in (c, BangSh r)
costW MergeS s =
  let (a, b) = splitP s
  in (Just 0, BangSh (PairSh (unbangS a) (unbangS b)))
costW (MapS f) s =
  (mulC (lenOfS s) (addC (Just 1) (fst (costW f (elemOfS s)))), TopS)
costW (IterS f) s =
  let (fu, a0) = splitP s
  in case fu of
       NatLE n -> let (c, r) = aiterC (costW f) n (unbangS a0)
                  in (c, BangSh r)
       _       -> (Nothing, TopS)
costW (FoldS f) s =
  let (ls, b0) = splitP s
  in case ls of
       ListSh n _ ->
         let (c, r) = aiterC (\x -> costW f (PairSh x (elemOfS ls))) n
                        (unbangS b0)
         in (c, BangSh r)
       _ -> (Nothing, TopS)
costW (WhileS _ t st) s =
  let (fu, a0) = splitP s
      stepC x = let (ct, _) = costW t x
                    (cs, r) = costW st x
                in (addC ct cs, r)
  in case fu of
       NatLE n -> let (c, r) = aiterC stepC n (unbangS a0)
                  in (c, BangSh r)
       _       -> (Nothing, TopS)

-- | Partial core-type representation threaded through 'costSp' so the
-- typed view of sizes survives composite traversal: an atomic @TopS@
-- (nat, unit, closure) is one word, exactly as the Agda @sizeS@
-- resolves it through the type index.  'RUnknown' appears only where
-- the traversal genuinely loses the type (apply results, mapCS
-- elements); its sizes are unbounded.
data TyR
  = RUnit
  | RNat
  | RProd TyR TyR
  | RSum TyR TyR
  | RList TyR
  | RBang TyR
  | RLolly
  | RUnknown
  deriving (Eq, Show)

tyROf :: STy a -> TyR
tyROf SUnit        = RUnit
tyROf SNat         = RNat
tyROf (SProd a b)  = RProd (tyROf a) (tyROf b)
tyROf (SSum a b)   = RSum (tyROf a) (tyROf b)
tyROf (SList a)    = RList (tyROf a)
tyROf (SBang a)    = RBang (tyROf a)
tyROf (SLolly _ _) = RLolly

splitRP :: TyR -> (TyR, TyR)
splitRP (RProd a b) = (a, b)
splitRP _           = (RUnknown, RUnknown)

splitRE :: TyR -> (TyR, TyR)
splitRE (RSum a b) = (a, b)
splitRE _          = (RUnknown, RUnknown)

unbangR :: TyR -> TyR
unbangR (RBang a) = a
unbangR _         = RUnknown

elemR :: TyR -> TyR
elemR (RList a) = a
elemR _         = RUnknown

pickR :: TyR -> TyR -> TyR
pickR RUnknown r = r
pickR r _        = r

-- | Typed static word-size bound over the partial representation
-- (spec: @T3.Bound.sizeS@; the Agda @topS@ clauses are the RUnit/RNat/
-- RLolly TopS cases here).
sizeR :: TyR -> ShapeH -> Maybe Natural
sizeR RUnit  TopS = Just 1
sizeR RNat   TopS = Just 1
sizeR RLolly TopS = Just 1
sizeR _      TopS = Nothing
sizeR _ UnitS     = Just 1
sizeR _ (NatLE _) = Just 1
sizeR r (PairSh a b) =
  let (x, y) = splitRP r in addC (sizeR x a) (sizeR y b)
sizeR r (SumSh a b) =
  let (x, y) = splitRE r
  in addC (Just 1)
       (joinMB (maybe (Just 0) (sizeR x) a) (maybe (Just 0) (sizeR y) b))
sizeR r (ListSh n a) = listSizeR n (elemR r) a
sizeR r (BangSh a)   = sizeR (unbangR r) a
sizeR _ (LollySh _)  = Just 1

listSizeR :: Natural -> TyR -> ShapeH -> Maybe Natural
listSizeR 0 _ _  = Just 1
listSizeR k r es = addC (Just 1) (addC (sizeR r es) (listSizeR (k - 1) r es))

-- spec: T3.SpaceBound.aiterSp — rounds join by max, every round also
-- charges the current shape's size so an early dynamic stop is dominated.
aiterSp :: TyR -> (ShapeH -> (Maybe Natural, ShapeH)) -> Natural -> ShapeH
        -> (Maybe Natural, ShapeH)
aiterSp r _ 0 s = (sizeR r s, s)
aiterSp r f n s =
  let (c1, s1) = f s
      (cn, sn) = aiterSp r f (n - 1) s1
  in (joinMB (sizeR r s) (joinMB c1 cn), joinShape s sn)

-- spec: T3.SpaceBound.mapSpC — tail retained through the round, produced
-- element through the rest of the traversal.
mapSpR :: Natural -> TyR -> ShapeH -> TyR -> ShapeH -> Maybe Natural
       -> Maybe Natural
mapSpR 0 _ _ _ _ _        = Just 1
mapSpR n re es rb rs cb =
  joinMB (addC (listSizeR (n - 1) re es) cb)
         (addC (sizeR rb rs) (mapSpR (n - 1) re es rb rs cb))

-- | Static live-heap space bound (spec: @T3.SpaceBound.spaceS@, proved
-- sound there by @spaceS-sound@ against @T3.Sem.Space.⟦_⟧S@).  The TyR
-- component resolves atomic top sizes; wherever it degrades to
-- 'RUnknown' the result only gets looser, never unsound.
costSp :: TyR -> Morph a b -> ShapeH -> (Maybe Natural, ShapeH, TyR)
costSp r IdS s = (sizeR r s, s, r)
costSp r (g :.: f) s =
  let (cf, sf, rf) = costSp r f s
      (cg, sg, rg) = costSp rf g sf
  in (joinMB cf cg, sg, rg)
costSp r (f :***: g) s =
  let (ra, rc) = splitRP r
      (sa, sc) = splitP s
      (cf, sb, rb) = costSp ra f sa
      (cg, sd, rd) = costSp rc g sc
  in ( joinMB (addC (sizeR rc sc) cf) (addC (sizeR rb sb) cg)
     , PairSh sb sd, RProd rb rd)
costSp r SwapS s =
  let (ra, rb) = splitRP r
      (a, b) = splitP s
  in (sizeR r s, PairSh b a, RProd rb ra)
costSp r AssocS s =
  let (rab, rc) = splitRP r; (ra, rb) = splitRP rab
      (ab, c) = splitP s; (a, b) = splitP ab
  in (sizeR r s, PairSh a (PairSh b c), RProd ra (RProd rb rc))
costSp r UnassocS s =
  let (ra, rbc) = splitRP r; (rb, rc) = splitRP rbc
      (a, bc) = splitP s; (b, c) = splitP bc
  in (sizeR r s, PairSh (PairSh a b) c, RProd (RProd ra rb) rc)
costSp r ExlS s = (sizeR r s, fst (splitP s), fst (splitRP r))
costSp r ExrS s = (sizeR r s, snd (splitP s), snd (splitRP r))
costSp r WeakS s = (sizeR r s, UnitS, RUnit)
costSp r RunitS s = (addC (Just 1) (sizeR r s), PairSh s UnitS, RProd r RUnit)
costSp r LunitS s = (addC (Just 1) (sizeR r s), PairSh UnitS s, RProd RUnit r)
costSp r InlS s =
  (addC (Just 1) (sizeR r s), SumSh (Just s) Nothing, RSum r RUnknown)
costSp r InrS s =
  (addC (Just 1) (sizeR r s), SumSh Nothing (Just s), RSum RUnknown r)
costSp r (CaseS l rr) s =
  let (rl, rrt) = splitRE r
      (ml, mr) = splitE s
      resL = fmap (costSp rl l) ml
      resR = fmap (costSp rrt rr) mr
      costOf = maybe (Just 0) (\(c, _, _) -> c)
      shape = case (resL, resR) of
        (Just (_, x, _), Just (_, y, _)) -> joinShape x y
        (Just (_, x, _), Nothing)        -> x
        (Nothing, Just (_, y, _))        -> y
        (Nothing, Nothing)               -> TopS
      tyOut = case (resL, resR) of
        (Just (_, _, x), Just (_, _, y)) -> pickR x y
        (Just (_, _, x), Nothing)        -> x
        (Nothing, Just (_, _, y))        -> y
        (Nothing, Nothing)               -> RUnknown
  in (joinMB (sizeR r s) (joinMB (costOf resL) (costOf resR)), shape, tyOut)
costSp r DistlS s =
  let (ra, rbc) = splitRP r; (rb, rc) = splitRE rbc
      (a, bc) = splitP s
      (mb, mc) = splitE bc
  in ( sizeR r s
     , SumSh (PairSh a <$> mb) (PairSh a <$> mc)
     , RSum (RProd ra rb) (RProd ra rc))
costSp _ NilS _ = (Just 1, ListSh 0 TopS, RList RUnknown)
costSp r ConsS s =
  let (re, rl) = splitRP r
      (e, l) = splitP s
  in ( addC (Just 1) (sizeR r s)
     , case l of
         ListSh n es -> ListSh (n + 1) (joinShape e es)
         _           -> TopS
     , RList (pickR re (elemR rl)))
costSp r UnconsS s =
  ( addC (Just 1) (sizeR r s)
  , SumSh (Just UnitS) (Just rest)
  , RSum RUnit (RProd (elemR r) r))
  where
    rest = case s of
      ListSh n es -> PairSh es (ListSh (predN n) es)
      _           -> PairSh TopS TopS
costSp _ NatOutS s =
  ( Just 2
  , case s of
      NatLE n -> SumSh (Just UnitS) (Just (NatLE (predN n)))
      _       -> SumSh (Just UnitS) (Just TopS)
  , RSum RUnit RNat)
costSp _ SucS s = (Just 1, case s of
  NatLE n -> NatLE (n + 1)
  _       -> TopS
  , RNat)
costSp _ AddS s =
  let (a, b) = splitP s
  in (Just 2, case (a, b) of
       (NatLE n, NatLE m) -> NatLE (n + m)
       _                  -> TopS
     , RNat)
costSp r (ConstS k) s = (sizeR r s, NatLE k, RNat)
costSp _ DupNatS s = (Just 2, PairSh s s, RProd RNat RNat)
costSp r (CopyS _) s =
  (addC (sizeR r s) (sizeR r s), PairSh s s, RProd r r)
costSp r (GuardS _ t) s =
  let (ct, _, _) = costSp r t s
  in ( joinMB ct (addC (Just 1) (sizeR r s))
     , SumSh (Just s) (Just UnitS)
     , RSum r RUnit)
costSp r (CurryS _ f) s =
  let (cb, _, _) = costSp (RProd r RUnknown) f (PairSh s TopS)
  in (sizeR r s, LollySh cb, RLolly)
costSp r ApplyS s =
  let (_, ra) = splitRP r
      (sf, sa) = splitP s
  in ( joinMB (addC (Just 1) (sizeR ra sa)) (lollyCostOf sf)
     , TopS, RUnknown)
costSp r MapCS s =
  let (rbf, rl) = splitRP r
      (sbf, sl) = splitP s
  in ( case sl of
         ListSh n es ->
           addC (Just 1)
             (mapSpR n (elemR rl) es RUnknown TopS
               (lollyCostOf (unbangS sbf)))
         _ -> Nothing
     , TopS, RBang (RList RUnknown))
costSp r (DupS _) s =
  (addC (sizeR r s) (sizeR r s), PairSh s s, RProd r r)
costSp r (BoxS f) s =
  let (c, r', rf) = costSp (unbangR r) f (unbangS s) in (c, BangSh r', RBang rf)
costSp r (BoxValS f) s =
  let (c, r', rf) = costSp r f s in (c, BangSh r', RBang rf)
costSp r MergeS s =
  let (ra, rb) = splitRP r
      (a, b) = splitP s
  in ( sizeR r s
     , BangSh (PairSh (unbangS a) (unbangS b))
     , RBang (RProd (unbangR ra) (unbangR rb)))
costSp r (MapS f) s = case s of
  ListSh n es ->
    let (cb, re, rb) = costSp (elemR r) f es
    in (mapSpR n (elemR r) es rb re cb, TopS, RBang (RList rb))
  _ -> (Nothing, TopS, RBang (RList RUnknown))
costSp r (IterS f) s =
  let (_, racc0) = splitRP r
      racc = unbangR racc0
      (fu, a0) = splitP s
  in case fu of
       NatLE n ->
         let step x = let (c, r', _) = costSp racc f x in (c, r')
             (c, r') = aiterSp racc step n (unbangS a0)
         in (addC (Just 1) c, BangSh r', RBang racc)
       _ -> (Nothing, TopS, RBang racc)
costSp r (FoldS f) s =
  let (rl, racc0) = splitRP r
      racc = unbangR racc0
      relem = elemR rl
      (ls, b0) = splitP s
  in case ls of
       ListSh n es ->
         let step x = let (cb, rb, _) = costSp (RProd racc relem) f (PairSh x es)
                      in (addC (listSizeR n relem es) cb, rb)
             (c, r') = aiterSp racc step n (unbangS b0)
         in (joinMB (sizeR r s) c, BangSh r', RBang racc)
       _ -> (Nothing, TopS, RBang racc)
costSp r (WhileS _ t st) s =
  let (_, racc0) = splitRP r
      racc = unbangR racc0
      (fu, a0) = splitP s
      step x = let (ct, _, _) = costSp racc t x
                   (cs, r', _) = costSp racc st x
               in (joinMB ct cs, r')
  in case fu of
       NatLE n ->
         let (c, r') = aiterSp racc step n (unbangS a0)
         in (addC (Just 1) c, BangSh r', RBang racc)
       _ -> (Nothing, TopS, RBang racc)

-- | Runtime input validation: the value-level mirror of the Agda
-- coverage relation @γW@ (closures are conservatively rejected — a
-- closure bound is semantic and machine inputs are first-order anyway).
-- This is what makes a conditional @--assume-shape@ certificate honest:
-- every admitted input is checked, nonconforming input is refused.
coversValue :: SUTy a -> ShapeH -> UVal a -> Bool
coversValue _ TopS _ = True
coversValue SUUnit UnitS _ = True
coversValue SUNat (NatLE n) v = v <= n
coversValue (SUProd a b) (PairSh sa sb) (x, y) =
  coversValue a sa x && coversValue b sb y
coversValue (SUSum a _) (SumSh (Just sa) _) (Left x) = coversValue a sa x
coversValue (SUSum _ b) (SumSh _ (Just sb)) (Right y) = coversValue b sb y
coversValue (SUList a) (ListSh n es) xs =
  fromIntegral (length xs) <= n && all (coversValue a es) xs
coversValue _ _ _ = False

-- Duplication multiplication preserves the useful affine case:
-- an unknown number of zero-cost rounds still costs zero.
mulD :: Maybe Natural -> Maybe Natural -> Maybe Natural
mulD _ (Just 0)        = Just 0
mulD (Just 0) _        = Just 0
mulD (Just a) (Just b) = Just (a * b)
mulD _ _               = Nothing

aiterD :: (ShapeH -> (Maybe Natural, ShapeH)) -> Natural -> ShapeH
       -> (Maybe Natural, ShapeH)
aiterD _ 0 s = (Just 0, s)
aiterD f n s =
  let (c1, s1) = f s
      (cn, sn) = aiterD f (n - 1) s1
  in (addC c1 cn, joinShape s sn)

-- | Certified static duplication bound (spec: @T3.Bound.costD@).  This
-- mirrors 'dupAlg': copies and probes charge static word size, while affine
-- plumbing and loop steps are free.
costD :: Morph a b -> ShapeH -> (Maybe Natural, ShapeH)
costD IdS s = (Just 0, s)
costD (g :.: f) s =
  let (cf, sf) = costD f s
      (cg, sg) = costD g sf
  in (addC cf cg, sg)
costD (f :***: g) s =
  let (sa, sc) = splitP s
      (cf, sb) = costD f sa
      (cg, sd) = costD g sc
  in (addC cf cg, PairSh sb sd)
costD SwapS s = let (a, b) = splitP s in (Just 0, PairSh b a)
costD AssocS s =
  let (ab, c) = splitP s; (a, b) = splitP ab
  in (Just 0, PairSh a (PairSh b c))
costD UnassocS s =
  let (a, bc) = splitP s; (b, c) = splitP bc
  in (Just 0, PairSh (PairSh a b) c)
costD ExlS s = (Just 0, fst (splitP s))
costD ExrS s = (Just 0, snd (splitP s))
costD WeakS _ = (Just 0, UnitS)
costD RunitS s = (Just 0, PairSh s UnitS)
costD LunitS s = (Just 0, PairSh UnitS s)
costD InlS s = (Just 0, SumSh (Just s) Nothing)
costD InrS s = (Just 0, SumSh Nothing (Just s))
costD (CaseS l r) s =
  let (ml, mr) = splitE s
      resL = costD l <$> ml
      resR = costD r <$> mr
      costOf = maybe (Just 0) fst
      shape = case (resL, resR) of
        (Just (_, x), Just (_, y)) -> joinShape x y
        (Just (_, x), Nothing)     -> x
        (Nothing, Just (_, y))     -> y
        (Nothing, Nothing)         -> TopS
  in (joinMB (costOf resL) (costOf resR), shape)
costD DistlS s =
  let (a, bc) = splitP s
      (mb, mc) = splitE bc
  in (Just 0, SumSh (PairSh a <$> mb) (PairSh a <$> mc))
costD NilS _ = (Just 0, ListSh 0 TopS)
costD ConsS s =
  let (e, l) = splitP s
  in (Just 0, case l of
       ListSh n es -> ListSh (n + 1) (joinShape e es)
       _           -> TopS)
costD UnconsS s = (Just 0, SumSh (Just UnitS) (Just rest))
  where
    rest = case s of
      ListSh n es -> PairSh es (ListSh (predN n) es)
      _           -> PairSh TopS TopS
costD NatOutS s = (Just 0, case s of
  NatLE n -> SumSh (Just UnitS) (Just (NatLE (predN n)))
  _       -> SumSh (Just UnitS) (Just TopS))
costD SucS s = (Just 0, case s of
  NatLE n -> NatLE (n + 1)
  _       -> TopS)
costD AddS s =
  let (a, b) = splitP s
  in (Just 0, case (a, b) of
       (NatLE n, NatLE m) -> NatLE (n + m)
       _                  -> TopS)
costD (ConstS k) _ = (Just 0, NatLE k)
costD DupNatS s = (Just 1, PairSh s s)
costD (CopyS w) s = (sizeS (copyableSTy w) s, PairSh s s)
costD (GuardS sa t) s =
  (addC (sizeS sa s) (fst (costD t s)), SumSh (Just s) (Just UnitS))
costD (CurryS _ f) s = (Just 0, LollySh (fst (costD f (PairSh s TopS))))
costD ApplyS s = (lollyCostOf (fst (splitP s)), TopS)
costD MapCS s =
  let (sbf, sl) = splitP s
  in (mulD (lenOfS sl) (lollyCostOf (unbangS sbf)), TopS)
costD (DupS sa) s = (sizeS (SBang sa) s, PairSh s s)
costD (BoxS f) s = let (c, r) = costD f (unbangS s) in (c, BangSh r)
costD (BoxValS f) s = let (c, r) = costD f s in (c, BangSh r)
costD MergeS s =
  let (a, b) = splitP s
  in (Just 0, BangSh (PairSh (unbangS a) (unbangS b)))
costD (MapS f) s = (mulD (lenOfS s) (fst (costD f (elemOfS s))), TopS)
costD (IterS f) s =
  let (fu, a0) = splitP s
  in case fu of
       NatLE n -> let (c, r) = aiterD (costD f) n (unbangS a0)
                  in (c, BangSh r)
       _       -> (Nothing, TopS)
costD (FoldS f) s =
  let (ls, b0) = splitP s
  in case ls of
       ListSh n _ ->
         let (c, r) = aiterD (\x -> costD f (PairSh x (elemOfS ls))) n
                        (unbangS b0)
         in (c, BangSh r)
       _ -> (Nothing, TopS)
costD (WhileS sa t st) s =
  let (fu, a0) = splitP s
      roundD x = let (ct, _) = costD t x
                     (cs, r) = costD st x
                 in (addC (sizeS sa x) (addC ct cs), r)
  in case fu of
       NatLE n -> let (c, r) = aiterD roundD n (unbangS a0)
                  in (c, BangSh r)
       _       -> (Nothing, TopS)

lenOfS :: ShapeH -> Maybe Natural
lenOfS (ListSh n _) = Just n
lenOfS _            = Nothing

elemOfS :: ShapeH -> ShapeH
elemOfS (ListSh _ e) = e
elemOfS _            = TopS

-- | The all-top shape of a surface type: what --certificate may assume
-- about an arbitrary input (spec: @T3.Bound.shapeOfTy@ over Lift).
shapeOfSTy :: SUTy a -> ShapeH
shapeOfSTy SUUnit        = UnitS
shapeOfSTy SUNat         = TopS
shapeOfSTy (SUProd a b)  = PairSh (shapeOfSTy a) (shapeOfSTy b)
shapeOfSTy (SUSum a b)   = SumSh (Just (shapeOfSTy a)) (Just (shapeOfSTy b))
shapeOfSTy (SUList _)    = TopS
shapeOfSTy (SULolly _ _) = LollySh Nothing
