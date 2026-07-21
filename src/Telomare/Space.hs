{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

-- | The live-heap space meter — Haskell mirror of @spec\/T3\/Sem\/Space.agda@.
--
-- A dedicated sized interpreter (deliberately not a 'CostAlgebra'
-- instance — see "Telomare.Denotation"): retention needs the sizes of
-- values that are not part of the current leaf transition.  The typed
-- evaluators cannot thread intermediate singletons, so the meter runs
-- on an untyped sized-value universe 'DVal' ('toDVal' injects a typed
-- value; the artifact is well typed, so the partial matches in 'evalSp'
-- cannot fail on values it produces).
--
-- Sizes follow 'sizeVal' (boxes weightless, closures one word — the
-- pointer model; a closure environment's words surface when its body
-- runs, because application re-enters 'evalSp' on (env, argument)).
module Telomare.Space
  ( DVal (..)
  , dSize
  , toDVal
  , evalSp
  , spacePeak
  ) where

import Numeric.Natural (Natural)

import Telomare.Core

-- | Untyped sized values.  'DSum' tags 'False' for left\/'Left',
-- 'True' for right\/'Right'.  A closure carries its body syntax and
-- captured environment (mirror of 'Closure').
data DVal where
  DUnit :: DVal
  DNat  :: Natural -> DVal
  DPair :: DVal -> DVal -> DVal
  DSum  :: Bool -> DVal -> DVal
  DList :: [DVal] -> DVal
  DClo  :: Morph (c ':*: a) b -> DVal -> DVal

-- | Word model of untyped value size (mirror of 'sizeVal'/@sizeG@).
dSize :: DVal -> Natural
dSize DUnit        = 1
dSize (DNat _)     = 1
dSize (DPair a b)  = dSize a + dSize b
dSize (DSum _ v)   = 1 + dSize v
dSize (DList xs)   = go xs
  where
    go []       = 1
    go (x : ys) = 1 + dSize x + go ys
dSize (DClo _ _)   = 1

-- | Inject a typed value into the sized universe.
toDVal :: STy a -> Val a -> DVal
toDVal SUnit        _         = DUnit
toDVal SNat         n         = DNat n
toDVal (SProd s t)  (a, b)    = DPair (toDVal s a) (toDVal t b)
toDVal (SSum s _)   (Left a)  = DSum False (toDVal s a)
toDVal (SSum _ t)   (Right b) = DSum True (toDVal t b)
toDVal (SList s)    xs        = DList (fmap (toDVal s) xs)
toDVal (SBang s)    a         = toDVal s a
toDVal (SLolly _ _) (Closure c body env) = DClo body (toDVal c env)

applyClo :: DVal -> DVal -> (Natural, DVal)
applyClo (DClo body env) a = evalSp body (DPair env a)
applyClo _ _ = error "space meter: applied a non-closure"

mapSp :: (DVal -> (Natural, DVal)) -> [DVal] -> (Natural, [DVal])
mapSp _ [] = (1, [])
mapSp f (x : xs) =
  let (pb, y)  = f x
      (pr, ys) = mapSp f xs
  in (max (dSize (DList xs) + pb) (dSize y + pr), y : ys)

iterSp :: (DVal -> (Natural, DVal)) -> Natural -> DVal -> (Natural, DVal)
iterSp _ 0 a = (dSize a, a)
iterSp f n a =
  let (pb, b) = f a
      (pr, c) = iterSp f (n - 1) b
  in (max pb pr, c)

foldSp :: (DVal -> (Natural, DVal)) -> [DVal] -> DVal -> (Natural, DVal)
foldSp _ [] b = (dSize b, b)
foldSp f (x : xs) b =
  let (pb, b') = f (DPair b x)
      (pr, c)  = foldSp f xs b'
  in (max (dSize (DList xs) + pb) pr, c)

whileSp :: (DVal -> (Natural, DVal)) -> (DVal -> (Natural, DVal))
        -> Natural -> DVal -> (Natural, DVal)
whileSp _ _ 0 a = (dSize a, a)
whileSp t s n a =
  let (pt, r) = t a
  in case r of
       DSum False _ -> (max pt (dSize a), a)
       DSum True _  ->
         let (ps, b) = s a
             (pr, c) = whileSp t s (n - 1) b
         in (max pt (max ps pr), c)
       _ -> error "space meter: while test returned a non-verdict"

-- | The sized interpreter (mirror of @⟦_⟧S@): peak live words and value.
evalSp :: Morph a b -> DVal -> (Natural, DVal)
evalSp IdS v = (dSize v, v)
evalSp (g :.: f) v =
  let (pf, b) = evalSp f v
      (pg, c) = evalSp g b
  in (max pf pg, c)
evalSp (f :***: g) (DPair a c) =
  let (pf, b) = evalSp f a
      (pg, d) = evalSp g c
  in (max (dSize c + pf) (dSize b + pg), DPair b d)
evalSp SwapS (DPair a b) = (dSize a + dSize b, DPair b a)
evalSp AssocS (DPair (DPair a b) c) =
  (dSize a + dSize b + dSize c, DPair a (DPair b c))
evalSp UnassocS (DPair a (DPair b c)) =
  (dSize a + (dSize b + dSize c), DPair (DPair a b) c)
evalSp ExlS (DPair a b) = (dSize a + dSize b, a)
evalSp ExrS (DPair a b) = (dSize a + dSize b, b)
evalSp WeakS v = (dSize v, DUnit)
evalSp RunitS v = (1 + dSize v, DPair v DUnit)
evalSp LunitS v = (1 + dSize v, DPair DUnit v)
evalSp InlS v = (1 + dSize v, DSum False v)
evalSp InrS v = (1 + dSize v, DSum True v)
evalSp (CaseS l _) (DSum False a) =
  let (p, c) = evalSp l a in (max (1 + dSize a) p, c)
evalSp (CaseS _ r) (DSum True b) =
  let (p, c) = evalSp r b in (max (1 + dSize b) p, c)
evalSp DistlS (DPair a (DSum False b)) =
  (dSize a + 1 + dSize b, DSum False (DPair a b))
evalSp DistlS (DPair a (DSum True c)) =
  (dSize a + 1 + dSize c, DSum True (DPair a c))
evalSp NilS _ = (1, DList [])
evalSp ConsS (DPair x (DList xs)) =
  (1 + dSize x + dSize (DList xs), DList (x : xs))
evalSp UnconsS (DList []) = (2, DSum False DUnit)
evalSp UnconsS (DList (x : xs)) =
  (1 + dSize x + dSize (DList xs), DSum True (DPair x (DList xs)))
evalSp NatOutS (DNat 0) = (2, DSum False DUnit)
evalSp NatOutS (DNat n) = (2, DSum True (DNat (n - 1)))
evalSp SucS (DNat n) = (1, DNat (n + 1))
evalSp AddS (DPair (DNat a) (DNat b)) = (2, DNat (a + b))
evalSp (ConstS k) v = (dSize v, DNat k)
evalSp DupNatS n = (2, DPair n n)
evalSp (CopyS _) v = (2 * dSize v, DPair v v)
evalSp (GuardS _ t) v =
  let (pt, r) = evalSp t v
      out = case r of
        DSum False _ -> DSum False v
        DSum True _  -> DSum True DUnit
        _            -> error "space meter: guard returned a non-verdict"
  in (max pt (1 + dSize v), out)
evalSp (CurryS _ body) v = (dSize v, DClo body v)
evalSp ApplyS (DPair f a) =
  let (pb, b) = applyClo f a
  in (max (1 + dSize a) pb, b)
evalSp MapCS (DPair f (DList xs)) =
  let (p, ys) = mapSp (applyClo f) xs in (1 + p, DList ys)
evalSp (PromoteS _) v = (dSize v, v)
evalSp (DupS _) v = (2 * dSize v, DPair v v)
evalSp (BoxS f) v = evalSp f v
evalSp (BoxValS f) v = evalSp f v
evalSp MergeS (DPair a b) = (dSize a + dSize b, DPair a b)
evalSp (MapS f) (DList xs) =
  let (p, ys) = mapSp (evalSp f) xs in (p, DList ys)
evalSp (IterS f) (DPair (DNat n) a) =
  let (p, c) = iterSp (evalSp f) n a in (1 + p, c)
evalSp (FoldS f) (DPair (DList xs) b) =
  let (p, c) = foldSp (evalSp f) xs b
  in (max (dSize (DList xs) + dSize b) p, c)
evalSp (WhileS _ t s) (DPair (DNat n) a) =
  let (p, c) = whileSp (evalSp t) (evalSp s) n a in (1 + p, c)
evalSp _ _ = error "space meter: ill-shaped value for this morphism"

-- | Peak live words of a typed run.
spacePeak :: STy a -> Morph a b -> Val a -> Natural
spacePeak sa f v = fst (evalSp f (toDVal sa v))
