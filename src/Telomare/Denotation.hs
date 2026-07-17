{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}

-- | Interpretations of the core — Haskell mirror of the Agda semantics.
--
-- Sources of truth: @spec\/T3\/Sem\/Value.agda@ ('evalV'),
-- @spec\/T3\/Sem\/Graded.agda@ ('CostAlgebra', 'evalG', 'workAlg',
-- 'dupAlg'), @spec\/T3\/Sem\/Exec.agda@ ('evalK').  The Agda side proves
-- (T3.Adequacy, T3.Sem.Graded.G-val) what test\/Laws.hs re-checks here by
-- QuickCheck: value coherence, precision, adequacy.
--
-- Deviations from the spec, both deliberate and documented:
--
--   * 'CostAlgebra' specializes Agda's
--     @chargePrim : (A B : Ty) → PrimTag → ⟦A⟧T → ⟦B⟧T → ℳ@ to the
--     charges the shipped instances actually distinguish ('caNatOut',
--     'caDup', 'caDupNat', plus 'caZero' for every other leaf); the
--     size-dependent charges receive the already-computed 'sizeVal'.
--   * The space instance (@spaceAlg@, Agda @⟦_⟧SP@) is NOT mirrored yet:
--     it charges sizes at every leaf and so needs full singleton
--     threading.  The Agda spec remains its definition; the mirror lands
--     when a backend consumes it.
module Telomare.Denotation
  ( evalV
  , CostAlgebra (..)
  , evalG
  , workAlg
  , dupAlg
  , work
  , dupGrade
  , evalK
  ) where

import Control.Monad ((>=>))
import Numeric.Natural (Natural)

import Telomare.Core

-- | Value denotation (spec: @T3.Sem.Value.⟦_⟧V@) — the specification.
evalV :: Morph a b -> Val a -> Val b
evalV IdS a                 = a
evalV (g :.: f) a           = evalV g (evalV f a)
evalV (f :***: g) (a, c)    = (evalV f a, evalV g c)
evalV SwapS (a, b)          = (b, a)
evalV AssocS ((a, b), c)    = (a, (b, c))
evalV UnassocS (a, (b, c))  = ((a, b), c)
evalV ExlS (a, _)           = a
evalV ExrS (_, b)           = b
evalV WeakS _               = ()
evalV RunitS a              = (a, ())
evalV LunitS a              = ((), a)
evalV InlS a                = Left a
evalV InrS b                = Right b
evalV (CaseS l r) e         = either (evalV l) (evalV r) e
evalV DistlS (a, Left b)    = Left (a, b)
evalV DistlS (a, Right c)   = Right (a, c)
evalV NilS _                = []
evalV ConsS (x, xs)         = x : xs
evalV UnconsS []            = Left ()
evalV UnconsS (x : xs)      = Right (x, xs)
evalV NatOutS 0             = Left ()
evalV NatOutS n             = Right (n - 1)
evalV SucS n                = n + 1
evalV AddS (a, b)           = a + b
evalV (ConstS k) _          = k
evalV DupNatS n             = (n, n)
evalV (CopyS _) a           = (a, a)
evalV (GuardS _ t) a        = guardOut a (evalV t a)
evalV (DupS _) a            = (a, a)
evalV (BoxS f) a            = evalV f a
evalV (BoxValS f) a         = evalV f a
evalV MergeS p              = p
evalV (MapS f) xs           = fmap (evalV f) xs
evalV (IterS f) (n, a)      = iterV n (evalV f) a
evalV (FoldS f) (xs, b)     = foldV xs (evalV f) b
evalV (WhileS _ t s) (n, a) = whileV n (evalV t) (evalV s) a

iterV :: Natural -> (a -> a) -> a -> a
iterV 0 _ a = a
iterV n f a = iterV (n - 1) f (f a)

foldV :: [a] -> ((b, a) -> b) -> b -> b
foldV [] _ b       = b
foldV (x : xs) f b = foldV xs f (f (b, x))

whileV :: Natural -> (a -> Either () ()) -> (a -> a) -> a -> a
whileV 0 _ _ a = a
whileV n t s a = case t a of
  Left _  -> a
  Right _ -> whileV (n - 1) t s (s a)

-- | Guard output (spec: @T3.Sem.Value.guardV@): pass on 'Left', error
-- value on 'Right'.
guardOut :: v -> Either () () -> Either v ()
guardOut a (Left _)  = Left a
guardOut _ (Right _) = Right ()

-- | Cost algebra (spec: @T3.Sem.Graded.CostAlgebra@, specialized — see
-- module header).
data CostAlgebra m = CostAlgebra
  { caSeq    :: m -> m -> m          -- ^ sequential composition (Agda _⋄_)
  , caPar    :: m -> m -> m          -- ^ parallel\/tensor composition (_∥_)
  , caZero   :: m                    -- ^ charge of a plain leaf
  , caNatOut :: m                    -- ^ chargePrim natOutT
  , caDup    :: Natural -> m         -- ^ chargePrim dupT, given sizeVal
  , caDupNat :: m                    -- ^ chargePrim dupNatT
  , caStep   :: m                    -- ^ per taken loop step
  , caProbe  :: Natural -> m         -- ^ guard\/while probe, given sizeVal
  }

-- | Work (spec: @T3.Sem.Graded.workAlg@): 1 per natOut look and per taken
-- loop step, everything else free.
workAlg :: CostAlgebra Natural
workAlg = CostAlgebra
  { caSeq = (+), caPar = (+), caZero = 0, caNatOut = 1
  , caDup = const 0, caDupNat = 0, caStep = 1, caProbe = const 0
  }

-- | Dup grade (spec: @T3.Sem.Graded.dupAlg@): sizeT at dupS and at the
-- costed data copy 'CopyS' (both through 'caDup'), 1 at the atom
-- exemption, sizeT per probe (a test reads what it does not consume).
dupAlg :: CostAlgebra Natural
dupAlg = CostAlgebra
  { caSeq = (+), caPar = (+), caZero = 0, caNatOut = 0
  , caDup = id, caDupNat = 1, caStep = 0, caProbe = id
  }

-- | Graded interpretation (spec: @T3.Sem.Graded.Interp.⟦_⟧G@).  Its value
-- component equals 'evalV' — proved generically in Agda (G-val),
-- QuickChecked here (test\/Laws.hs prop_coherence).
evalG :: CostAlgebra m -> Morph a b -> Val a -> (m, Val b)
evalG alg IdS a = (caZero alg, a)
evalG alg (g :.: f) a =
  let (m, b) = evalG alg f a
      (r, c) = evalG alg g b
  in (caSeq alg m r, c)
evalG alg (f :***: g) (a, c) =
  let (m, b) = evalG alg f a
      (r, d) = evalG alg g c
  in (caPar alg m r, (b, d))
evalG alg SwapS (a, b)         = (caZero alg, (b, a))
evalG alg AssocS ((a, b), c)   = (caZero alg, (a, (b, c)))
evalG alg UnassocS (a, (b, c)) = (caZero alg, ((a, b), c))
evalG alg ExlS (a, _)          = (caZero alg, a)
evalG alg ExrS (_, b)          = (caZero alg, b)
evalG alg WeakS _              = (caZero alg, ())
evalG alg RunitS a             = (caZero alg, (a, ()))
evalG alg LunitS a             = (caZero alg, ((), a))
evalG alg InlS a               = (caZero alg, Left a)
evalG alg InrS b               = (caZero alg, Right b)
evalG alg (CaseS l _) (Left a)  = evalG alg l a
evalG alg (CaseS _ r) (Right b) = evalG alg r b
evalG alg DistlS (a, Left b)   = (caZero alg, Left (a, b))
evalG alg DistlS (a, Right c)  = (caZero alg, Right (a, c))
evalG alg NilS _               = (caZero alg, [])
evalG alg ConsS (x, xs)        = (caZero alg, x : xs)
evalG alg UnconsS []           = (caZero alg, Left ())
evalG alg UnconsS (x : xs)     = (caZero alg, Right (x, xs))
evalG alg NatOutS 0            = (caNatOut alg, Left ())
evalG alg NatOutS n            = (caNatOut alg, Right (n - 1))
evalG alg SucS n               = (caZero alg, n + 1)
evalG alg AddS (a, b)          = (caZero alg, a + b)
evalG alg (ConstS k) _         = (caZero alg, k)
evalG alg DupNatS n            = (caDupNat alg, (n, n))
evalG alg (CopyS w) a          = (caDup alg (sizeVal (copyableSTy w) a), (a, a))
evalG alg (GuardS sa t) a =
  let (mt, r) = evalG alg t a
  in (caSeq alg (caProbe alg (sizeVal sa a)) mt, guardOut a r)
evalG alg (DupS sa) a          = (caDup alg (sizeVal (SBang sa) a), (a, a))
evalG alg (BoxS f) a           = evalG alg f a
evalG alg (BoxValS f) a        = evalG alg f a
evalG alg MergeS p             = (caZero alg, p)
evalG alg (MapS f) xs          = mapG alg (evalG alg f) xs
evalG alg (IterS f) (n, a)     = iterG alg (evalG alg f) n a
evalG alg (FoldS f) (xs, b)    = foldG alg (evalG alg f) xs b
evalG alg (WhileS sa t s) (n, a) =
  whileG alg sa (evalG alg t) (evalG alg s) n a

mapG :: CostAlgebra m -> (a -> (m, b)) -> [a] -> (m, [b])
mapG alg _ [] = (caZero alg, [])
mapG alg f (x : xs) =
  let (m, y)  = f x
      (r, ys) = mapG alg f xs
  in (caSeq alg (caStep alg) (caSeq alg m r), y : ys)

iterG :: CostAlgebra m -> (a -> (m, a)) -> Natural -> a -> (m, a)
iterG alg _ 0 a = (caZero alg, a)
iterG alg f n a =
  let (m, b) = f a
      (r, c) = iterG alg f (n - 1) b
  in (caSeq alg (caStep alg) (caSeq alg m r), c)

foldG :: CostAlgebra m -> ((b, a) -> (m, b)) -> [a] -> b -> (m, b)
foldG alg _ [] b = (caZero alg, b)
foldG alg f (x : xs) b =
  let (m, b') = f (b, x)
      (r, c)  = foldG alg f xs b'
  in (caSeq alg (caStep alg) (caSeq alg m r), c)

whileG :: CostAlgebra m -> STy a -> (Val a -> (m, Either () ()))
       -> (Val a -> (m, Val a)) -> Natural -> Val a -> (m, Val a)
whileG alg _ _ _ 0 a = (caZero alg, a)
whileG alg sa t s n a =
  let (mt, r) = t a
      probe   = caProbe alg (sizeVal sa a)
  in case r of
       Left _  -> (caSeq alg probe mt, a)
       Right _ ->
         let (ms, b) = s a
             (mr, c) = whileG alg sa t s (n - 1) b
         in (caSeq alg probe
              (caSeq alg mt (caSeq alg (caStep alg) (caSeq alg ms mr))), c)

-- | Work grade (spec: @T3.Sem.Graded.work@).
work :: Morph a b -> Val a -> Natural
work f a = fst (evalG workAlg f a)

-- | Dup grade (spec: @T3.Sem.Graded.dupGrade@).
dupGrade :: Morph a b -> Val a -> Natural
dupGrade f a = fst (evalG dupAlg f a)

-- | Fuel-metered execution (spec: @T3.Sem.Exec.⟦_⟧K@): 'Nothing' = fuel
-- exhausted (never diverges).  Consumes exactly where 'workAlg' charges;
-- T3.Adequacy proves precision, test\/Laws.hs re-checks it.
evalK :: Morph a b -> Val a -> Natural -> Maybe (Val b, Natural)
evalK IdS a g                    = Just (a, g)
evalK (g :.: f) a fu             = evalK f a fu >>= uncurry (evalK g)
evalK (f :***: g) (a, c) fu      = do
  (b, fu')  <- evalK f a fu
  (d, fu'') <- evalK g c fu'
  pure ((b, d), fu'')
evalK SwapS (a, b) g             = Just ((b, a), g)
evalK AssocS ((a, b), c) g       = Just ((a, (b, c)), g)
evalK UnassocS (a, (b, c)) g     = Just (((a, b), c), g)
evalK ExlS (a, _) g              = Just (a, g)
evalK ExrS (_, b) g              = Just (b, g)
evalK WeakS _ g                  = Just ((), g)
evalK RunitS a g                 = Just ((a, ()), g)
evalK LunitS a g                 = Just (((), a), g)
evalK InlS a g                   = Just (Left a, g)
evalK InrS b g                   = Just (Right b, g)
evalK (CaseS l _) (Left a) g     = evalK l a g
evalK (CaseS _ r) (Right b) g    = evalK r b g
evalK DistlS (a, Left b) g       = Just (Left (a, b), g)
evalK DistlS (a, Right c) g      = Just (Right (a, c), g)
evalK NilS _ g                   = Just ([], g)
evalK ConsS (x, xs) g            = Just (x : xs, g)
evalK UnconsS [] g               = Just (Left (), g)
evalK UnconsS (x : xs) g         = Just (Right (x, xs), g)
evalK NatOutS n g                = stepK (\g' -> Just (out, g')) g
  where out = if n == 0 then Left () else Right (n - 1)
evalK SucS n g                   = Just (n + 1, g)
evalK AddS (a, b) g              = Just (a + b, g)
evalK (ConstS k) _ g             = Just (k, g)
evalK DupNatS n g                = Just ((n, n), g)
evalK (CopyS _) a g              = Just ((a, a), g)
evalK (GuardS _ t) a g           =
  evalK t a g >>= \(r, g') -> Just (guardOut a r, g')
evalK (DupS _) a g               = Just ((a, a), g)
evalK (BoxS f) a g               = evalK f a g
evalK (BoxValS f) a g            = evalK f a g
evalK MergeS p g                 = Just (p, g)
evalK (MapS f) xs g              = mapK (evalK f) xs g
evalK (IterS f) (n, a) g         = iterK (evalK f) n a g
evalK (FoldS f) (xs, b) g        = foldK (evalK f) xs b g
evalK (WhileS _ t s) (n, a) g    = whileK (evalK t) (evalK s) n a g

mapK :: (a -> Natural -> Maybe (b, Natural)) -> [a] -> Natural
     -> Maybe ([b], Natural)
mapK _ [] g = Just ([], g)
mapK f (x : xs) g = stepK action g
  where
    action fuel = do
      (y, fuel') <- f x fuel
      (ys, fuel'') <- mapK f xs fuel'
      pure (y : ys, fuel'')

stepK :: (Natural -> Maybe (a, Natural)) -> Natural -> Maybe (a, Natural)
stepK _ 0 = Nothing
stepK m g = m (g - 1)

iterK :: (a -> Natural -> Maybe (a, Natural)) -> Natural -> a -> Natural
      -> Maybe (a, Natural)
iterK _ 0 a g = Just (a, g)
iterK f n a g =
  stepK (f a >=> uncurry (iterK f (n - 1))) g

foldK :: ((b, a) -> Natural -> Maybe (b, Natural)) -> [a] -> b -> Natural
      -> Maybe (b, Natural)
foldK _ [] b g = Just (b, g)
foldK f (x : xs) b g =
  stepK (f (b, x) >=> uncurry (foldK f xs)) g

whileK :: (a -> Natural -> Maybe (Either () (), Natural))
       -> (a -> Natural -> Maybe (a, Natural)) -> Natural -> a -> Natural
       -> Maybe (a, Natural)
whileK _ _ 0 a g = Just (a, g)
whileK t s n a g = t a g >>= \(r, g') -> case r of
  Left _  -> Just (a, g')
  Right _ ->
    stepK (s a >=> uncurry (whileK t s (n - 1))) g'
