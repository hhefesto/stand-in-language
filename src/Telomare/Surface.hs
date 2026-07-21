{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | Box-free cartesian surface category.
--
-- This is the Haskell mirror of @T3.Surface.Ty@, @T3.Surface.Syntax@, and
-- @T3.Surface.Sem@.  Agda's implicit type arguments become explicit
-- singletons only where the direct compiler needs to inspect the object:
-- general duplication, guards, and while loops.
module Telomare.Surface
  ( UTy (..)
  , UVal
  , UClosure (..)
  , SUTy (..)
  , sameSUTy
  , Lift
  , liftSTy
  , UMorph (..)
  , evalU
  , UShape (..)
  , shapeU
  ) where

import Data.Type.Equality ((:~:) (Refl))

import Numeric.Natural (Natural)

import Telomare.Core (STy (..), Ty (..))

-- | Surface objects contain no exponential.  Arrows appear box-free:
-- the core's reusable-closure bang erases.
data UTy
  = UUnit
  | UNat
  | UTy :**: UTy
  | UTy :++: UTy
  | UList UTy
  | ULolly UTy UTy

infixl 5 :**:
infixl 4 :++:

-- | Surface value denotation.  Closures are structural (code + typed
-- environment), mirroring the core's defunctionalized representation.
type family UVal (a :: UTy) where
  UVal 'UUnit        = ()
  UVal 'UNat         = Natural
  UVal (a ':**: b)   = (UVal a, UVal b)
  UVal (a ':++: b)   = Either (UVal a) (UVal b)
  UVal ('UList a)    = [UVal a]
  UVal ('ULolly a b) = UClosure a b

data UClosure (a :: UTy) (b :: UTy) where
  UClosure :: SUTy c -> UMorph (c ':**: a) b -> UVal c -> UClosure a b

-- | Runtime witness for a surface object.
data SUTy (a :: UTy) where
  SUUnit  :: SUTy 'UUnit
  SUNat   :: SUTy 'UNat
  SUProd  :: SUTy a -> SUTy b -> SUTy (a ':**: b)
  SUSum   :: SUTy a -> SUTy b -> SUTy (a ':++: b)
  SUList  :: SUTy a -> SUTy ('UList a)
  SULolly :: SUTy a -> SUTy b -> SUTy ('ULolly a b)

-- | Runtime type equality on surface witnesses.
sameSUTy :: SUTy a -> SUTy b -> Maybe (a :~: b)
sameSUTy SUUnit SUUnit = Just Refl
sameSUTy SUNat SUNat = Just Refl
sameSUTy (SUProd a b) (SUProd c d) = do
  Refl <- sameSUTy a c
  Refl <- sameSUTy b d
  pure Refl
sameSUTy (SUSum a b) (SUSum c d) = do
  Refl <- sameSUTy a c
  Refl <- sameSUTy b d
  pure Refl
sameSUTy (SUList a) (SUList b) = do Refl <- sameSUTy a b; pure Refl
sameSUTy (SULolly a b) (SULolly c d) = do
  Refl <- sameSUTy a c
  Refl <- sameSUTy b d
  pure Refl
sameSUTy _ _ = Nothing

-- | Canonical bang-free embedding of surface objects into the core.
type family Lift (a :: UTy) :: Ty where
  Lift 'UUnit        = 'Unit
  Lift 'UNat         = 'Nat
  Lift (a ':**: b)   = Lift a ':*: Lift b
  Lift (a ':++: b)   = Lift a ':+: Lift b
  Lift ('UList a)    = 'ListT (Lift a)
  Lift ('ULolly a b) = 'Lolly (Lift a) (Lift b)

liftSTy :: SUTy a -> STy (Lift a)
liftSTy SUUnit        = SUnit
liftSTy SUNat         = SNat
liftSTy (SUProd a b)  = SProd (liftSTy a) (liftSTy b)
liftSTy (SUSum a b)   = SSum (liftSTy a) (liftSTy b)
liftSTy (SUList a)    = SList (liftSTy a)
liftSTy (SULolly a b) = SLolly (liftSTy a) (liftSTy b)

-- | Surface morphisms, constructor-for-constructor with
-- @T3.Surface.Syntax._⇨U_@.
data UMorph (a :: UTy) (b :: UTy) where
  UId      :: UMorph a a
  (:..:)   :: UMorph b c -> UMorph a b -> UMorph a c
  (:****:) :: UMorph a b -> UMorph c d
           -> UMorph (a ':**: c) (b ':**: d)
  UDup     :: SUTy a -> UMorph a (a ':**: a)
  USwap    :: UMorph (a ':**: b) (b ':**: a)
  UAssoc   :: UMorph ((a ':**: b) ':**: c) (a ':**: (b ':**: c))
  UUnassoc :: UMorph (a ':**: (b ':**: c)) ((a ':**: b) ':**: c)
  UExl     :: UMorph (a ':**: b) a
  UExr     :: UMorph (a ':**: b) b
  UWeak    :: UMorph a 'UUnit
  URunit   :: UMorph a (a ':**: 'UUnit)
  ULunit   :: UMorph a ('UUnit ':**: a)
  UInl     :: UMorph a (a ':++: b)
  UInr     :: UMorph b (a ':++: b)
  UCase    :: UMorph a c -> UMorph b c -> UMorph (a ':++: b) c
  UDistl   :: UMorph (a ':**: (b ':++: c))
                     ((a ':**: b) ':++: (a ':**: c))
  UNil     :: UMorph 'UUnit ('UList a)
  UCons    :: UMorph (a ':**: 'UList a) ('UList a)
  UUncons  :: UMorph ('UList a) ('UUnit ':++: (a ':**: 'UList a))
  UNatOut  :: UMorph 'UNat ('UUnit ':++: 'UNat)
  USuc     :: UMorph 'UNat 'UNat
  UAdd     :: UMorph ('UNat ':**: 'UNat) 'UNat
  UConst   :: Natural -> UMorph a 'UNat
  -- closures (box-free typing: the core's reusable-closure bang erases)
  UCurry   :: SUTy c -> UMorph (c ':**: a) b -> UMorph c ('ULolly a b)
  UApply   :: UMorph ('ULolly a b ':**: a) b
  UMapC    :: UMorph ('ULolly a b ':**: 'UList a) ('UList b)
  UIterC   :: UMorph ('ULolly a a ':**: ('UNat ':**: a)) a
  UFoldC   :: UMorph ('ULolly (b ':**: a) b ':**: ('UList a ':**: b)) b
  UWhileC  :: SUTy a
           -> UMorph ('ULolly a ('UUnit ':++: 'UUnit)
                       ':**: ('ULolly a a ':**: ('UNat ':**: a))) a
  UGuard   :: SUTy a -> UMorph a ('UUnit ':++: 'UUnit)
           -> UMorph a (a ':++: 'UUnit)
  UMap     :: UMorph a b -> UMorph ('UList a) ('UList b)
  UIter    :: UMorph a a -> UMorph ('UNat ':**: a) a
  UFold    :: UMorph (b ':**: a) b -> UMorph ('UList a ':**: b) b
  UWhile   :: SUTy a -> UMorph a ('UUnit ':++: 'UUnit) -> UMorph a a
           -> UMorph ('UNat ':**: a) a

infixr 9 :..:
infixr 3 :****:

-- | Plain total surface semantics.
evalU :: UMorph a b -> UVal a -> UVal b
evalU UId a                           = a
evalU (g :..: f) a                    = evalU g (evalU f a)
evalU (f :****: g) (a, c)             = (evalU f a, evalU g c)
evalU (UDup _) a                      = (a, a)
evalU USwap (a, b)                    = (b, a)
evalU UAssoc ((a, b), c)              = (a, (b, c))
evalU UUnassoc (a, (b, c))            = ((a, b), c)
evalU UExl (a, _)                     = a
evalU UExr (_, b)                     = b
evalU UWeak _                         = ()
evalU URunit a                        = (a, ())
evalU ULunit a                        = ((), a)
evalU UInl a                          = Left a
evalU UInr b                          = Right b
evalU (UCase l _) (Left a)            = evalU l a
evalU (UCase _ r) (Right b)           = evalU r b
evalU UDistl (a, Left b)              = Left (a, b)
evalU UDistl (a, Right c)             = Right (a, c)
evalU UNil _                          = []
evalU UCons (x, xs)                   = x : xs
evalU UUncons []                      = Left ()
evalU UUncons (x : xs)                = Right (x, xs)
evalU UNatOut 0                       = Left ()
evalU UNatOut n                       = Right (n - 1)
evalU USuc n                          = n + 1
evalU UAdd (a, b)                     = a + b
evalU (UConst k) _                    = k
evalU (UCurry sc f) c                 = UClosure sc f c
evalU UApply (UClosure _ body env, a) = evalU body (env, a)
evalU UMapC (UClosure _ body env, xs) = fmap (\x -> evalU body (env, x)) xs
evalU UIterC (UClosure _ body env, (n, a)) =
  iterU n (\x -> evalU body (env, x)) a
evalU UFoldC (UClosure _ body env, (xs, b)) =
  foldU xs (\p -> evalU body (env, p)) b
evalU (UWhileC _) (UClosure _ tb te, (UClosure _ sb se, (n, a))) =
  whileU n (\x -> evalU tb (te, x)) (\x -> evalU sb (se, x)) a
evalU (UGuard _ t) a                  = guardU a (evalU t a)
evalU (UMap f) xs                     = fmap (evalU f) xs
evalU (UIter f) (n, a)                = iterU n (evalU f) a
evalU (UFold f) (xs, b)               = foldU xs (evalU f) b
evalU (UWhile _ t s) (n, a)           = whileU n (evalU t) (evalU s) a

guardU :: a -> Either () () -> Either a ()
guardU a (Left ())  = Left a
guardU _ (Right ()) = Right ()

iterU :: Natural -> (a -> a) -> a -> a
iterU 0 _ a = a
iterU n f a = iterU (n - 1) f (f a)

foldU :: [a] -> ((b, a) -> b) -> b -> b
foldU [] _ b       = b
foldU (x : xs) f b = foldU xs f (f (b, x))

whileU :: Natural -> (a -> Either () ()) -> (a -> a) -> a -> a
whileU 0 _ _ a = a
whileU n t s a = case t a of
  Left ()  -> a
  Right () -> whileU (n - 1) t s (s a)

-- | Untyped structural view used to compare a source term with the erasure
-- of its compiled core term.  The GADT indices still type-check both terms;
-- this view only removes existential intermediate objects from composition.
data UShape
  = ShId
  | ShComp UShape UShape
  | ShTensor UShape UShape
  | ShDup
  | ShSwap | ShAssoc | ShUnassoc | ShExl | ShExr | ShWeak | ShRunit | ShLunit
  | ShInl | ShInr | ShCase UShape UShape | ShDistl
  | ShNil | ShCons | ShUncons | ShNatOut | ShSuc | ShAdd | ShConst Natural
  | ShGuard UShape | ShMap UShape | ShIter UShape | ShFold UShape | ShWhile UShape UShape
  | ShCurry UShape | ShApply | ShMapC | ShIterC | ShFoldC | ShWhileC
  deriving (Eq, Show)

shapeU :: UMorph a b -> UShape
shapeU UId            = ShId
shapeU (g :..: f)     = ShComp (shapeU g) (shapeU f)
shapeU (f :****: g)   = ShTensor (shapeU f) (shapeU g)
shapeU (UDup _)       = ShDup
shapeU USwap          = ShSwap
shapeU UAssoc         = ShAssoc
shapeU UUnassoc       = ShUnassoc
shapeU UExl           = ShExl
shapeU UExr           = ShExr
shapeU UWeak          = ShWeak
shapeU URunit         = ShRunit
shapeU ULunit         = ShLunit
shapeU UInl           = ShInl
shapeU UInr           = ShInr
shapeU (UCase l r)    = ShCase (shapeU l) (shapeU r)
shapeU UDistl         = ShDistl
shapeU UNil           = ShNil
shapeU UCons          = ShCons
shapeU UUncons        = ShUncons
shapeU UNatOut        = ShNatOut
shapeU USuc           = ShSuc
shapeU UAdd           = ShAdd
shapeU (UConst k)     = ShConst k
shapeU (UCurry _ f)   = ShCurry (shapeU f)
shapeU UApply         = ShApply
shapeU UMapC          = ShMapC
shapeU UIterC         = ShIterC
shapeU UFoldC         = ShFoldC
shapeU (UWhileC _)    = ShWhileC
shapeU (UGuard _ t)   = ShGuard (shapeU t)
shapeU (UMap f)       = ShMap (shapeU f)
shapeU (UIter f)      = ShIter (shapeU f)
shapeU (UFold f)      = ShFold (shapeU f)
shapeU (UWhile _ t s) = ShWhile (shapeU t) (shapeU s)
