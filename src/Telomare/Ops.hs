{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

-- | A conservative operation vocabulary for Telomare categories.
--
-- These classes only expose operations. They deliberately assert no category,
-- tensor, coproduct, exponential, recursion, or copying equations.
module Telomare.Ops
  ( CategoryOps (..)
  , TensorOps (..)
  , AffineOps (..)
  , SumOps (..)
  , DistributivityOps (..)
  , NatOps (..)
  , ListOps (..)
  , GuardOps (..)
  , BangOps (..)
  , NatCopyOps (..)
  , BangCopyOps (..)
  , BoundedRecursionOps (..)
  ) where

import Data.Kind (Type)
import Numeric.Natural (Natural)

import Telomare.Core
import Telomare.Surface

class CategoryOps (m :: k -> k -> Type) where
  type ObjectWitness m (a :: k) :: Type
  identityOp :: m a a
  composeOp :: m b c -> m a b -> m a c

class CategoryOps m => TensorOps (m :: k -> k -> Type) where
  type Tensor m (a :: k) (b :: k) :: k
  type TensorUnit m :: k
  tensorOp :: m a b -> m c d -> m (Tensor m a c) (Tensor m b d)
  swapOp :: m (Tensor m a b) (Tensor m b a)
  assocOp :: m (Tensor m (Tensor m a b) c) (Tensor m a (Tensor m b c))
  unassocOp :: m (Tensor m a (Tensor m b c)) (Tensor m (Tensor m a b) c)
  rightUnitOp :: m a (Tensor m a (TensorUnit m))
  leftUnitOp :: m a (Tensor m (TensorUnit m) a)

class TensorOps m => AffineOps (m :: k -> k -> Type) where
  discardLeftOp :: m (Tensor m a b) a
  discardRightOp :: m (Tensor m a b) b
  weakenOp :: m a (TensorUnit m)

class CategoryOps m => SumOps (m :: k -> k -> Type) where
  type Sum m (a :: k) (b :: k) :: k
  injectLeftOp :: m a (Sum m a b)
  injectRightOp :: m b (Sum m a b)
  caseOp :: m a c -> m b c -> m (Sum m a b) c

class (TensorOps m, SumOps m) => DistributivityOps (m :: k -> k -> Type) where
  distributeLeftOp
    :: m (Tensor m a (Sum m b c)) (Sum m (Tensor m a b) (Tensor m a c))

class (TensorOps m, SumOps m) => NatOps (m :: k -> k -> Type) where
  type NatObject m :: k
  natOutOp :: m (NatObject m) (Sum m (TensorUnit m) (NatObject m))
  successorOp :: m (NatObject m) (NatObject m)
  addOp :: m (Tensor m (NatObject m) (NatObject m)) (NatObject m)
  constantOp :: Natural -> m a (NatObject m)

class (TensorOps m, SumOps m) => ListOps (m :: k -> k -> Type) where
  type ListObject m (a :: k) :: k
  nilOp :: m (TensorUnit m) (ListObject m a)
  consOp :: m (Tensor m a (ListObject m a)) (ListObject m a)
  unconsOp
    :: m (ListObject m a)
         (Sum m (TensorUnit m) (Tensor m a (ListObject m a)))

class (TensorOps m, SumOps m) => GuardOps (m :: k -> k -> Type) where
  guardOp
    :: ObjectWitness m a
    -> m a (Sum m (TensorUnit m) (TensorUnit m))
    -> m a (Sum m a (TensorUnit m))

-- | Only the promotion and merge operations actually present in the core.
-- There is intentionally no dereliction, digging, extraction, or extension.
class TensorOps m => BangOps (m :: k -> k -> Type) where
  type BangObject m (a :: k) :: k
  boxOp :: m a b -> m (BangObject m a) (BangObject m b)
  boxValueOp :: m (TensorUnit m) b -> m (TensorUnit m) (BangObject m b)
  mergeOp
    :: m (Tensor m (BangObject m a) (BangObject m b))
         (BangObject m (Tensor m a b))

-- | The exceptional, primitive copying operation for naturals.
class (TensorOps m, NatOps m) => NatCopyOps (m :: k -> k -> Type) where
  copyNatOp :: m (NatObject m) (Tensor m (NatObject m) (NatObject m))

-- | Copying is restricted to witnessed values already under 'BangObject'.
class (TensorOps m, BangOps m) => BangCopyOps (m :: k -> k -> Type) where
  copyBangOp
    :: ObjectWitness m a
    -> m (BangObject m a) (Tensor m (BangObject m a) (BangObject m a))

class
  (TensorOps m, SumOps m, NatOps m, ListOps m, GuardOps m) =>
  BoundedRecursionOps (m :: k -> k -> Type) where
  type RecState m (a :: k) :: k
  iterateBoundedOp
    :: m a a
    -> m (Tensor m (NatObject m) (RecState m a)) (RecState m a)
  foldBoundedOp
    :: m (Tensor m b a) b
    -> m (Tensor m (ListObject m a) (RecState m b)) (RecState m b)
  whileBoundedOp
    :: ObjectWitness m a
    -> m a (Sum m (TensorUnit m) (TensorUnit m))
    -> m a a
    -> m (Tensor m (NatObject m) (RecState m a)) (RecState m a)

instance CategoryOps UMorph where
  type ObjectWitness UMorph a = SUTy a
  identityOp = UId
  composeOp = (:..:)

instance TensorOps UMorph where
  type Tensor UMorph a b = a ':**: b
  type TensorUnit UMorph = 'UUnit
  tensorOp = (:****:)
  swapOp = USwap
  assocOp = UAssoc
  unassocOp = UUnassoc
  rightUnitOp = URunit
  leftUnitOp = ULunit

instance AffineOps UMorph where
  discardLeftOp = UExl
  discardRightOp = UExr
  weakenOp = UWeak

instance SumOps UMorph where
  type Sum UMorph a b = a ':++: b
  injectLeftOp = UInl
  injectRightOp = UInr
  caseOp = UCase

instance DistributivityOps UMorph where
  distributeLeftOp = UDistl

instance NatOps UMorph where
  type NatObject UMorph = 'UNat
  natOutOp = UNatOut
  successorOp = USuc
  addOp = UAdd
  constantOp = UConst

instance ListOps UMorph where
  type ListObject UMorph a = 'UList a
  nilOp = UNil
  consOp = UCons
  unconsOp = UUncons

instance GuardOps UMorph where
  guardOp = UGuard

instance NatCopyOps UMorph where
  copyNatOp = UDup SUNat

instance BoundedRecursionOps UMorph where
  type RecState UMorph a = a
  iterateBoundedOp = UIter
  foldBoundedOp = UFold
  whileBoundedOp = UWhile

instance CategoryOps Morph where
  type ObjectWitness Morph a = STy a
  identityOp = IdS
  composeOp = (:.:)

instance TensorOps Morph where
  type Tensor Morph a b = a ':*: b
  type TensorUnit Morph = 'Unit
  tensorOp = (:***:)
  swapOp = SwapS
  assocOp = AssocS
  unassocOp = UnassocS
  rightUnitOp = RunitS
  leftUnitOp = LunitS

instance AffineOps Morph where
  discardLeftOp = ExlS
  discardRightOp = ExrS
  weakenOp = WeakS

instance SumOps Morph where
  type Sum Morph a b = a ':+: b
  injectLeftOp = InlS
  injectRightOp = InrS
  caseOp = CaseS

instance DistributivityOps Morph where
  distributeLeftOp = DistlS

instance NatOps Morph where
  type NatObject Morph = 'Nat
  natOutOp = NatOutS
  successorOp = SucS
  addOp = AddS
  constantOp = ConstS

instance ListOps Morph where
  type ListObject Morph a = 'ListT a
  nilOp = NilS
  consOp = ConsS
  unconsOp = UnconsS

instance GuardOps Morph where
  guardOp = GuardS

instance BangOps Morph where
  type BangObject Morph a = 'Bang a
  boxOp = BoxS
  boxValueOp = BoxValS
  mergeOp = MergeS

instance NatCopyOps Morph where
  copyNatOp = DupNatS

instance BangCopyOps Morph where
  copyBangOp = DupS

instance BoundedRecursionOps Morph where
  type RecState Morph a = 'Bang a
  iterateBoundedOp = IterS
  foldBoundedOp = FoldS
  whileBoundedOp = WhileS
