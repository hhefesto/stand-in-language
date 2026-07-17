{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | Telomare 3 core category — Haskell mirror of the Agda specification.
--
-- Source of truth: @spec\/T3\/Core\/Ty.agda@ (objects) and
-- @spec\/T3\/Core\/Syntax.agda@ (morphisms).  This module is a
-- constructor-for-constructor mirror; every deviation is noted where it
-- occurs.  The one systematic deviation: Agda's implicit type arguments
-- become explicit 'STy' singletons on exactly the constructors whose
-- /grading/ inspects the type ('DupS', 'GuardS', 'WhileS' — the
-- size-charged ones); everywhere else the type index alone suffices.
module Telomare.Core
  ( Ty (..)
  , Val
  , Closure (..)
  , STy (..)
  , sameSTy
  , sizeVal
  , Copyable (..)
  , copyableSTy
  , Morph (..)
  , depth
  , towerHeight
  , telomareVersion
  ) where

import Data.Type.Equality ((:~:) (Refl))
import Numeric.Natural (Natural)

-- | Version string reported by the @telomare@ executable.
telomareVersion :: String
telomareVersion = "telomare 0.1.0.0"

-- | Objects (spec: @T3.Core.Ty.Ty@).  Promoted to a kind; 'Bang' is the
-- EAL exponential @!_@.
data Ty
  = Unit
  | Nat
  | Ty :*: Ty
  | Ty :+: Ty
  | ListT Ty
  | Bang Ty
  | Lolly Ty Ty

infixl 5 :*:
infixl 4 :+:

-- | Value denotation (spec: @T3.Core.Ty.⟦_⟧T@).  Values do not see boxes:
-- @Val ('Bang' a) = Val a@ — the load-bearing clause.
--
-- Deviation from the spec, deliberate and central: Agda denotes
-- @A ⊸ B@ by the semantic function space; the Haskell mirror
-- DEFUNCTIONALIZES it as a structural 'Closure' — code identity plus a
-- typed environment — because closures must serialize through transport,
-- compare structurally in the evaluator-agreement checks, and validate
-- independently.  One structural closure serves all three evaluators
-- (value, graded, fuel) by re-running its carried syntax.
type family Val (a :: Ty) where
  Val 'Unit        = ()
  Val 'Nat         = Natural
  Val (a ':*: b)   = (Val a, Val b)
  Val (a ':+: b)   = Either (Val a) (Val b)
  Val ('ListT a)   = [Val a]
  Val ('Bang a)    = Val a
  Val ('Lolly a b) = Closure a b

-- | A first-class closure value: environment witness, body syntax, and
-- the captured environment.  Never an opaque Haskell function.
data Closure (a :: Ty) (b :: Ty) where
  Closure :: STy c -> Morph (c ':*: a) b -> Val c -> Closure a b

-- | Type singleton: Agda pattern-matches on types directly ('sizeT');
-- Haskell needs the runtime witness.
data STy (a :: Ty) where
  SUnit  :: STy 'Unit
  SNat   :: STy 'Nat
  SProd  :: STy a -> STy b -> STy (a ':*: b)
  SSum   :: STy a -> STy b -> STy (a ':+: b)
  SList  :: STy a -> STy ('ListT a)
  SBang  :: STy a -> STy ('Bang a)
  SLolly :: STy a -> STy b -> STy ('Lolly a b)

-- | Runtime type equality on core witnesses.
sameSTy :: STy a -> STy b -> Maybe (a :~: b)
sameSTy SUnit SUnit = Just Refl
sameSTy SNat SNat = Just Refl
sameSTy (SProd a b) (SProd c d) = do
  Refl <- sameSTy a c
  Refl <- sameSTy b d
  pure Refl
sameSTy (SSum a b) (SSum c d) = do
  Refl <- sameSTy a c
  Refl <- sameSTy b d
  pure Refl
sameSTy (SList a) (SList b) = do Refl <- sameSTy a b; pure Refl
sameSTy (SBang a) (SBang b) = do Refl <- sameSTy a b; pure Refl
sameSTy (SLolly a b) (SLolly c d) = do
  Refl <- sameSTy a c
  Refl <- sameSTy b d
  pure Refl
sameSTy _ _ = Nothing

-- | Word model of value size (spec: @T3.Core.Ty.sizeT@).
sizeVal :: STy a -> Val a -> Natural
sizeVal SUnit       _         = 1
sizeVal SNat        _         = 1
sizeVal (SProd s t) (a, b)    = sizeVal s a + sizeVal t b
sizeVal (SSum s _)  (Left a)  = 1 + sizeVal s a
sizeVal (SSum _ t)  (Right b) = 1 + sizeVal t b
sizeVal (SList _)   []        = 1
sizeVal (SList s)   (x : xs)  = 1 + sizeVal s x + sizeVal (SList s) xs
sizeVal (SBang s)   a         = sizeVal s a
sizeVal (SLolly _ _) _        = 1
  -- Pointer model.  Exact where duplication is actually possible: only
  -- CLOSED closures are promotable/duplicable, and a closed-closure
  -- duplicate is one code pointer (design/CLOSURES.md; revisit at R3).

-- | Structural copy evidence (spec: @T3.Core.Ty.Copyable@): which types
-- admit the costed data copy 'CopyS', charged 'sizeVal' by the dup grade.
-- Every first-order data type is copyable — deliberately.  The witness
-- stays evidence-indexed (rather than collapsing into 'STy') because
-- future non-data objects (closures) must NOT be copyable: duplicating
-- suspended computation goes through the 'Bang' modality, never 'CopyS'.
data Copyable a where
  CopyUnit :: Copyable 'Unit
  CopyNat  :: Copyable 'Nat
  CopyProd :: Copyable a -> Copyable b -> Copyable (a ':*: b)
  CopySum  :: Copyable a -> Copyable b -> Copyable (a ':+: b)
  CopyList :: Copyable a -> Copyable ('ListT a)
  CopyBang :: STy a -> Copyable ('Bang a)

-- | The singleton a witness copies at (grading needs it for 'sizeVal').
copyableSTy :: Copyable a -> STy a
copyableSTy CopyUnit       = SUnit
copyableSTy CopyNat        = SNat
copyableSTy (CopyProd a b) = SProd (copyableSTy a) (copyableSTy b)
copyableSTy (CopySum a b)  = SSum (copyableSTy a) (copyableSTy b)
copyableSTy (CopyList a)   = SList (copyableSTy a)
copyableSTy (CopyBang a)   = SBang a

-- | Morphisms (spec: @T3.Core.Syntax._⇨_@), same constructor set and
-- typing discipline: affinity is the default costing discipline, not a
-- prohibition — contraction of first-order data is legal wherever it is
-- priced ('CopyS', charged 'sizeVal' by the dup grade); EAL exponential =
-- 'DupS'\/'BoxS'\/'BoxValS'\/'MergeS' and nothing else (no dereliction,
-- no digging), recursion only as fuel-carrying 'IterS'\/'FoldS'\/'WhileS'
-- whose output lives one box level deeper.  'BoxValS' is empty-context
-- promotion only (the formal soundness discovery).
data Morph (a :: Ty) (b :: Ty) where
  IdS      :: Morph a a
  (:.:)    :: Morph b c -> Morph a b -> Morph a c
  (:***:)  :: Morph a b -> Morph c d -> Morph (a ':*: c) (b ':*: d)
  SwapS    :: Morph (a ':*: b) (b ':*: a)
  AssocS   :: Morph ((a ':*: b) ':*: c) (a ':*: (b ':*: c))
  UnassocS :: Morph (a ':*: (b ':*: c)) ((a ':*: b) ':*: c)
  ExlS     :: Morph (a ':*: b) a
  ExrS     :: Morph (a ':*: b) b
  WeakS    :: Morph a 'Unit
  RunitS   :: Morph a (a ':*: 'Unit)
  LunitS   :: Morph a ('Unit ':*: a)
  InlS     :: Morph a (a ':+: b)
  InrS     :: Morph b (a ':+: b)
  CaseS    :: Morph a c -> Morph b c -> Morph (a ':+: b) c
  DistlS   :: Morph (a ':*: (b ':+: c)) ((a ':*: b) ':+: (a ':*: c))
  NilS     :: Morph 'Unit ('ListT a)
  ConsS    :: Morph (a ':*: 'ListT a) ('ListT a)
  UnconsS  :: Morph ('ListT a) ('Unit ':+: (a ':*: 'ListT a))
  NatOutS  :: Morph 'Nat ('Unit ':+: 'Nat)
  SucS     :: Morph 'Nat 'Nat
  AddS     :: Morph ('Nat ':*: 'Nat) 'Nat
  ConstS   :: Natural -> Morph a 'Nat
  DupNatS  :: Morph 'Nat ('Nat ':*: 'Nat)
  CopyS    :: Copyable a -> Morph a (a ':*: a)
  -- closures: affine first-class functions.  A bare @Lolly a b@ is
  -- applied at most once; a REUSABLE closure is @Bang (Lolly a b)@,
  -- formed only by 'BoxValS' empty-context promotion of a closed closure
  -- and duplicated only by 'DupS'.  'MapCS' applies one reusable closure
  -- per element, one level down.  'CurryS' carries the environment
  -- witness because closure values compare structurally and export
  -- through transport.
  CurryS   :: STy c -> Morph (c ':*: a) b -> Morph c ('Lolly a b)
  ApplyS   :: Morph ('Lolly a b ':*: a) b
  MapCS    :: Morph ('Bang ('Lolly a b) ':*: 'ListT a) ('Bang ('ListT b))
  GuardS   :: STy a -> Morph a ('Unit ':+: 'Unit) -> Morph a (a ':+: 'Unit)
  DupS     :: STy a -> Morph ('Bang a) ('Bang a ':*: 'Bang a)
  BoxS     :: Morph a b -> Morph ('Bang a) ('Bang b)
  BoxValS  :: Morph 'Unit b -> Morph 'Unit ('Bang b)
  MergeS   :: Morph ('Bang a ':*: 'Bang b) ('Bang (a ':*: b))
  MapS     :: Morph a b -> Morph ('ListT a) ('Bang ('ListT b))
  IterS    :: Morph a a -> Morph ('Nat ':*: 'Bang a) ('Bang a)
  FoldS    :: Morph (b ':*: a) b -> Morph ('ListT a ':*: 'Bang b) ('Bang b)
  WhileS   :: STy a -> Morph a ('Unit ':+: 'Unit) -> Morph a a
           -> Morph ('Nat ':*: 'Bang a) ('Bang a)

infixr 9 :.:
infixr 3 :***:

-- | Box depth (spec: @T3.Core.Syntax.depth@): the static number whose
-- fixedness is both theorems.  Loop bodies and promotions add one.
depth :: Morph a b -> Natural
depth IdS            = 0
depth (g :.: f)      = max (depth g) (depth f)
depth (f :***: g)    = max (depth f) (depth g)
depth SwapS          = 0
depth AssocS         = 0
depth UnassocS       = 0
depth ExlS           = 0
depth ExrS           = 0
depth WeakS          = 0
depth RunitS         = 0
depth LunitS         = 0
depth InlS           = 0
depth InrS           = 0
depth (CaseS l r)    = max (depth l) (depth r)
depth DistlS         = 0
depth NilS           = 0
depth ConsS          = 0
depth UnconsS        = 0
depth NatOutS        = 0
depth SucS           = 0
depth AddS           = 0
depth (ConstS _)     = 0
depth DupNatS        = 0
depth (CopyS _)      = 0
depth (CurryS _ f)   = depth f
  -- level-preserving: the body runs at the apply site's level, and
  -- linearity keeps that at the curry site's level
depth ApplyS         = 0
depth MapCS          = 1
  -- the closure body runs one level down, like every recursion body
depth (GuardS _ t)   = depth t
depth (DupS _)       = 0
depth (BoxS f)       = 1 + depth f
depth (BoxValS f)    = 1 + depth f
depth MergeS         = 0
depth (MapS f)       = 1 + depth f
depth (IterS f)      = 1 + depth f
depth (FoldS f)      = 1 + depth f
depth (WhileS _ t s) = 1 + max (depth t) (depth s)

-- | Coarse cost report (spec: @T3.Core.Syntax.towerHeight@).
towerHeight :: Morph a b -> Natural
towerHeight = depth
