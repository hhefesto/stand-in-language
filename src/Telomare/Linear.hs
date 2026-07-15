{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE LinearTypes   #-}
{-# LANGUAGE RankNTypes    #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | A small linear frontend with separate direct and closed-recursion APIs.
--
-- A 'Wire' is a whole circuit, rather than a host value. Its scope parameter is
-- abstracted by 'Circuit', so wires cannot escape reification. Linear arrows
-- make consuming a locally bound wire exactly once a GHC type-checking
-- obligation. This is syntactic resource checking: unrestricted top-level
-- circuit definitions may still be referenced more than once.
module Telomare.Linear
  ( Wire
  , Circuit
  , Closed
  , Host
  , HostType (..)
  , Copy (..)
  , identity
  , (>>>)
  , tensor
  , swap
  , associate
  , unassociate
  , discard
  , discardLeft
  , discardRight
  , pairUnitRight
  , pairUnitLeft
  , injectLeft
  , injectRight
  , branch
  , distribute
  , copy
  , zeroOrPred
  , successor
  , add
  , natural
  , nil
  , cons
  , uncons
  , reify
  , compile
  , closedCore
  , closedIter
  , closedFold
  , closedWhile
  ) where

import Data.Kind (Type)
import Numeric.Natural (Natural)

import qualified Telomare.Compiler.Closed as ClosedCompiler
import Telomare.Compiler.Direct (DirectError, compileDirect)
import Telomare.Core (Morph, Ty (..))
import Telomare.Surface

-- | Telomare's representation of the supported host-shaped object language.
type family Host a :: UTy where
  Host ()         = 'UUnit
  Host Natural    = 'UNat
  Host (a, b)     = Host a ':**: Host b
  Host (Either a b) = Host a ':++: Host b
  Host [a]        = 'UList (Host a)

-- | An abstract circuit in scope @s@. The constructor is intentionally hidden.
newtype Wire (s :: Type) a b = Wire (UMorph (Host a) (Host b))

-- | A closed circuit. Rank-2 scope prevents a 'Wire' from escaping or being
-- captured by another closed circuit.
type Circuit a b = forall s. Wire s a b

-- | A placed, closed recursive result. Its constructor is hidden so a core box
-- cannot be smuggled back into the source-level 'Host' family.
newtype Closed a = Closed (Morph 'Unit ('Bang (Lift (Host a))))

-- | Runtime type evidence needed by size-aware closed while loops.
data HostType a where
  UnitType    :: HostType ()
  NaturalType :: HostType Natural
  ProductType :: HostType a -> HostType b -> HostType (a, b)
  SumType     :: HostType a -> HostType b -> HostType (Either a b)
  ListType    :: HostType a -> HostType [a]

-- | Explicit evidence for the only host shapes this frontend can copy.
data Copy a where
  CopyUnit    :: Copy ()
  CopyNatural :: Copy Natural
  CopyProduct :: Copy a -> Copy b -> Copy (a, b)

identity :: Wire s a a
identity = Wire UId

infixr 1 >>>

(>>>) :: Wire s a b %1 -> Wire s b c %1 -> Wire s a c
Wire f >>> Wire g = Wire (g :..: f)

tensor
  :: Wire s a b %1
  -> Wire s c d %1
  -> Wire s (a, c) (b, d)
tensor (Wire f) (Wire g) = Wire (f :****: g)

swap :: Wire s (a, b) (b, a)
swap = Wire USwap

associate :: Wire s ((a, b), c) (a, (b, c))
associate = Wire UAssoc

unassociate :: Wire s (a, (b, c)) ((a, b), c)
unassociate = Wire UUnassoc

-- | Explicit affine weakening.
discard :: Wire s a ()
discard = Wire UWeak

discardLeft :: Wire s (a, b) a
discardLeft = Wire UExl

discardRight :: Wire s (a, b) b
discardRight = Wire UExr

pairUnitRight :: Wire s a (a, ())
pairUnitRight = Wire URunit

pairUnitLeft :: Wire s a ((), a)
pairUnitLeft = Wire ULunit

injectLeft :: Wire s a (Either a b)
injectLeft = Wire UInl

injectRight :: Wire s b (Either a b)
injectRight = Wire UInr

-- | Eliminate a sum with closed branches. A branch cannot capture a live
-- scoped wire because it must work in every fresh scope.
branch
  :: Circuit a c %1
  -> Circuit b c %1
  -> Wire s (Either a b) c
branch (Wire l) (Wire r) = Wire (UCase l r)

distribute :: Wire s (a, Either b c) (Either (a, b) (a, c))
distribute = Wire UDistl

copy :: Copy a -> Wire s a (a, a)
copy = Wire . copyMorph

copyMorph :: Copy a -> UMorph (Host a) (Host a ':**: Host a)
copyMorph CopyUnit          = URunit
copyMorph CopyNatural       = UDup SUNat
copyMorph (CopyProduct a b) =
  UUnassoc
    :..: (UId :****: USwap)
    :..: (UId :****: UUnassoc)
    :..: UAssoc
    :..: (copyMorph a :****: copyMorph b)

zeroOrPred :: Wire s Natural (Either () Natural)
zeroOrPred = Wire UNatOut

successor :: Wire s Natural Natural
successor = Wire USuc

add :: Wire s (Natural, Natural) Natural
add = Wire UAdd

natural :: Natural -> Wire s () Natural
natural = Wire . UConst

nil :: Wire s () [a]
nil = Wire UNil

cons :: Wire s (a, [a]) [a]
cons = Wire UCons

uncons :: Wire s [a] (Either () (a, [a]))
uncons = Wire UUncons

reify :: Circuit a b -> UMorph (Host a) (Host b)
reify (Wire f) = f

compile
  :: Circuit a b
  -> Either DirectError (Morph (Lift (Host a)) (Lift (Host b)))
compile circuit = compileDirect (reify circuit)

-- | Inspect the typed decorated core result without making boxes a source type.
closedCore :: Closed a -> Morph 'Unit ('Bang (Lift (Host a)))
closedCore (Closed core) = core

-- | Place literal-bounded iteration from rank-2 closed descriptions.
closedIter
  :: Natural
  -> Circuit () a
  -> Circuit a a
  -> Circuit a c
  -> Either DirectError (Closed c)
closedIter count seed step continuation = Closed <$>
  ClosedCompiler.closedIter count (reify seed) (reify step) (reify continuation)

-- | Place a closed list fold from rank-2 closed descriptions.
closedFold
  :: Circuit () [a]
  -> Circuit () b
  -> Circuit (b, a) b
  -> Circuit b c
  -> Either DirectError (Closed c)
closedFold input seed step continuation = Closed <$>
  ClosedCompiler.closedFold
    (reify input) (reify seed) (reify step) (reify continuation)

-- | Place a literal-capped while from rank-2 closed descriptions.
closedWhile
  :: HostType a
  -> Natural
  -> Circuit () a
  -> Circuit a (Either () ())
  -> Circuit a a
  -> Circuit a c
  -> Either DirectError (Closed c)
closedWhile stateTy limit seed test step continuation = Closed <$>
  ClosedCompiler.closedWhile (hostType stateTy) limit
    (reify seed) (reify test) (reify step) (reify continuation)

hostType :: HostType a -> SUTy (Host a)
hostType UnitType          = SUUnit
hostType NaturalType       = SUNat
hostType (ProductType a b) = SUProd (hostType a) (hostType b)
hostType (SumType a b)     = SUSum (hostType a) (hostType b)
hostType (ListType a)      = SUList (hostType a)
