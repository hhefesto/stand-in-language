{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

-- | Placement for recursion whose inputs, bodies, and continuations are closed.
--
-- This is the Haskell counterpart of
-- @spec/T3/Compiler/ClosedRecursion.agda@. Every 'UMorph' argument is compiled
-- by the direct compiler before the modal structure is assembled.
module Telomare.Compiler.Closed
  ( closedValue
  , affineMapValueFrom
  , affineIterValueFrom
  , affineFoldValueFrom
  , affineWhileValueFrom
  , closedIterValue
  , closedMapValue
  , closedIterValueFrom
  , closedFoldValue
  , closedWhileValue
  , closedWhileValueFrom
  , closedContinue
  , closedContinueFrom
  , closedMerge
  , closedIter
  , closedFold
  , closedWhile
  ) where

import Numeric.Natural (Natural)

import Telomare.Compiler.Direct (DirectError, compileDirect)
import Telomare.Core (Morph (..), Ty (..))
import Telomare.Surface (Lift, SUTy, UMorph (..), UTy (..), liftSTy)

-- | Empty-context promotion of a directly compilable value.
closedValue
  :: UMorph 'UUnit a
  -> Either DirectError (Morph 'Unit ('Bang (Lift a)))
closedValue value = BoxValS <$> compileDirect value

-- | Mapping an affine runtime list with a directly compiled body.
affineMapValueFrom
  :: UMorph x ('UList a)
  -> UMorph a b
  -> Either DirectError (Morph (Lift x) ('Bang ('ListT (Lift b))))
affineMapValueFrom input body = do
  inputCore <- compileDirect input
  bodyCore <- compileDirect body
  pure (MapS bodyCore :.: inputCore)

-- | Iteration with an affine runtime controller and a closed seed.
affineIterValueFrom
  :: UMorph x 'UNat
  -> UMorph 'UUnit a
  -> UMorph a a
  -> Either DirectError (Morph (Lift x) ('Bang (Lift a)))
affineIterValueFrom count seed step = do
  countCore <- compileDirect count
  seedCore <- closedValue seed
  stepCore <- compileDirect step
  pure (IterS stepCore :.: (countCore :***: seedCore) :.: RunitS)

-- | Folding an affine runtime list with a closed accumulator seed.
affineFoldValueFrom
  :: UMorph x ('UList a)
  -> UMorph 'UUnit b
  -> UMorph (b ':**: a) b
  -> Either DirectError (Morph (Lift x) ('Bang (Lift b)))
affineFoldValueFrom input seed step = do
  inputCore <- compileDirect input
  seedCore <- closedValue seed
  stepCore <- compileDirect step
  pure (FoldS stepCore :.: (inputCore :***: seedCore) :.: RunitS)

-- | Bounded while with affine runtime fuel and a closed seed.
affineWhileValueFrom
  :: SUTy a
  -> UMorph x 'UNat
  -> UMorph 'UUnit a
  -> UMorph a ('UUnit ':++: 'UUnit)
  -> UMorph a a
  -> Either DirectError (Morph (Lift x) ('Bang (Lift a)))
affineWhileValueFrom stateTy limit seed test step = do
  limitCore <- compileDirect limit
  seedCore <- closedValue seed
  testCore <- compileDirect test
  stepCore <- compileDirect step
  pure (WhileS (liftSTy stateTy) testCore stepCore
    :.: (limitCore :***: seedCore) :.: RunitS)

-- | Closed-input specialization of 'affineMapValueFrom'.
closedMapValue
  :: UMorph 'UUnit ('UList a)
  -> UMorph a b
  -> Either DirectError (Morph 'Unit ('Bang ('ListT (Lift b))))
closedMapValue = affineMapValueFrom

-- | The loop portion of @closedIterS@, before its final continuation.
closedIterValue
  :: Natural
  -> UMorph 'UUnit a
  -> UMorph a a
  -> Either DirectError (Morph 'Unit ('Bang (Lift a)))
closedIterValue count seed step = do
  closedIterValueFrom (UConst count) seed step

-- | Closed iteration whose bound is itself a directly compilable expression.
closedIterValueFrom
  :: UMorph 'UUnit 'UNat
  -> UMorph 'UUnit a
  -> UMorph a a
  -> Either DirectError (Morph 'Unit ('Bang (Lift a)))
closedIterValueFrom count seed step = do
  affineIterValueFrom count seed step

-- | The loop portion of @closedFoldS@, before its final continuation.
closedFoldValue
  :: UMorph 'UUnit ('UList a)
  -> UMorph 'UUnit b
  -> UMorph (b ':**: a) b
  -> Either DirectError (Morph 'Unit ('Bang (Lift b)))
closedFoldValue input seed step = do
  affineFoldValueFrom input seed step

-- | The loop portion of @closedWhileS@, before its final continuation.
closedWhileValue
  :: SUTy a
  -> Natural
  -> UMorph 'UUnit a
  -> UMorph a ('UUnit ':++: 'UUnit)
  -> UMorph a a
  -> Either DirectError (Morph 'Unit ('Bang (Lift a)))
closedWhileValue stateTy limit seed test step = do
  closedWhileValueFrom stateTy (UConst limit) seed test step

-- | Closed while whose fuel is itself a directly compilable expression.
closedWhileValueFrom
  :: SUTy a
  -> UMorph 'UUnit 'UNat
  -> UMorph 'UUnit a
  -> UMorph a ('UUnit ':++: 'UUnit)
  -> UMorph a a
  -> Either DirectError (Morph 'Unit ('Bang (Lift a)))
closedWhileValueFrom stateTy limit seed test step = do
  affineWhileValueFrom stateTy limit seed test step

-- | Functorially promote a directly compilable continuation over a closed box.
closedContinue
  :: UMorph a b
  -> Morph 'Unit ('Bang (Lift a))
  -> Either DirectError (Morph 'Unit ('Bang (Lift b)))
closedContinue continuation value = do
  continuationCore <- compileDirect continuation
  pure (BoxS continuationCore :.: value)

-- | Close an affine input before evaluating closed bindings and their final
-- continuation. Keeping this composition here preserves the right-associated
-- categorical translation used by whole-entry Tel2 recursion.
closedContinueFrom
  :: UMorph a b
  -> Morph x 'Unit
  -> Morph 'Unit ('Bang (Lift a))
  -> Either DirectError (Morph x ('Bang (Lift b)))
closedContinueFrom continuation closeInput value = do
  continuationCore <- compileDirect continuation
  pure (BoxS continuationCore :.: value :.: closeInput)

-- | Combine two independently closed boxed values with one 'MergeS'.
closedMerge
  :: Morph 'Unit ('Bang a)
  -> Morph 'Unit ('Bang b)
  -> Morph 'Unit ('Bang (a ':*: b))
closedMerge left right = MergeS :.: (left :***: right) :.: RunitS

-- | Directly compilable specialization of @closedIterS@.
closedIter
  :: Natural
  -> UMorph 'UUnit a
  -> UMorph a a
  -> UMorph a c
  -> Either DirectError (Morph 'Unit ('Bang (Lift c)))
closedIter count seed step continuation =
  closedIterValue count seed step >>= closedContinue continuation

-- | Directly compilable specialization of @closedFoldS@.
closedFold
  :: UMorph 'UUnit ('UList a)
  -> UMorph 'UUnit b
  -> UMorph (b ':**: a) b
  -> UMorph b c
  -> Either DirectError (Morph 'Unit ('Bang (Lift c)))
closedFold input seed step continuation =
  closedFoldValue input seed step >>= closedContinue continuation

-- | Directly compilable specialization of @closedWhileS@.
closedWhile
  :: SUTy a
  -> Natural
  -> UMorph 'UUnit a
  -> UMorph a ('UUnit ':++: 'UUnit)
  -> UMorph a a
  -> UMorph a c
  -> Either DirectError (Morph 'Unit ('Bang (Lift c)))
closedWhile stateTy limit seed test step continuation =
  closedWhileValue stateTy limit seed test step >>= closedContinue continuation
