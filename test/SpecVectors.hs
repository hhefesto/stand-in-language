{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

-- | Spec vectors: every refl equation of
-- @spec\/T3\/Examples\/Basics.agda@, transcribed 1:1 by name.
-- The Agda side is the ground truth (checked by @checks.telomare-spec@);
-- a changed example breaks that check, and its twin here breaks
-- @cabal test telomare-test@ — the sync convention that keeps mirror and spec
-- paired.
module SpecVectors (specVectors, isZero, predS) where

import Telomare.Core
import Telomare.Denotation

double :: Morph 'Nat ('Bang 'Nat)
double = IterS (SucS :.: SucS) :.: (IdS :***: BoxValS (ConstS 0)) :.: RunitS

addTwice :: Morph 'Nat 'Nat
addTwice = AddS :.: DupNatS

sumList :: Morph ('ListT 'Nat) ('Bang 'Nat)
sumList = FoldS AddS :.: (IdS :***: BoxValS (ConstS 0)) :.: RunitS

incrementAll :: Morph ('ListT 'Nat) ('Bang ('ListT 'Nat))
incrementAll = MapS SucS

egList :: [Natural']
egList = [1, 2, 3]

type Natural' = Val 'Nat

sumTwice :: Morph ('ListT 'Nat) ('Bang 'Nat)
sumTwice = BoxS AddS :.: MergeS :.: DupS SNat :.: sumList

twoLevels :: Morph 'Unit ('Bang ('Bang 'Nat))
twoLevels = BoxValS (BoxValS (ConstS 7))

isZero :: Morph 'Nat ('Unit ':+: 'Unit)
isZero = CaseS InlS (InrS :.: WeakS) :.: NatOutS

predS :: Morph 'Nat 'Nat
predS = CaseS (ConstS 0) IdS :.: NatOutS

countDown :: Morph 'Nat ('Bang 'Nat)
countDown = WhileS SNat isZero predS :.: (IdS :***: BoxValS (ConstS 3)) :.: RunitS

isPositive :: Morph 'Nat ('Unit ':+: 'Unit)
isPositive = CaseS InrS (InlS :.: WeakS) :.: NatOutS

positive :: Morph 'Nat ('Nat ':+: 'Unit)
positive = GuardS SNat isPositive

-- | (name in Examples.agda, holds in the mirror)
specVectors :: [(String, Bool)]
specVectors =
  [ ("double-val",         evalV double 5 == 10)
  , ("double-cost",        work double 5 == 5)
  , ("double-dup",         dupGrade double 5 == 0)
  , ("double-depth",       depth double == 1)
  , ("double-adequate",    evalK double 5 5 == Just (10, 0))
  , ("addTwice-val",       evalV addTwice 5 == 10)
  , ("addTwice-dup",       dupGrade addTwice 5 == 1)
  , ("map-val",            evalV incrementAll egList == [2, 3, 4])
  , ("map-cost",           work incrementAll egList == 3)
  , ("map-dup",            dupGrade incrementAll egList == 0)
  , ("map-depth",          depth incrementAll == 1)
  , ("map-adequate",       evalK incrementAll egList 3 == Just ([2, 3, 4], 0))
  , ("sumList-val",        evalV sumList egList == 6)
  , ("sumList-cost",       work sumList egList == 3)
  , ("sumList-dup",        dupGrade sumList egList == 0)
  , ("sumTwice-val",       evalV sumTwice egList == 12)
  , ("sumTwice-dup",       dupGrade sumTwice egList == 1)
  , ("twoLevels-depth",    towerHeight twoLevels == 2)
  , ("countDown-val",      evalV countDown 5 == 0)
  , ("countDown-cost",     work countDown 5 == 10)
  , ("countDown-dup",      dupGrade countDown 5 == 4)
  , ("countDown-depth",    depth countDown == 1)
  , ("countDown-adequate", evalK countDown 5 10 == Just (0, 0))
  , ("countDown-fuel",     evalV countDown 2 == 1)
  , ("positive-pass",      evalV positive 5 == Left 5)
  , ("positive-fail",      evalV positive 0 == Right ())
  , ("positive-cost",      work positive 5 == 1)
  , ("positive-dup",       dupGrade positive 5 == 1)
  , ("positive-adequate",  evalK positive 5 1 == Just (Left 5, 0))
  ]
