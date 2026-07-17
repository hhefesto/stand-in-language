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

copyList :: Morph ('ListT 'Nat) ('ListT 'Nat ':*: 'ListT 'Nat)
copyList = CopyS (CopyList CopyNat)

sumBoth :: Morph ('ListT 'Nat) ('Bang 'Nat ':*: 'Bang 'Nat)
sumBoth = (sumList :***: sumList) :.: CopyS (CopyList CopyNat)

twoLevels :: Morph 'Unit ('Bang ('Bang 'Nat))
twoLevels = BoxValS (BoxValS (ConstS 7))

isZero :: Morph 'Nat ('Unit ':+: 'Unit)
isZero = CaseS InlS (InrS :.: WeakS) :.: NatOutS

incLolly :: Morph 'Unit ('Lolly 'Nat 'Nat)
incLolly = CurryS SUnit (SucS :.: ExrS)

applyInc :: Morph 'Nat 'Nat
applyInc = ApplyS :.: (incLolly :***: IdS) :.: LunitS

chooseOp :: Morph ('Unit ':+: 'Unit) ('Bang ('Lolly 'Nat 'Nat))
chooseOp = CaseS (BoxValS incLolly) (BoxValS (CurryS SUnit (predS :.: ExrS)))

applyChosen :: Morph ('Unit ':+: 'Unit) ('Bang 'Nat)
applyChosen =
  BoxS ApplyS :.: MergeS :.: (chooseOp :***: BoxValS (ConstS 3)) :.: RunitS

egListS :: Morph 'Unit ('ListT 'Nat)
egListS =
  ConsS :.: (ConstS 1 :***: (ConsS :.: (ConstS 2 :***: NilS) :.: LunitS))
    :.: LunitS

mapChosen :: Morph ('Unit ':+: 'Unit) ('Bang ('ListT 'Nat))
mapChosen = MapCS :.: (chooseOp :***: egListS) :.: RunitS

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
  , ("copyList-val",       evalV copyList egList == (egList, egList))
  , ("copyList-cost",      work copyList egList == 0)
  , ("copyList-dup",       dupGrade copyList egList == 7)
  , ("copyList-depth",     depth copyList == 0)
  , ("sumBoth-val",        evalV sumBoth egList == (6, 6))
  , ("sumBoth-cost",       work sumBoth egList == 6)
  , ("sumBoth-dup",        dupGrade sumBoth egList == 7)
  , ("sumBoth-adequate",   evalK sumBoth egList 6 == Just ((6, 6), 0))
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
  , ("applyInc-val",       evalV applyInc 5 == 6)
  , ("applyInc-cost",      work applyInc 5 == 1)
  , ("applyInc-dup",       dupGrade applyInc 5 == 0)
  , ("applyInc-depth",     depth applyInc == 0)
  , ("applyInc-adequate",  evalK applyInc 5 1 == Just (6, 0))
  , ("applyChosen-left",   evalV applyChosen (Left ()) == 4)
  , ("applyChosen-right",  evalV applyChosen (Right ()) == 2)
  , ("applyChosen-depth",  depth applyChosen == 1)
  , ("mapChosen-left",     evalV mapChosen (Left ()) == [2, 3])
  , ("mapChosen-right",    evalV mapChosen (Right ()) == [0, 1])
  , ("mapChosen-cost-left",  work mapChosen (Left ()) == 2)
  , ("mapChosen-cost-right", work mapChosen (Right ()) == 4)
  , ("mapChosen-depth",    depth mapChosen == 1)
  ]
