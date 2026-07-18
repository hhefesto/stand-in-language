{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

-- | Static work-bound vectors: the refl facts of
-- @spec\/T3\/Examples\/Bounds.agda@ transcribed 1:1 by name, plus the
-- tic-tac-toe acceptance check (a concrete certified bound exists and
-- dominates the measured work of every golden-transcript run).
module BoundVectors (boundVectors, tictactoeBoundVectors) where

import Data.Maybe (isJust, isNothing)
import Numeric.Natural (Natural)

import SpecVectors (isZero, predS)
import Telomare.Budget
import Telomare.Core
import Telomare.Denotation
import Telomare.Machine
import Telomare.Surface (SUTy (..))

double :: Morph 'Nat ('Bang 'Nat)
double = IterS (SucS :.: SucS) :.: (IdS :***: BoxValS (ConstS 0)) :.: RunitS

countDown :: Morph 'Nat ('Bang 'Nat)
countDown = WhileS SNat isZero predS :.: (IdS :***: BoxValS (ConstS 3)) :.: RunitS

applyInc :: Morph 'Nat 'Nat
applyInc = ApplyS :.: (CurryS SUnit (SucS :.: ExrS) :***: IdS) :.: LunitS

chooseOp :: Morph ('Unit ':+: 'Unit) ('Bang ('Lolly 'Nat 'Nat))
chooseOp = CaseS (BoxValS (CurryS SUnit (SucS :.: ExrS)))
                 (BoxValS (CurryS SUnit (predS :.: ExrS)))

applyChosen :: Morph ('Unit ':+: 'Unit) ('Bang 'Nat)
applyChosen =
  BoxS ApplyS :.: MergeS :.: (chooseOp :***: BoxValS (ConstS 3)) :.: RunitS

egListS :: Morph 'Unit ('ListT 'Nat)
egListS =
  ConsS :.: (ConstS 1 :***: (ConsS :.: (ConstS 2 :***: NilS) :.: LunitS))
    :.: LunitS

mapChosen :: Morph ('Unit ':+: 'Unit) ('Bang ('ListT 'Nat))
mapChosen = MapCS :.: (chooseOp :***: egListS) :.: RunitS

probe3 :: Morph 'Nat 'Nat
probe3 =
  CaseS (ConstS 0)
    (CaseS (ConstS 1)
      (CaseS (ConstS 2) (ConstS 3) :.: NatOutS)
      :.: NatOutS)
    :.: NatOutS

sumShape :: ShapeH
sumShape = SumSh (Just UnitS) (Just UnitS)

-- | (name in Examples/Bounds.agda, holds in the mirror)
boundVectors :: [(String, Bool)]
boundVectors =
  [ ("double-bound", fst (costW double (NatLE 5)) == Just 5)
  , ("double-bound-holds", work double 5 <= 5)
  , ("double-unbounded", isNothing (fst (costW double TopS)))
  , ("countDown-bound", fst (costW countDown (NatLE 5)) == Just 15)
  , ("countDown-bound-holds", work countDown 5 <= 15)
  , ("applyInc-bound", fst (costW applyInc TopS) == Just 1)
  , ("applyInc-bound-holds", work applyInc 5 <= 1)
  , ("applyChosen-bound", fst (costW applyChosen sumShape) == Just 2)
  , ("applyChosen-bound-holds-left", work applyChosen (Left ()) <= 2)
  , ("applyChosen-bound-holds-right", work applyChosen (Right ()) <= 2)
  , ("mapChosen-bound", fst (costW mapChosen sumShape) == Just 4)
  , ("mapChosen-bound-holds-left", work mapChosen (Left ()) <= 4)
  , ("mapChosen-bound-holds-right", work mapChosen (Right ()) <= 4)
  , ("probe3-bound", fst (costW probe3 TopS) == Just 3)
  , ("probe3-bound-holds", work probe3 100 <= 3)
  ]

-- | Acceptance: the compiled game has concrete certified bounds and
-- every golden-transcript run stays under them ("any step invocation
-- costs at most N work units, derived statically").
tictactoeBoundVectors :: Program -> [(String, Bool)]
tictactoeBoundVectors program@(Program _ _ _ initial step) =
  [ ("tictactoe init has a certified static work bound", isJust initBound)
  , ("tictactoe step has a certified static work bound", isJust stepBound)
  , ("tictactoe golden runs stay under the certified bounds",
      all runBounded goldenScripts)
  ]
  where
    entryBound :: CoreEntry a b -> Maybe Natural
    entryBound (CoreEntry inputTy _ _ morph) =
      fst (costW morph (shapeOfSTy inputTy))
    initBound = entryBound initial
    stepBound = entryBound step
    goldenScripts =
      [ ["1", "4", "2", "5", "3"]
      , ["q"]
      , ["x", "1", "1", "4", "2", "5", "3"]
      , ["1", "2", "3", "5", "8", "4", "6", "9", "7"]
      ]
    -- runProgramScript totals init work + per-step work; the certified
    -- per-run cap is therefore initBound + steps * stepBound.
    runBounded inputs = case (initBound, stepBound, runProgramScript program inputs) of
      (Just ib, Just sb, Right (_, spent)) ->
        spent <= ib + fromIntegral (length inputs) * sb
      _ -> False
