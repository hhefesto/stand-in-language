{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}

-- | Hand-computed live-heap peaks for the space meter (mirror of
-- @spec\/T3\/Sem\/Space.agda@) and static-dominates-dynamic checks for
-- the certified bound's Haskell mirror (@T3.SpaceBound.spaceS@ /
-- 'costSp').
module SpaceVectors (spaceVectors) where

import Numeric.Natural (Natural)

import Telomare.Budget (ShapeH (..), costSp)
import Telomare.Core
import Telomare.Space (evalSp, spacePeak, toDVal)

spaceVectors :: [(String, Bool)]
spaceVectors =
  [ ("space copy of a Nat peaks at both copies",
      spacePeak SNat (CopyS CopyNat) 7 == 2)
  , ("space map retains the tail and the produced prefix",
      -- the spaceAlg counter-example (design/SPACE.md): mapping suc over
      -- [1,2,3] peaks at tail [2,3] (5 words) live beside the body (1),
      -- Θ(n) where any per-leaf algebra reports a constant
      spacePeak (SList SNat) (MapS SucS) [1, 2, 3] == 6)
  , ("space fold retains the un-consumed tail",
      -- fold add over [1,2,3] from 0: entry (list 7 + acc 1) dominates
      spacePeak (SProd (SList SNat) (SBang SNat)) (FoldS AddS) ([1, 2, 3], 0)
        == 8)
  , ("space tensor charges the co-live sibling",
      -- (suc *** id) on (1, [1,1]): sibling list (5) + body peak (1)
      spacePeak (SProd SNat (SList SNat)) (SucS :***: IdS) (3, [1, 1]) == 6)
  , ("space sequential stages reuse memory",
      spacePeak SNat (SucS :.: SucS) 4 == 1)
  , ("static space bound dominates the measured peak on add",
      dominates (SProd SNat SNat) AddS (PairSh (NatLE 9) (NatLE 9)) (4, 5))
  , ("static space bound dominates the measured peak on copy",
      dominates SNat (CopyS CopyNat) (NatLE 9) 6)
  , ("static space bound dominates the measured peak on a fold",
      dominates (SProd (SList SNat) (SBang SNat)) (FoldS AddS)
        (PairSh (ListSh 3 (NatLE 9)) (BangSh (NatLE 9))) ([1, 2, 3], 0))
  ]

dominates :: STy a -> Morph a b -> ShapeH -> Val a -> Bool
dominates sa f shape v = case fst (costSp f shape) of
  Nothing    -> True
  Just bound -> fst (evalSp f (toDVal sa v)) <= bound
