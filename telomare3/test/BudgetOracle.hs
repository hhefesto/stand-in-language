{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

-- | M4 budget vectors: every refl equation of
-- @spec\/T3\/Examples\/Budgets.agda@, transcribed 1:1 by name, plus the
-- churchK oracle mapping (VALIDATION.md: telomare1 k = semantic bound + 2):
-- dPow-shape bounds (3,6) ↦ churchK (5,8); whoWon strata (8,3) ↦ (10,5);
-- church-literal arithmetic has no fuel-carrying sites.
module BudgetOracle (budgetVectors) where

import Telomare3.Budget
import Telomare3.Core

double :: Morph 'Nat ('Bang 'Nat)
double = IterS (SucS :.: SucS) :.: (IdS :***: BoxValS (ConstS 0)) :.: RunitS

towerStep :: Morph ('Nat ':*: 'Bang 'Nat) ('Nat ':*: 'Bang 'Nat)
towerStep = (SucS :***: IterS SucS) :.: AssocS :.: (DupNatS :***: IdS)

tower :: Morph ('Nat ':*: 'Bang ('Nat ':*: 'Bang 'Nat))
               ('Bang ('Nat ':*: 'Bang 'Nat))
tower = IterS towerStep

prod :: Morph 'Nat 'Nat
prod = AddS :.: DupNatS

consumerAfterProducer :: Morph ('Nat ':*: 'Bang 'Nat) ('Bang 'Nat)
consumerAfterProducer = IterS SucS :.: (prod :***: IdS)

rowStep :: Morph ('Bang 'Nat ':*: 'ListT 'Nat) ('Bang 'Nat)
rowStep = FoldS AddS :.: SwapS

whoWonish :: Morph ('ListT ('ListT 'Nat) ':*: 'Bang ('Bang 'Nat))
                   ('Bang ('Bang 'Nat))
whoWonish = FoldS rowStep

churchArith :: Morph 'Nat 'Nat
churchArith = AddS :.: DupNatS :.: SucS

budgetVectors :: [(String, Bool)]
budgetVectors =
  [ ("double-budget",
      fst (transferB double (NatLE 5))
      == BinT (RecT (Just 5) (BinT TipT TipT))
              (BinT (BinT TipT TipT) TipT))
  , ("double-shape",
      snd (transferB double (NatLE 5)) == BangSh (NatLE 10))
  , ("tower-depth", depth tower == 2)
  , ("tower-budget (S2: inner = max over outer; churchK 5,8)",
      fst (transferB tower
            (PairSh (NatLE 3) (BangSh (PairSh (NatLE 4) (BangSh (NatLE 0))))))
      == RecT (Just 3)
           (BinT (BinT TipT (RecT (Just 6) TipT))
                 (BinT TipT (BinT TipT TipT))))
  , ("s3-budget (producer sized before consumer)",
      fst (transferB consumerAfterProducer
            (PairSh (NatLE 3) (BangSh (NatLE 0))))
      == BinT (RecT (Just 6) TipT) (BinT (BinT TipT TipT) TipT))
  , ("whoWonish-depth", depth whoWonish == 2)
  , ("whoWonish-budget (strata 8,3; churchK 10,5)",
      fst (transferB whoWonish
            (PairSh (ListSh 8 (ListSh 3 (NatLE 2)))
                    (BangSh (BangSh (NatLE 0)))))
      == RecT (Just 8) (BinT (RecT (Just 3) TipT) TipT))
  , ("churchArith-budget (no sites)",
      fst (transferB churchArith (NatLE 7))
      == BinT TipT (BinT TipT TipT))
  , ("unsizable-budget (⊤ notice, not rejection)",
      fst (transferB (IterS SucS) (TopS :: ShapeH))
      == RecT Nothing TipT)
  ]
