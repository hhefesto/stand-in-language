-- | Level-inference oracle gate (M3) + spec-mirror properties.
--
-- Frozen compatibility structural-level oracle.
--
-- > nix run . -- --emit-levels tictactoe.tel
--
-- Key facts from its output, gated below on a structural reduction of the
-- same program (tictactoePort — the call/offset skeleton of the level-
-- relevant chains, not the full game):
--
--   * max box depth (towerHeight): 3
--   * whoWon.board : !! (copied 2 levels down)
--   * main.input   : !! (copied 2 levels down)
--   * main.newBoard : ! (copied 1 level down)
--   * foldr.f : !, d2c.b : ! (step functions copied by the numeral)
--   * sites at levels 0, 1 and 2 (d2c/fixed/map chains)
--
-- PROPERTIES: the Haskell mirror of T3\/Place.agda re-checked by
-- QuickCheck (the Agda proves place-solves\/place-least\/solves-meet; the
-- mirror must not drift).
module InferOracle (oracleVectors, inferProps) where

import qualified Data.Map as Map
import Numeric.Natural (Natural)
import Test.QuickCheck

import Telomare.Infer

-- ── spec-mirror properties ──────────────────────────────────────────────────

genSkel :: Int -> Gen Skel
genSkel 0 = pure Tip
genSkel n = oneof
  [ pure Tip
  , Bin <$> sub <*> sub
  , Rec <$> sub
  , (Call . fromIntegral <$> chooseInt (0, 3)) <*> sub
  ]
  where sub = genSkel (n `div` 2)

newtype SomeSkel = SomeSkel Skel deriving Show

instance Arbitrary SomeSkel where
  arbitrary = SomeSkel <$> sized (genSkel . min 8)

-- An arbitrary solution: place with per-site upward slack (any solution
-- has this shape; slack propagates the ambient depth).
genSolution :: Natural -> Skel -> Gen Deco
genSolution _ Tip        = pure TipD
genSolution d (Bin x y)  = BinD <$> genSolution d x <*> genSolution d y
genSolution d (Rec s)    = do
  bump <- fromIntegral <$> chooseInt (0, 3)
  RecD (d + bump) <$> genSolution (d + bump + 1) s
genSolution d (Call k s) = CallD k <$> genSolution (d + k) s

-- place computes a solution (Agda: place-solves).
prop_place_solves :: Property
prop_place_solves = forAll arbitrary $ \(SomeSkel s) -> solves 0 (place 0 s)

-- place is beneath every solution (Agda: place-least).
prop_place_least :: Property
prop_place_least =
  forAll arbitrary $ \(SomeSkel s) ->
  forAll (genSolution 0 s) $ \y ->
    solves 0 y && decoLE (place 0 s) y == Just True

-- solutions are closed under pointwise meet (Agda: solves-meet).
prop_meet_solves :: Property
prop_meet_solves =
  forAll arbitrary $ \(SomeSkel s) ->
  forAll (genSolution 0 s) $ \x ->
  forAll (genSolution 0 s) $ \y ->
    fmap (solves 0) (meetD x y) == Just True

inferProps :: [(String, Property)]
inferProps =
  [ ("prop_place_solves (place-solves)", prop_place_solves)
  , ("prop_place_least (place-least)",   prop_place_least)
  , ("prop_meet_solves (solves-meet)",   prop_meet_solves)
  ]

-- ── oracle fixtures ─────────────────────────────────────────────────────────

-- Structural reduction of tictactoe.tel's level-relevant chains: each def
-- carries exactly the containment/offset structure the real one exposes
-- to the walk (d2c/fixed/map are the sized {t,s,b} sites; oneWins nests
-- dEqual inside map's step; whoWon routes board through its fold step;
-- processInput pulls its argument two levels down).
tictactoePort :: Program
tictactoePort = Map.fromList
  [ ("d2c",     Def ["b"] (RecT Leaf (Var "b") Leaf))
  , ("fixed",   Def ["g"] (RecT Leaf (Var "g") Leaf))
  , ("foldr",   Def ["f"] (App "fixed" [Var "f"]))
  , ("map",     Def ["f"] (RecT Leaf (Var "f") Leaf))
  , ("dEqual",  Def ["b"] (App "d2c" [Var "b"]))
  , ("oneWins", Def ["row"] (Node [ App "map" [App "dEqual" [Leaf]]
                                  , App "d2c" [Var "row"]]))
  , ("whoWon",  Def ["board"] (Let [("doRow", App "oneWins" [Var "board"])]
                                   (App "foldr" [Var "doRow"])))
  , ("processInput", Def ["x"] (App "d2c" [App "d2c" [Var "x"]]))
  , ("main",    Def ["input"]
      (Let [("newBoard", App "d2c" [Leaf])]
           (Node [ App "whoWon" [Var "newBoard"]
                 , App "processInput" [Var "input"]])))
  ]

-- dPow shape: a depth-3 iteration tower.
dPowPort :: Program
dPowPort = Map.fromList
  [ ("main", Def ["n"]
      (RecT Leaf (RecT Leaf (RecT Leaf (Var "n") Leaf) Leaf) Leaf))
  ]

-- pow on church literals: no sized {t,s,b} sites at all —
-- invisible to the structural pass (the documented scope divergence).
powChurchPort :: Program
powChurchPort = Map.fromList
  [ ("main", Def ["n"] (Node [Var "n", Leaf]))
  ]

ttt :: Levels
ttt = inferLevels tictactoePort

bangAt :: String -> String -> Maybe Natural
bangAt d v = Map.lookup (d, v) (lvBangs ttt)

oracleVectors :: [(String, Bool)]
oracleVectors =
  [ ("tictactoe towerHeight 3",   lvTowerHeight ttt == 3)
  , ("whoWon.board : !!",         bangAt "whoWon" "board" == Just 2)
  , ("main.input : !!",           bangAt "main" "input" == Just 2)
  , ("main.newBoard : !",         bangAt "main" "newBoard" == Just 1)
  , ("foldr.f : !",               bangAt "foldr" "f" == Just 1)
  , ("d2c.b : !",                 bangAt "d2c" "b" == Just 1)
  , ("site levels {0,1,2} reached",
       let ls = fmap snd (lvSites ttt)
       in 0 `elem` ls && 1 `elem` ls && 2 `elem` ls && maximum ls == 2)
  , ("dPow towerHeight 3",
       lvTowerHeight (inferLevels dPowPort) == 3)
  , ("dPow strata 0,1,2",
       fmap snd (lvSites (inferLevels dPowPort)) == [0, 1, 2])
  , ("pow-on-church: no sites",
       null (lvSites (inferLevels powChurchPort))
         && lvTowerHeight (inferLevels powChurchPort) == 0)
  ]
