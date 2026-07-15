{-# LANGUAGE DataKinds   #-}
{-# LANGUAGE LinearTypes #-}

module LinearVectors (linearVectors) where

import Numeric.Natural (Natural)

import Telomare.Compiler.Direct (eraseMorph, erasureMatches)
import Telomare.Core (Morph (..), STy (..), Ty (..), depth)
import Telomare.Denotation (evalV, work)
import Telomare.Linear
import Telomare.Surface (evalU, shapeU)
import Telomare.Transport (artifactNode, exportMorph)

incrementTwice :: Circuit Natural Natural
incrementTwice = successor >>> successor

copyPair :: Circuit (Natural, ((), Natural)) ((Natural, ((), Natural)), (Natural, ((), Natural)))
copyPair = copy (CopyProduct CopyNatural (CopyProduct CopyUnit CopyNatural))

sumLengthStep :: Circuit (Either Natural (Natural, [Natural])) Natural
sumLengthStep = branch identity (discard >>> natural 1)

listShape :: Circuit [Natural] (Either () (Natural, [Natural]))
listShape = uncons

list12 :: Circuit () [Natural]
list12 = pairUnitRight
  >>> tensor (natural 1)
    (pairUnitRight >>> tensor (natural 2) nil >>> cons)
  >>> cons

alwaysContinue :: Circuit Natural (Either () ())
alwaysContinue = discard >>> injectRight

closedIteration :: Either String (Closed Natural)
closedIteration = mapLeft show (closedIter 3 (natural 0) successor successor)

closedListFold :: Either String (Closed Natural)
closedListFold = mapLeft show (closedFold list12 (natural 0) add successor)

closedNaturalWhile :: Either String (Closed Natural)
closedNaturalWhile = mapLeft show
  (closedWhile NaturalType 3 (natural 0) alwaysContinue successor successor)

linearVectors :: [(String, Bool)]
linearVectors =
  [ ("linear-runtime-compose", evalU (reify incrementTwice) 4 == 6)
  , ("linear-runtime-product-copy",
      evalU (reify copyPair) (3, ((), 5)) == ((3, ((), 5)), (3, ((), 5))))
  , ("linear-runtime-sum-left", evalU (reify sumLengthStep) (Left 9) == 9)
  , ("linear-runtime-sum-right",
      evalU (reify sumLengthStep) (Right (9, [1, 2])) == 1)
  , ("linear-runtime-list", evalU (reify listShape) [4, 5] == Right (4, [5]))
  , ("linear-shape-copy-has-no-general-dup",
      erasureMatches (reify copyPair) == Right True)
  , ("linear-compile-through-direct", case compile incrementTwice of
      Left _     -> False
      Right core -> evalV core 4 == 6
        && shapeU (eraseMorph core) == shapeU (reify incrementTwice))
  ] <> closedVectors "iter" closedIteration expectedIteration 4 3
    <> closedVectors "fold" closedListFold expectedFold 4 2
    <> closedVectors "while" closedNaturalWhile expectedWhile 4 3

closedVectors
  :: String
  -> Either String (Closed Natural)
  -> Morph 'Unit ('Bang 'Nat)
  -> Natural
  -> Natural
  -> [(String, Bool)]
closedVectors name result expected value expectedWork =
  [ ("linear-closed-" <> name <> "-evalV", withCore (\core -> evalV core () == value))
  , ("linear-closed-" <> name <> "-erased-evalU",
      withCore (\core -> evalU (eraseMorph core) () == value))
  , ("linear-closed-" <> name <> "-depth", withCore ((== 1) . depth))
  , ("linear-closed-" <> name <> "-exact-work",
      withCore (\core -> work core () == expectedWork))
  , ("linear-closed-" <> name <> "-exact-shape",
      withCore (\core -> artifactNode (exportMorph SUnit (SBang SNat) core)
        == artifactNode (exportMorph SUnit (SBang SNat) expected)))
  ]
  where
    withCore predicate = case result of
      Left _       -> False
      Right closed -> predicate (closedCore closed)

expectedIteration :: Morph 'Unit ('Bang 'Nat)
expectedIteration = BoxS SucS
  :.: IterS SucS
  :.: (ConstS 3 :***: BoxValS (ConstS 0))
  :.: RunitS

expectedFold :: Morph 'Unit ('Bang 'Nat)
expectedFold = BoxS SucS
  :.: FoldS AddS
  :.: (input :***: BoxValS (ConstS 0))
  :.: RunitS
  where
    input = (ConsS
      :.: (ConstS 1 :***: ((ConsS
        :.: (ConstS 2 :***: NilS))
        :.: RunitS)))
      :.: RunitS

expectedWhile :: Morph 'Unit ('Bang 'Nat)
expectedWhile = BoxS SucS
  :.: WhileS SNat (InrS :.: WeakS) SucS
  :.: (ConstS 3 :***: BoxValS (ConstS 0))
  :.: RunitS

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
