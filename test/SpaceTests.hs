{-# LANGUAGE LambdaCase #-}

-- |Hand-computed live-heap peaks, on terms small enough to trace against the
-- machine by hand. Each figure here was derived on paper from the sweep
-- discipline in `Telomare.Eval.Space` before it was asserted; a change that
-- moves one of them is a change to what "live" means and deserves the same
-- scrutiny as a changed step count.
module SpaceTests where

import Control.Monad (forM_, unless)
import Data.Char (ord)
import Data.Functor.Foldable (cata, project)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Numeric.Natural (Natural)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

import ConformanceTests (corpus)
import SizingTests (loadWith)

import Telomare.Driver (compileModules)
import Telomare.Eval.Meter (Meter (..), evalMeter)
import Telomare.Eval.Space (SpaceMeter (..), SweepPolicy (..), evalSpace)
import Telomare.IR.Base
import Telomare.IR.Core (CompiledExpr)
import Telomare.Machine (appB, deferB)
import Telomare.Size (SizingReport (..))
import Telomare.Space.Static (StaticSpaceFailure (..), StaticSpaceStats (..),
                              defaultStaticSpaceFuel, evalSpaceStatic')
import Telomare.SpaceBound

measure :: SweepPolicy -> CompiledExpr -> SpaceMeter
measure policy = fst . evalSpace policy

-- |A unary number as data: 2n+1 cells.
unary :: Int -> CompiledExpr
unary 0 = ZeroB
unary n = PairB (unary (n - 1)) ZeroB

spaceSpec :: Spec
spaceSpec = describe "the live-heap peak" $ do
  it "counts a literal pair as its three cells" $ do
    let m = measure SweepEveryAlloc (PairB ZeroB ZeroB)
    spPeakLower m `shouldBe` 3
    spPeakUpper m `shouldBe` 3
    spSteps m `shouldBe` 3
    spBuilt m `shouldBe` 1

  it "counts a shared environment once, not once per reference" $ do
    -- \x -> (x, x) applied to a three-cell pair. A tree count of the result
    -- reads 7 nodes; the run's peak is 5 cells (the argument pair, its two
    -- zeros, the function cell, and the application pair), because both
    -- references resolve to the argument's one allocation.
    let f = deferB (toEnum 1) (PairB EnvB EnvB)
        arg = PairB ZeroB ZeroB
        m = measure SweepEveryAlloc (SetEnvB (PairB f arg))
    spPeakLower m `shouldBe` 5
    spPeakUpper m `shouldBe` 5

  it "sees a transient the result does not keep" $ do
    -- @right (n, 0)@ returns a single cell, but the run held the number
    -- while the projection waited: its 2n+1 cells, the zero, and the pair.
    -- The peak growing with n is what a size-of-the-result figure — or a
    -- retention-blind cost algebra — would have missed.
    let transientPeak n =
          spPeakLower (measure SweepEveryAlloc (RightB (PairB (unary n) ZeroB)))
    transientPeak 10 `shouldBe` 2 * 10 + 3
    transientPeak 200 - transientPeak 100 `shouldBe` 200

  it "the adaptive sweep brackets the exact peak" $ do
    let expr = RightB (PairB (unary 5000) ZeroB)
        exact = measure SweepEveryAlloc expr
        adaptive = measure SweepAdaptive expr
    -- Same run, different measuring cadence.
    spSteps adaptive `shouldBe` spSteps exact
    spBuilt adaptive `shouldBe` spBuilt exact
    spPeakLower adaptive `shouldSatisfy` (> 0)
    spPeakLower adaptive `shouldSatisfy` (<= spPeakLower exact)
    spPeakUpper adaptive `shouldSatisfy` (>= spPeakUpper exact)

boundSpec :: Spec
boundSpec = describe "the bound language" $ do
  it "adds cell counts and keeps the worse alternative" $ do
    let a = sbAdd (sbConst 3) (sbScale 2 (sbInput 0))
    renderSpaceBound a `shouldBe` "2·|input| + 3 cells"
    renderSpaceBound (sbMax a (sbConst 100)) `shouldBe`
      "max(100, 2·|input| + 3) cells"

  it "prunes an affine another one dominates" $ do
    -- 2·|input| + 3 stands above |input| + 1 everywhere, so the maximum
    -- forgets the smaller one.
    let big = sbAdd (sbScale 2 (sbInput 0)) (sbConst 3)
        small = sbAdd (sbInput 0) (sbConst 1)
    sbMax big small `shouldBe` big
    -- Incomparable affines both stay.
    let other = sbAdd (sbScale 3 (sbInput 1)) (sbConst 1)
    sbMax big other `shouldSatisfy` \b ->
      b /= big && b /= other && b == sbMax other big

  it "substitutes known input sizes and goes concrete" $ do
    let b = sbAdd (sbScale 3 (sbInput 1)) (sbConst 12)
    sbConcrete b `shouldBe` Nothing
    sbConcrete (sbSubstitute (Map.singleton 1 5) b) `shouldBe` Just 27

  it "widening stands above everything it replaced" $ do
    -- Widen a maximum of incomparable affines to width 1, then check the
    -- widened bound is at least each original at sample input sizes.
    let affs = [ sbAdd (sbScale c (sbInput p)) (sbConst k)
               | (c, p, k) <- [(2, 0, 3), (1, 1, 9), (5, 2, 0)] ]
        combined = foldr1 sbMax affs
        widened = sbWiden 1 combined
        sizes = Map.fromList [(0, 4), (1, 7), (2, 1)]
        at b = sbConcrete (sbSubstitute sizes b)
    at widened `shouldSatisfy` \w -> all (\a -> at a <= w) affs

  it "checks a measured figure against the bound" $ do
    let b = sbAdd (sbInput 0) (sbConst 2)
        sizes = Map.singleton 0 10
    sbAtLeast 12 sizes b `shouldBe` True
    sbAtLeast 13 sizes b `shouldBe` False
    -- The bound that says nothing bounds everything.
    sbAtLeast 1000000 sizes sbTop `shouldBe` True
    -- A bound still symbolic after substitution verifies nothing.
    sbAtLeast 0 Map.empty b `shouldBe` False

  it "renders paths as the words a reader would use" $ do
    renderSpaceBound (sbInput 0) `shouldBe` "|input| cells"
    renderSpaceBound (sbInput 5) `shouldBe` "|input.right.left| cells"
    renderSpaceBound sbTop `shouldBe` "unknown"

-- |The headline invariant: on every corpus program, the static bound with
-- the actual input sizes substituted stands at or above the exactly measured
-- live-heap peak. This is the empirical check of the simulation between the
-- abstract and the concrete machine.
--
-- The bound covers refinement-valid runs: the abstract input is shaped by
-- the same refinement-derived restrictions the sizing pass uses, so a run
-- whose input fails a check — which constructs and retains the aborted
-- message — is outside it. Such iterations are detected by `spAborts` and
-- not compared; at least one abort-free iteration must remain, or the test
-- would be vacuous.
staticVsMeasuredSpec :: Spec
staticVsMeasuredSpec = describe "the static bound stands above the measured peak" $
  mapM_ checkOn corpus

checkOn :: (FilePath, String, [String]) -> Spec
checkOn (path, name, inputs) = it name $ do
  modules <- loadWith path name
  case compileModules modules name of
    Left err -> expectationFailure $ "failed to compile:\n" <> err
    Right (report, sized) -> case sizingReportSpace report of
      Left why -> expectationFailure $ "no static bound: " <> why
      Right bound -> do
        -- A world the walk closed as impossible is a world it did not
        -- follow; a bound over any of those is weaker evidence, so none may
        -- occur on the corpus.
        case sizingReportSpaceStats report of
          Just (Right stats) -> ssDeadWorlds stats `shouldBe` 0
          other -> expectationFailure $ "no walk statistics: " <> show other
        checked <- loop sized bound ZeroB inputs 0
        checked `shouldSatisfy` (> 0)
  where
    loop :: CompiledExpr -> SpaceBound -> CompiledExpr -> [String] -> Int -> IO Int
    loop sized bound st inps checked = do
      let applied = appB sized st
          (m, r) = evalSpace SweepEveryAlloc applied
          sizes = Map.fromList [ (p, sizeAtPath st p) | p <- sbPaths bound ]
          validRun = spAborts m == 0
      unless (not validRun || sbAtLeast (spPeakUpper m) sizes bound)
        . expectationFailure $
          "measured " <> show (spPeakUpper m) <> " cells, bound only "
            <> renderSpaceBound (sbSubstitute sizes bound)
      let checked' = checked + fromEnum validRun
      case r of
        Left _ -> pure checked' -- an abort ended the session
        Right v -> case project v of
          BasicFW (PairSF _ newState) -> case (project newState, inps) of
            (BasicFW ZeroSF, _) -> pure checked'
            (_, [])             -> pure checked'
            (_, i : rest) -> loop sized bound (PairB (str2b i) newState) rest checked'
          _ -> expectationFailure "unexpected iteration result" >> pure checked'

-- |The input as the driver builds it, at the compiled type.
str2b :: String -> CompiledExpr
str2b = foldr (PairB . unary . ord) ZeroB

-- |Directions from the root, decoded from a path index.
pathSteps :: Integer -> [Bool]
pathSteps = go [] where
  go acc 0 = acc
  go acc p
    | odd p = go (True : acc) ((p - 1) `div` 2)
    | otherwise = go (False : acc) ((p - 2) `div` 2)

-- |How many cells the input part at a path holds. Projecting past a zero
-- stays zero, as the machine's projections do.
sizeAtPath :: CompiledExpr -> Integer -> Natural
sizeAtPath v p = cells (walk v (pathSteps p)) where
  walk :: CompiledExpr -> [Bool] -> CompiledExpr
  walk x [] = x
  walk x (s : rest) = case project x of
    BasicFW (PairSF a b) -> walk (if s then a else b) rest
    _                    -> x
  cells :: CompiledExpr -> Natural
  cells = cata $ \case
    BasicFW ZeroSF       -> 1
    BasicFW (PairSF a b) -> 1 + a + b
    _                    -> 1

-- |Tick parity and the adaptive bracket, across a whole session on the real
-- inputs — the conformance suite checks the first, empty-input iteration only.
sessionParitySpec :: Spec
sessionParitySpec = describe "the space meter across a session" $
  mapM_ parityOn corpus

parityOn :: (FilePath, String, [String]) -> Spec
parityOn (path, name, inputs) = it name $ do
  modules <- loadWith path name
  case compileModules modules name of
    Left err         -> expectationFailure $ "failed to compile:\n" <> err
    Right (_, sized) -> loop sized ZeroB inputs (0 :: Int)
  where
    loop sized st inps iterations = do
      let applied = appB sized st
          (metered, result) = evalMeter applied
          (exact, result') = evalSpace SweepEveryAlloc applied
          (adaptive, _) = evalSpace SweepAdaptive applied
      fmap show result' `shouldBe` fmap show result
      spSteps exact `shouldBe` meterSteps metered
      spBuilt exact `shouldBe` meterBuilt metered
      -- The bracket holds the pinned peak, on a real program.
      spPeakLower adaptive `shouldSatisfy` (<= spPeakLower exact)
      spPeakUpper adaptive `shouldSatisfy` (>= spPeakUpper exact)
      case result' of
        Right v | BasicFW (PairSF _ newState) <- project v
                , BasicFW (PairSF _ _) <- project newState
                , (i : rest) <- inps
                -> loop sized (PairB (str2b i) newState) rest (iterations + 1)
        _ -> iterations `shouldSatisfy` (>= 0)

-- |Programs small enough to reason about, run through the abstract walk.
staticFixtureSpec :: Spec
staticFixtureSpec = describe "the abstract walk" $ do
  it "forks on an unknown input, joins, and bounds both sides" $
    case evalSpaceStatic' defaultStaticSpaceFuel mempty oneGate of
      Left why -> expectationFailure $ "no bound: " <> show why
      Right stats -> do
        ssDeadWorlds stats `shouldBe` 0
        ssWidenings stats `shouldBe` 0
        -- The bound is in the whole input and nothing else.
        sbPaths (ssBound stats) `shouldBe` [0]
        forM_ [ZeroB, PairB ZeroB ZeroB, PairB (unary 3) (unary 2)] $ \input -> do
          let (m, _) = evalSpace SweepEveryAlloc (appB oneGate input)
          sbAtLeast (spPeakUpper m) (Map.singleton 0 (sizeAtPath input 0)) (ssBound stats)
            `shouldBe` True

  it "widens a superposition nested past the cap, and still bounds every run" $
    case evalSpaceStatic' defaultStaticSpaceFuel mempty nestedGates of
      Left why -> expectationFailure $ "no bound: " <> show why
      Right stats -> do
        ssDeadWorlds stats `shouldBe` 0
        ssWidenings stats `shouldSatisfy` (> 0)
        forM_ [ZeroB, str2b "ab", str2b "abcdefgh"] $ \input -> do
          let (m, _) = evalSpace SweepEveryAlloc (appB nestedGates input)
              sizes = Map.fromList [ (p, sizeAtPath input p) | p <- sbPaths (ssBound stats) ]
          sbAtLeast (spPeakUpper m) sizes (ssBound stats) `shouldBe` True

  it "refuses to apply a widened value rather than guess" $
    case evalSpaceStatic' defaultStaticSpaceFuel mempty (closure (FillFunctionEE nestedBody ZeroB)) of
      Left (SpaceUnsupported _) -> pure ()
      other -> expectationFailure $ "expected an unsupported report, got " <> show other

  it "keeps simpleplus at its recorded bound" $ do
    -- A golden: a change here is a change to the bound's precision, up or
    -- down, and deserves the same look as a changed iteration count.
    modules <- loadWith "simpleplus.tel" "simpleplus"
    case compileModules modules "simpleplus" of
      Left err -> expectationFailure $ "failed to compile:\n" <> err
      Right (report, _) -> case sizingReportSpace report of
        Left why -> expectationFailure $ "no static bound: " <> why
        Right bound -> renderSpaceBoundBrief bound
          `shouldBe` "sizes of 116 input parts (116 weighted) + 4337 cells"

-- |A program as the machine applies one: a closure is a pair of code and its
-- captured environment, and once applied the argument is the left part of
-- the environment its body sees. The captured part is a zero here, as the
-- sizing pass leaves a program with nothing to capture.
closure :: CompiledExpr -> CompiledExpr
closure body = PairB (deferB 7 body) ZeroB

-- |The argument, inside a `closure` body.
arg :: CompiledExpr
arg = LeftB EnvB

-- |A program that tests its whole input: zero or a pair.
oneGate :: CompiledExpr
oneGate = closure (GateSwitchEE ZeroB (PairB ZeroB ZeroB) arg)

-- |The head of the k-th element of the input list: @left (right^k input)@.
element :: Int -> CompiledExpr
element k = LeftB (iterate RightB arg !! k)

-- |Tests on six independent input parts, nested, every leaf a different
-- number: each join is a genuine superposition of the joins below it, so
-- the nesting outgrows the widening cap.
nestedBody :: CompiledExpr
nestedBody = go 0 0 where
  go :: Int -> Int -> CompiledExpr
  go k acc
    | k == 6 = unary acc
    | otherwise = GateSwitchEE (go (k + 1) (2 * acc)) (go (k + 1) (2 * acc + 1)) (element k)

nestedGates :: CompiledExpr
nestedGates = closure nestedBody

-- |Laws of the bound language, checked at random sizes: the language is a
-- max-plus algebra and widening only ever loosens.
boundLawSpec :: Spec
boundLawSpec = describe "the bound language's laws" $ do
  prop "a maximum evaluates to the larger side" $ \(Few a) (Few b) ->
    forAll sizes $ \s -> at s (sbMax a b) === max (at s a) (at s b)
  prop "a sum evaluates to the sum" $ \(Few a) (Few b) ->
    forAll sizes $ \s -> at s (sbAdd a b) === at s a + at s b
  prop "addition distributes over the maximum" $ \(Few a) (Few b) (Few c) ->
    forAll sizes $ \s -> at s (sbAdd a (sbMax b c)) === at s (sbMax (sbAdd a b) (sbAdd a c))
  prop "the maximum is idempotent and commutative" $ \(Few a) (Few b) ->
    sbMax a a === a .&&. sbMax a b === sbMax b a
  prop "widening stands above what it replaced" $ \(Few a) (Few b) ->
    forAll sizes $ \s -> at s (sbWiden 1 (sbMax a b)) >= max (at s a) (at s b)
  prop "substituting in two steps is substituting at once" $ \(Few a) ->
    forAll sizes $ \s ->
      let (front, back) = Map.partitionWithKey (\p _ -> even p) s
      in at back (sbSubstitute front a) === at s a
  where
    sizes :: Gen (Map Integer Natural)
    sizes = Map.fromList <$> mapM (\p -> (,) p . fromIntegral <$> chooseInt (0, 9)) [0 .. 5]
    at :: Map Integer Natural -> SpaceBound -> Natural
    at s b = fromMaybe (error "still symbolic after substitution")
      (sbConcrete (sbSubstitute s b))

-- |A bound of a few affines over paths 0..5, so that every law is exercised
-- without widening getting in the way.
newtype Few = Few SpaceBound
  deriving Show

instance Arbitrary Few where
  arbitrary = do
    n <- chooseInt (1, 3)
    Few . foldr1 sbMax <$> vectorOf n affine
    where
      affine = do
        k <- chooseInt (0, 6)
        terms <- listOf term
        pure $ foldr (\(p, c) b -> sbAdd (sbScale c (sbInput p)) b)
          (sbConst (fromIntegral k)) (take 3 terms)
      term = do
        p <- chooseInt (0, 5)
        c <- chooseInt (0, 4)
        pure (toInteger p, fromIntegral c :: Natural)
