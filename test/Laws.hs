{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}

-- | Law-level property tests: what the Agda spec PROVES
-- (T3.Sem.Graded.G-val, T3.Adequacy.precise\/adequate), re-checked on the
-- Haskell mirror over randomly generated core terms.  This is the bridge
-- that transfers the machine-checked theorems to the shipped artifact.
module Laws (lawProps) where

import Numeric.Natural (Natural)
import Test.QuickCheck

import SpecVectors (isZero, predS)
import Telomare.Core
import Telomare.Denotation

-- Compact printer for counterexample reporting (GADTs can't derive Show).
showM :: Morph a b -> String
showM IdS            = "IdS"
showM (g :.: f)      = "(" <> showM g <> " . " <> showM f <> ")"
showM (f :***: g)    = "(" <> showM f <> " *** " <> showM g <> ")"
showM SwapS          = "SwapS"
showM AssocS         = "AssocS"
showM UnassocS       = "UnassocS"
showM ExlS           = "ExlS"
showM ExrS           = "ExrS"
showM WeakS          = "WeakS"
showM RunitS         = "RunitS"
showM LunitS         = "LunitS"
showM InlS           = "InlS"
showM InrS           = "InrS"
showM (CaseS l r)    = "CaseS (" <> showM l <> ") (" <> showM r <> ")"
showM DistlS         = "DistlS"
showM NilS           = "NilS"
showM ConsS          = "ConsS"
showM UnconsS        = "UnconsS"
showM NatOutS        = "NatOutS"
showM SucS           = "SucS"
showM AddS           = "AddS"
showM (ConstS k)     = "ConstS " <> show k
showM DupNatS        = "DupNatS"
showM (CopyS _)      = "CopyS"
showM (CurryS _ f)   = "CurryS (" <> showM f <> ")"
showM ApplyS         = "ApplyS"
showM MapCS          = "MapCS"
showM (GuardS _ t)   = "GuardS (" <> showM t <> ")"
showM (DupS _)       = "DupS"
showM (BoxS f)       = "BoxS (" <> showM f <> ")"
showM (BoxValS f)    = "BoxValS (" <> showM f <> ")"
showM MergeS         = "MergeS"
showM (MapS f)       = "MapS (" <> showM f <> ")"
showM (IterS f)      = "IterS (" <> showM f <> ")"
showM (FoldS f)      = "FoldS (" <> showM f <> ")"
showM (WhileS _ t s) = "WhileS (" <> showM t <> ") (" <> showM s <> ")"

-- Wrappers so QuickCheck can Show counterexamples.
newtype NN = NN (Morph 'Nat 'Nat)
instance Show NN where show (NN f) = showM f

newtype ProgNB = ProgNB (Morph 'Nat ('Bang 'Nat))
instance Show ProgNB where show (ProgNB f) = showM f

smallNat :: Gen Natural
smallNat = fromIntegral <$> chooseInt (0, 6)

-- Affine Nat ⇨ Nat pieces: no dup of any kind, no probes.
affineLeaf :: Gen (Morph 'Nat 'Nat)
affineLeaf = elements [IdS, SucS, predS, ConstS 3, ConstS 7]

-- General pieces add the atom exemption (dupNatS) and the costed data
-- copy (CopyS at Nat).
anyLeaf :: Gen (Morph 'Nat 'Nat)
anyLeaf = frequency
  [ (3, affineLeaf)
  , (1, pure (AddS :.: DupNatS))
  , (1, pure (AddS :.: CopyS CopyNat))
  ]

pipe :: Gen (Morph 'Nat 'Nat) -> Int -> Gen (Morph 'Nat 'Nat)
pipe l 0 = l
pipe l n = oneof
  [ l
  , (:.:) <$> pipe l (n `div` 2) <*> pipe l (n `div` 2)
  ]

genNN :: Gen NN
genNN = NN <$> sized (pipe anyLeaf . min 6)

-- Full programs: a pipeline capped by fuel-carrying iteration (the shape
-- every Telomare core program has — recursion only via iterS/whileS).
cap :: Morph 'Nat 'Nat -> Natural -> Bool -> Morph 'Nat ('Bang 'Nat)
cap f seed useWhile
  | useWhile  = WhileS SNat isZero f :.: seeded
  | otherwise = IterS f :.: seeded
  where seeded = (IdS :***: BoxValS (ConstS seed)) :.: RunitS

genProg :: Gen (Morph 'Nat 'Nat) -> Gen ProgNB
genProg l = do
  f <- sized (pipe l . min 4)
  seed <- smallNat
  ProgNB . cap f seed <$> arbitrary

-- Iter-only capping: whileS is NOT in the affine fragment — its probe
-- reads the loop state without consuming it, and that implicit copy is
-- priced (dupAlg.chargeProbe = sizeT).  The first run of this suite
-- falsified the naive property on a WhileS cap, exactly as the semantics
-- says it should.
genAffineProg :: Gen ProgNB
genAffineProg = do
  f <- sized (pipe affineLeaf . min 4)
  seed <- smallNat
  pure (ProgNB (cap f seed False))

-- G-val: the graded semantics' value component equals the specification,
-- for every algebra (Agda: proved generically; here: both instances).
prop_coherence :: Property
prop_coherence =
  forAll (genProg anyLeaf) $ \(ProgNB p) ->
  forAll smallNat $ \n ->
    snd (evalG workAlg p n) == evalV p n
      && snd (evalG dupAlg p n) == evalV p n

-- Precision (Agda: T3.Adequacy.precise): budget + slack ⇒ value + exact
-- slack left.
prop_precision :: Property
prop_precision =
  forAll (genProg anyLeaf) $ \(ProgNB p) ->
  forAll smallNat $ \n ->
  forAll smallNat $ \extra ->
    evalK p n (work p n + extra) == Just (evalV p n, extra)

-- Adequacy (extra = 0): run with the computed budget, finish with 0 left.
prop_adequate :: Property
prop_adequate =
  forAll (genProg anyLeaf) $ \(ProgNB p) ->
  forAll smallNat $ \n ->
    evalK p n (work p n) == Just (evalV p n, 0)

-- The affine fragment (no dupS/dupNatS, no guard/while probes) has dup
-- grade 0 BY CONSTRUCTION: no implicit contraction exists to charge for.
prop_affine_dup_zero :: Property
prop_affine_dup_zero =
  forAll genAffineProg $ \(ProgNB p) ->
  forAll smallNat $ \n ->
    dupGrade p n == 0

-- Grade functoriality (regression; definitional in this implementation,
-- proved generically in Agda): grades compose along ⋄.
prop_work_functorial :: Property
prop_work_functorial =
  forAll genNN $ \(NN f) ->
  forAll genNN $ \(NN g) ->
  forAll smallNat $ \n ->
    work (g :.: f) n == work f n + work g (evalV f n)

prop_dup_functorial :: Property
prop_dup_functorial =
  forAll genNN $ \(NN f) ->
  forAll genNN $ \(NN g) ->
  forAll smallNat $ \n ->
    dupGrade (g :.: f) n == dupGrade f n + dupGrade g (evalV f n)

-- Closure laws: applying a curried body once agrees with the body on
-- values across all three evaluators, work(apply) = 1 + work(body), and
-- forming a closure is free.
prop_closure_beta :: Property
prop_closure_beta =
  forAll genNN $ \(NN f) ->
  forAll smallNat $ \n ->
    let applied = ApplyS :.: (CurryS SUnit (f :.: ExrS) :***: IdS) :.: LunitS
    in evalV applied n == evalV f n
      && snd (evalG workAlg applied n) == evalV f n
      && snd (evalG dupAlg applied n) == evalV f n
      && work applied n == 1 + work f n
      && dupGrade applied n == dupGrade f n
      && evalK applied n (work applied n) == Just (evalV f n, 0)

-- Higher-order map: a promoted closed closure applied per element equals
-- plain list map.  MapCS charges 1 step per element plus the body's own
-- grade (no separate apply tag), mirroring MapS.
prop_mapc_coherence :: Property
prop_mapc_coherence =
  forAll (listOf smallNat) $ \xs ->
  forAllBlind affineLeaf $ \f ->
    let clo = BoxValS (CurryS SUnit (f :.: ExrS))
        prog = MapCS :.: (clo :***: IdS) :.: LunitS
    in evalV prog xs == fmap (evalV f) xs
      && work prog xs == fromIntegral (length xs) + sum (fmap (work f) xs)
      && evalK prog xs (work prog xs) == Just (fmap (evalV f) xs, 0)

-- CopyS charge exactness (Agda: dupAlg.chargeD copyT = sizeT): the dup
-- grade of a lone copy is exactly the copied value's size, and the copy
-- is free work.
prop_copy_charge_exact :: Property
prop_copy_charge_exact =
  forAll (listOf smallNat) $ \xs ->
  forAll smallNat $ \n ->
    let listCopy = CopyS (CopyList CopyNat)
        pairCopy = CopyS (CopyProd CopyNat CopyNat)
    in dupGrade listCopy xs == sizeVal (SList SNat) xs
      && work listCopy xs == 0
      && dupGrade pairCopy (n, n) == 2
      && evalV listCopy xs == (xs, xs)

prop_map_coherence_precision :: Property
prop_map_coherence_precision =
  forAll (listOf smallNat) $ \xs ->
  forAllBlind affineLeaf $ \f ->
    let mapped = MapS f
    in snd (evalG workAlg mapped xs) == evalV mapped xs
      && snd (evalG dupAlg mapped xs) == evalV mapped xs
      && evalK mapped xs (work mapped xs) == Just (evalV mapped xs, 0)
      && work mapped xs == fromIntegral (length xs) + sum (fmap (work f) xs)

lawProps :: [(String, Property)]
lawProps =
  [ ("prop_coherence (G-val)",       prop_coherence)
  , ("prop_precision (precise)",     prop_precision)
  , ("prop_adequate (adequate)",     prop_adequate)
  , ("prop_affine_dup_zero",         prop_affine_dup_zero)
  , ("prop_work_functorial",         prop_work_functorial)
  , ("prop_dup_functorial",          prop_dup_functorial)
  , ("prop_copy_charge_exact",       prop_copy_charge_exact)
  , ("prop_closure_beta",            prop_closure_beta)
  , ("prop_mapc_coherence",          prop_mapc_coherence)
  , ("prop_map_coherence_precision", prop_map_coherence_precision)
  ]
