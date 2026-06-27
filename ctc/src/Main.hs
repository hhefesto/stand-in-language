{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators   #-}

-- | The telomare typed-syntax category @_⇨S_@ (from @telomare.agda@) rendered as
-- circuit wiring diagrams via Conal Elliott's Compile-to-Categories (ConCat).
--
-- @telomare.agda@ defines a Cartesian category @_⇨S_@ of morphisms between @Ty@
-- objects, and its Fibonacci showcase is built purely from its constructors:
--
-- @
--   fibAccStepS = forkS exrS (addS ∘S forkS exlS exrS)   -- (a,b) ↦ (b, a+b)
--   fibInitS    = forkS idS (forkS (constS 0) (constS 1)) -- n ↦ (n,(0,1))
--   fibS        = exlS ∘S iterS fibAccStepS ∘S fibInitS
-- @
--
-- That is /literally/ a categorical wiring description.  ConCat's GHC plugin
-- reinterprets an ordinary Haskell function in any Cartesian-closed category,
-- including @ConCat.Circuit@ @(:>)@, which renders to a Graphviz DOT graph (→
-- SVG).  So the same morphism the Agda writes with @_⇨S_@ constructors, we write
-- here as a plain Haskell function (each named after its Agda counterpart) and
-- ConCat draws it as a circuit.
--
-- @iterS@ is runtime-n iteration; circuits are combinational, so the full @fibS@
-- is rendered by unrolling the iteration to a fixed depth (8) over the
-- accumulator pair.
--
-- NB: the scalars are ConCat's @R@ (= 'Double'), not @Int@.  ConCat's numeric
-- categories are exercised on @R@; @Int@ arithmetic trips the plugin's
-- post-transformation lint ("ccc post-transfo check. Lint").  The /wiring/ a
-- diagram shows — fork, add, projection — is identical either way; only the
-- carried scalar type differs from the Agda object @nat@.
module Main where

import Prelude

import System.Directory (createDirectoryIfMissing)

import ConCat.AltCat    (toCcc)
import ConCat.Circuit   ((:>), Attr, GenBuses, mkGraph, writeDot)
import ConCat.Misc      ((:*), R)
import ConCat.Rebox     ()                 -- reboxing rules, so the plugin fires
import ConCat.Syntactic (Syn, render)

-- ──────────────────────────────────────────────────────────────────────────
-- The telomare _⇨S_ Fibonacci morphisms, as ordinary Haskell functions.
-- @R@ (= Double) stands in for the Agda object @nat@; @(:*)@ for product @_⊗_@.
-- ──────────────────────────────────────────────────────────────────────────

-- | Agda @fibAccStepS : (nat ⊗ nat) ⇨S (nat ⊗ nat)@
--       @= forkS exrS (addS ∘S forkS exlS exrS)@   —   @(a,b) ↦ (b, a+b)@
fibAccStep :: R :* R -> R :* R
fibAccStep (a, b) = (b, a + b)
{-# INLINE fibAccStep #-}

-- | Agda @fibInitS : nat ⇨S (nat ⊗ (nat ⊗ nat))@
--       @= forkS idS (forkS (constS 0) (constS 1))@   —   @n ↦ (n,(0,1))@
fibInit :: R -> R :* (R :* R)
fibInit n = (n, (0, 1))
{-# INLINE fibInit #-}

-- | Agda @addS : (nat ⊗ nat) ⇨S nat@   —   @(a,b) ↦ a+b@
add :: R :* R -> R
add (a, b) = a + b
{-# INLINE add #-}

-- | The Agda @fibS = exlS ∘S iterS fibAccStepS ∘S fibInitS@ with the @iterS@
-- loop unrolled to a fixed depth of 8.  The real @fibS@ iterates a /runtime/
-- count @n@; a circuit is combinational, so we fix the unroll depth and take the
-- initial accumulator pair @(a,b)@ as the input (the @fibInitS@ constants
-- @(0,1)@ would otherwise fold away, leaving a constant circuit).  The result is
-- @exl ∘ fibAccStep^8@: eight chained step blocks.
-- Point-free (no intermediate @let@s: a @let@-chain becomes a @letrec@ the
-- ConCat plugin cannot categorify).  @exlR@ is @exlS@; @.@ is @_∘S_@.
fibUnrolled8 :: R :* R -> R
fibUnrolled8 =
  exlR . fibAccStep . fibAccStep . fibAccStep . fibAccStep
       . fibAccStep . fibAccStep . fibAccStep . fibAccStep
  where exlR (a, _) = a
{-# INLINE fibUnrolled8 #-}

-- | The 10th Fibonacci term, as a computation: @exl ∘ fibAccStep¹⁰@.  Same shape
-- as 'fibUnrolled8' but unrolled ten times.  Feeding the telomare seed @(0,1)@
-- gives @fibS 10 = exl (fibAccStep¹⁰ (0,1)) = 55@
-- (0-indexed: 0,1,1,2,3,5,8,13,21,34,55).
fibUnrolled10 :: R :* R -> R
fibUnrolled10 =
  exlR . fibAccStep . fibAccStep . fibAccStep . fibAccStep . fibAccStep
       . fibAccStep . fibAccStep . fibAccStep . fibAccStep . fibAccStep
  where exlR (a, _) = a
{-# INLINE fibUnrolled10 #-}

-- | The 10th Fibonacci term as a CLOSED computation: the @(0,1)@ seed baked in, so
-- there is no real input.  GHC @-O2@ + the ConCat plugin constant-fold the whole
-- thing to a single @const 55.0@ node — a diagram of the term's /value/.
fib10Value :: () -> R
fib10Value () = fibUnrolled10 (0, 1)
{-# INLINE fib10Value #-}

-- ──────────────────────────────────────────────────────────────────────────
-- The COST calculation + the categorical combinators (forkS, _∘S_) at the
-- program level, plus a non-fib iterS body.
-- ──────────────────────────────────────────────────────────────────────────

-- | The COST calculation, drawn.  telomare's cost functor @⟦_⟧C@ charges one
-- @tel@ tick per @iterS@ step (a writer monad @ℕ × A@), so @⟦ fibS ⟧C 10 =
-- (10, 55)@.  Here we carry the counter alongside the value:
-- @((a,b),c) ↦ ((b,a+b), c+1)@.  Unrolled ten times and projected to
-- @(value, cost)@, feeding the seed @((0,1),0)@ yields @(55, 10)@ — the value
-- cascade with a /parallel +1 cost-counter chain/.
fibCost10 :: ((R :* R) :* R) -> (R :* R)
fibCost10 = out . s . s . s . s . s . s . s . s . s . s
  where s ((a, b), c) = ((b, a + b), c + 1)   -- value step + one cost tick
        out ((a, _), c) = (a, c)              -- (value, cost)
{-# INLINE fibCost10 #-}

-- | Ten fib steps returning the FULL accumulator state (for composing pipelines).
fibState10 :: R :* R -> R :* R
fibState10 = s . s . s . s . s . s . s . s . s . s
  where s (a, b) = (b, a + b)
{-# INLINE fibState10 #-}

-- | Agda @fibPairS = forkS fibS fibS@.  The fork/duplication combinator: the
-- input fans into two fib pipelines → @(fib, fib)@.  Feeding @(0,1)@ gives
-- @(55, 55)@; telomare cost = 2·n (@forkC@ sums the branch costs).
-- (Compute fib once, then duplicate the scalar result — i.e. @dup ∘ fibUnrolled10@.
--  This is @forkS fibS fibS@ under sharing; duplicating the deep /pipeline/
--  instead, @\p -> (fib p, fib p)@, trips the ConCat plugin's post-transfo lint.)
fibPair :: R :* R -> R :* R
fibPair = dupR . fibUnrolled10
  where dupR x = (x, x)
{-# INLINE fibPair #-}

-- | Agda @doubleFibS = fibS ∘S fibS@ as a circuit.  @_∘S_@ concatenates
-- pipelines: two 10-step fib stages composed (then @exl@) — 20 steps total, so
-- feeding @(0,1)@ advances Fibonacci to @fib(20) = 6765@.  (telomare's
-- data-dependent @fib(fib n)@ is not combinational; this is the
-- pipeline-composition reading of @_∘S_@, where costs add: 10 + 10 = 20.)
doubleFib :: R :* R -> R
doubleFib = exlR . fibState10 . fibState10
  where exlR (a, _) = a
{-# INLINE doubleFib #-}

-- | @iterS@ is not fib-specific.  A scalar-state body — doubling, @x ↦ x + x@ —
-- iterated ten times from @1@ computes @2¹⁰ = 1024@.  Shows @iterS@ over a single
-- object (no pair), a genuinely different body from fib, categorifying cleanly
-- (like ConCat's @sqr = x*x@).  Shows @iterS doubleStep@.
-- (A pair-state body that reuses a wire across two combines — triangular sum
--  @(s,i) ↦ (s+i, i+1)@ or Pell @(a,b) ↦ (b, a+2b)@ — trips the ConCat plugin's
--  lint; the safe shapes are fib's @(a,b) ↦ (b, a+b)@ and this scalar doubling.)
pow2Iter10 :: R -> R
pow2Iter10 = d . d . d . d . d . d . d . d . d . d
  where d x = x + x
{-# INLINE pow2Iter10 #-}

-- | Merge sort as an 8-input sorting network — the telomare `mergeSortS`
-- (Batcher's odd-even mergesort, 19 compare-and-swaps in 6 stages).  Each
-- compare-and-swap is @(min x y, max x y)@, which ConCat compiles to a "min" and
-- a "max" gate (`MinMaxCat (:>)`).  The eight wires are a left-nested 8-pair,
-- matching telomare's @V8@.  Stages 1–3 sort the two halves [0–3] and [4–7];
-- stages 4–6 merge them.  Feeding @[7,6,5,4,3,2,1,0]@ gives @[0,1,…,7]@.
type V8 = (((((((R :* R) :* R) :* R) :* R) :* R) :* R) :* R)

-- Each stage is a compare-and-swap layer.  Comparator (i,j): position i gets the
-- min, position j the max; untouched positions pass through.  Inline min/max
-- (no `let`s) keeps the ConCat plugin happy.
sortL1, sortL2, sortL3, sortL4, sortL5, sortL6 :: V8 -> V8
sortL1 (((((((a,b),c),d),e),f),g),h) =                       -- (0,1)(2,3)(4,5)(6,7)
  (((((((min a b, max a b), min c d), max c d), min e f), max e f), min g h), max g h)
sortL2 (((((((a,b),c),d),e),f),g),h) =                       -- (0,2)(1,3)(4,6)(5,7)
  (((((((min a c, min b d), max a c), max b d), min e g), min f h), max e g), max f h)
sortL3 (((((((a,b),c),d),e),f),g),h) =                       -- (1,2)(5,6)
  (((((((a, min b c), max b c), d), e), min f g), max f g), h)
sortL4 (((((((a,b),c),d),e),f),g),h) =                       -- (0,4)(1,5)(2,6)(3,7)
  (((((((min a e, min b f), min c g), min d h), max a e), max b f), max c g), max d h)
sortL5 (((((((a,b),c),d),e),f),g),h) =                       -- (2,4)(3,5)
  (((((((a, b), min c e), min d f), max c e), max d f), g), h)
sortL6 (((((((a,b),c),d),e),f),g),h) =                       -- (1,2)(3,4)(5,6)
  (((((((a, min b c), max b c), min d e), max d e), min f g), max f g), h)
{-# INLINE sortL1 #-}
{-# INLINE sortL2 #-}
{-# INLINE sortL3 #-}
{-# INLINE sortL4 #-}
{-# INLINE sortL5 #-}
{-# INLINE sortL6 #-}

mergeSort8 :: V8 -> V8
mergeSort8 v = sortL6 (sortL5 (sortL4 (sortL3 (sortL2 (sortL1 v)))))
{-# INLINE mergeSort8 #-}

-- The 4-element merge-sort network (sort two pairs, then merge: 5 comparators in
-- 3 stages).  This is what we RENDER: ConCat's circuit serializer blows up on the
-- 8-wire network's fan-out (the proven 8-element version lives in telomare.agda
-- as mergeSortS).  Same construction, a size ConCat can draw.
type V4 = ((R :* R) :* R) :* R

s4a, s4b, s4c :: V4 -> V4
s4a (((a,b),c),d) = (((min a b, max a b), min c d), max c d)   -- (0,1)(2,3): sort pairs
s4b (((a,b),c),d) = (((min a c, min b d), max a c), max b d)   -- (0,2)(1,3): merge
s4c (((a,b),c),d) = (((a, min b c), max b c), d)               -- (1,2): merge
{-# INLINE s4a #-}
{-# INLINE s4b #-}
{-# INLINE s4c #-}

mergeSort4 :: V4 -> V4
mergeSort4 v = s4c (s4b (s4a v))
{-# INLINE mergeSort4 #-}

-- ──────────────────────────────────────────────────────────────────────────
-- Categorified into ConCat's circuit category (:>).
-- ──────────────────────────────────────────────────────────────────────────

fibAccStepCirc :: (R :* R) :> (R :* R)
fibAccStepCirc = toCcc fibAccStep

fibInitCirc :: R :> (R :* (R :* R))
fibInitCirc = toCcc fibInit

addCirc :: (R :* R) :> R
addCirc = toCcc add

fibUnrolled8Circ :: (R :* R) :> R
fibUnrolled8Circ = toCcc fibUnrolled8

fibUnrolled10Circ :: (R :* R) :> R
fibUnrolled10Circ = toCcc fibUnrolled10

fib10ValueCirc :: () :> R
fib10ValueCirc = toCcc fib10Value

fibCost10Circ :: ((R :* R) :* R) :> (R :* R)
fibCost10Circ = toCcc fibCost10

fibPairCirc :: (R :* R) :> (R :* R)
fibPairCirc = toCcc fibPair

doubleFibCirc :: (R :* R) :> R
doubleFibCirc = toCcc doubleFib

pow2Iter10Circ :: R :> R
pow2Iter10Circ = toCcc pow2Iter10

mergeSort4Circ :: V4 :> V4
mergeSort4Circ = toCcc mergeSort4

-- ──────────────────────────────────────────────────────────────────────────
-- Rendering
-- ──────────────────────────────────────────────────────────────────────────

main :: IO ()
main = do
  putStrLn "Telomare _⇨S_ design via Conal Elliott's Compile-to-Categories"
  putStrLn ""
  putStrLn "Each function below is a Haskell port of a telomare.agda _⇨S_ morphism."
  putStrLn "ConCat's plugin reinterprets it as a categorical combinator term and"
  putStrLn "(via ConCat.Circuit) as a wiring diagram written to out/*.dot."
  putStrLn ""

  -- The categorical-combinator (Syn) form of each morphism — cross-check it
  -- against the corresponding _⇨S_ term in telomare.agda.
  showSyn "fibAccStep" "(a,b) -> (b, a+b)        [Agda fibAccStepS]"
          (toCcc fibAccStep   :: Syn (R :* R) (R :* R))
  showSyn "fibInit"    "n -> (n,(0,1))           [Agda fibInitS]"
          (toCcc fibInit      :: Syn R (R :* (R :* R)))
  showSyn "add"        "(a,b) -> a+b             [Agda addS]"
          (toCcc add          :: Syn (R :* R) R)
  showSyn "fibUnrolled8" "exl . fibAccStep^8       [Agda exlS ∘ iterS fibAccStepS, depth 8]"
          (toCcc fibUnrolled8 :: Syn (R :* R) R)
  showSyn "fibUnrolled10" "exl . fibAccStep^10     [10th term: feed (0,1) -> 55]"
          (toCcc fibUnrolled10 :: Syn (R :* R) R)
  showSyn "fib10Value"  "() -> fib(10) = 55       [closed; folds to a const node]"
          (toCcc fib10Value    :: Syn () R)
  showSyn "fibCost10"   "((a,b),c)->((b,a+b),c+1)^10  [⟦fibS⟧C: value + cost]"
          (toCcc fibCost10  :: Syn ((R :* R) :* R) (R :* R))
  showSyn "fibPair"     "forkS fibS fibS              [fork / duplication]"
          (toCcc fibPair    :: Syn (R :* R) (R :* R))
  showSyn "doubleFib"   "fibS ∘S fibS (pipeline)      [composition]"
          (toCcc doubleFib  :: Syn (R :* R) R)
  showSyn "pow2Iter10"  "(x -> x+x)^10                [iterS, non-fib: 2^10]"
          (toCcc pow2Iter10 :: Syn R R)

  putStrLn ("  check: exl (fibAccStep^10 (0,1)) = " ++ show (fibUnrolled10 (0, 1) :: R))
  putStrLn ("  check: fibCost10 ((0,1),0)       = " ++ show (fibCost10 ((0, 1), 0)) ++ "   (value, cost)")
  putStrLn ("  check: fibPair (0,1)             = " ++ show (fibPair (0, 1)))
  putStrLn ("  check: doubleFib (0,1)           = " ++ show (doubleFib (0, 1) :: R) ++ "   = fib(20)")
  putStrLn ("  check: pow2Iter10 1              = " ++ show (pow2Iter10 1 :: R) ++ "   = 2^10")
  putStrLn ("  check: mergeSort8 [7,6..0]       = " ++ show (mergeSort8 (((((((7,6),5),4),3),2),1),0)))
  putStrLn ("  check: mergeSort4 [3,1,4,2]      = " ++ show (mergeSort4 (((3,1),4),2)))
  putStrLn ""

  writeCircuitGraphs

  putStrLn "Render the DOT graphs to SVG with GraphViz, e.g.:"
  putStrLn "    dot -Tsvg out/fib-acc-step.dot   -o out/fib-acc-step.svg"
  putStrLn "    dot -Tsvg out/fib-10.dot         -o out/fib-10.svg"
  putStrLn "(or just run `nix run .#telomare-ctc-svg`)."

showSyn :: String -> String -> Syn a b -> IO ()
showSyn name source syn = do
  putStrLn (name ++ "  Haskell: " ++ source)
  putStrLn ("  CCC: " ++ render syn)
  putStrLn ""

graphAttrs :: [Attr]
graphAttrs = [("ranksep", "0.8")]

writeCircuitGraphs :: IO ()
writeCircuitGraphs = do
  createDirectoryIfMissing True "out"
  putStrLn "Circuit graph interpretation"
  writeGraph "fib-acc-step"   fibAccStepCirc
  writeGraph "fib-init"       fibInitCirc
  writeGraph "add"            addCirc
  writeGraph "fib-unrolled-8" fibUnrolled8Circ
  writeGraph "fib-10"         fibUnrolled10Circ
  writeGraph "fib-10-value"   fib10ValueCirc
  writeGraph "fib-cost"       fibCost10Circ
  writeGraph "fib-pair"       fibPairCirc
  writeGraph "double-fib"     doubleFibCirc
  writeGraph "pow2-iter"      pow2Iter10Circ
  writeGraph "merge-sort"     mergeSort4Circ
  putStrLn ""

writeGraph :: (GenBuses a, GenBuses b) => String -> (a :> b) -> IO ()
writeGraph name circuit = do
  writeDot name graphAttrs (mkGraph circuit)
  putStrLn ("  wrote out/" ++ name ++ ".dot")
