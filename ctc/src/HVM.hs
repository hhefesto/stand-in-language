{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-missing-methods -Wno-unused-imports #-}

-- | A new ConCat category whose CCC-class instances EMIT Bend (HVM2) code.
-- Modeled on @ConCat.Syntactic.Syn@, but instead of pretty-printing it renders a
-- point-free term of Bend combinators (`comp`, `cross`, `exl`, `addC`, `minC`,
-- `applyC`, `curryC`, `inlC`, …) defined in the Bend prelude (`bendPrelude`).
-- `toCcc f :: HVM a b` then renders to a runnable HVM2/Bend program.
module HVM where

import Prelude hiding (id, (.), const, curry, uncurry)
import Data.List (intercalate)

import ConCat.Category
import ConCat.Misc (Yes1, (:*))

-- A Bend combinator-application term: a nullary combinator (`Atom`/`App s []`)
-- or a combinator applied to sub-morphism terms.  Point-free ⇒ no shared vars.
data Bnd = Atom String | App String [Bnd]

newtype HVM a b = HVM Bnd

unHVM :: HVM a b -> Bnd
unHVM (HVM t) = t

app0 :: String -> HVM a b
app0 s = HVM (App s [])

app1 :: String -> HVM a b -> HVM c d
app1 s (HVM p) = HVM (App s [p])

app2 :: String -> HVM a b -> HVM c d -> HVM e f
app2 s (HVM p) (HVM q) = HVM (App s [p, q])

-- Render the term as a Bend expression: nullary → bare name; n-ary → name(args).
renderBnd :: Bnd -> String
renderBnd (Atom s)      = s
renderBnd (App s [])    = s
renderBnd (App s args)  = s ++ "(" ++ intercalate ", " (map renderBnd args) ++ ")"

render :: HVM a b -> String
render = renderBnd . unHVM

instance Show (HVM a b) where show = render

-- The Bend (HVM2) prelude: each ConCat combinator as a Bend function.  Bound
-- combinators that need pair destructuring use a helper `def` (Bend lambdas take
-- one var and have expression bodies only).  Higher-order combinators return a
-- `lambda`.  This is the runtime that makes the emitted point-free term execute.
bendPrelude :: String
bendPrelude = unlines
  [ "# ConCat combinator prelude for HVM2/Bend (auto-paired with emitted terms)."
  , "def idC(x):"
  , "  return x"
  , "def dup(x):"
  , "  return (x, x)"
  , "def exl(p):"
  , "  (a, b) = p"
  , "  return a"
  , "def exr(p):"
  , "  (a, b) = p"
  , "  return b"
  , "def swapP(p):"
  , "  (a, b) = p"
  , "  return (b, a)"
  , "def lassocP(p):"
  , "  (a, bc) = p"
  , "  (b, c) = bc"
  , "  return ((a, b), c)"
  , "def rassocP(p):"
  , "  (ab, c) = p"
  , "  (a, b) = ab"
  , "  return (a, (b, c))"
  , "def addC(p):"
  , "  (a, b) = p"
  , "  return a + b"
  , "def subC(p):"
  , "  (a, b) = p"
  , "  return a - b"
  , "def mulC(p):"
  , "  (a, b) = p"
  , "  return a * b"
  , "def negateC(x):"
  , "  return 0 - x"
  , "def minC(p):"
  , "  (a, b) = p"
  , "  switch (a < b):"
  , "    case 0:"
  , "      return b"
  , "    case _:"
  , "      return a"
  , "def maxC(p):"
  , "  (a, b) = p"
  , "  switch (a < b):"
  , "    case 0:"
  , "      return a"
  , "    case _:"
  , "      return b"
  , "def comp(g, f):"
  , "  return lambda x: g(f(x))"
  , "def crossH(f, g, p):"
  , "  (a, b) = p"
  , "  return (f(a), g(b))"
  , "def cross(f, g):"
  , "  return lambda p: crossH(f, g, p)"
  , "def firstH(f, p):"
  , "  (a, b) = p"
  , "  return (f(a), b)"
  , "def firstC(f):"
  , "  return lambda p: firstH(f, p)"
  , "def secondH(g, p):"
  , "  (a, b) = p"
  , "  return (a, g(b))"
  , "def secondC(g):"
  , "  return lambda p: secondH(g, p)"
  , "def applyC(p):"
  , "  (g, x) = p"
  , "  return g(x)"
  , "def curryC(f):"
  , "  return lambda a: (lambda b: f((a, b)))"
  , "def uncurryCH(f, p):"
  , "  (a, b) = p"
  , "  g = f(a)"
  , "  return g(b)"
  , "def uncurryC(f):"
  , "  return lambda p: uncurryCH(f, p)"
  , "def constC(k):"
  , "  return lambda x: k"
  ]

-- Assemble a complete, runnable Bend program: prelude + a `main` that applies the
-- compiled morphism term to a Bend input literal.
toBendProgram :: HVM a b -> String -> String
toBendProgram m input = bendPrelude ++ unlines
  [ ""
  , "def main():"
  , "  morph = " ++ render m
  , "  return morph(" ++ input ++ ")"
  ]

-- ── Bounded recursion through ConCat → HVM2 ──────────────────────────────────
-- The plugin can't categorify recursion, but the per-node morphisms (step / init
-- / leaf / combine) DO go through `toCcc`.  We emit those terms as NAMED Bend
-- globals and a specialized recursive loop that calls them by name.  (A generic
-- combinator that *passes* the step as a value trips HVM2's duplication of
-- higher-order tuple-functions; referencing a global is fresh each call and runs
-- correctly — and, for the fold, in parallel.)  The size is a RUNTIME CLI arg, so
-- the .bend is constant (no unrolling).

-- exl ∘ iterate(step) ∘ init, with the iteration count a runtime CLI argument.
-- step : a ⇨ a ;  init : n ⇨ (count × a).  Run:  bend run-c file.bend <n>
toBendIterate :: HVM a a -> HVM n (Int :* a) -> String
toBendIterate step initM = bendPrelude ++ unlines
  [ ""
  , "def stepFn(x):"
  , "  s = " ++ render step
  , "  return s(x)"
  , "def iterGo(n, x):"
  , "  switch n:"
  , "    case 0:"
  , "      return x"
  , "    case _:"
  , "      return iterGo(n-1, stepFn(x))"
  , "def initFn(n):"
  , "  i = " ++ render initM
  , "  return i(n)"
  , "def main(n):"
  , "  pre = initFn(n)"
  , "  (cnt, st0) = pre"
  , "  fin = iterGo(cnt, st0)"
  , "  (a, b) = fin"
  , "  return a"
  ]

-- A catamorphism over a perfect binary tree: foldGo's two recursive calls are
-- independent, so HVM2 reduces them IN PARALLEL.  leaf : a ⇨ b, combine : (b×b) ⇨ b.
-- genTree builds 2^d leaves (=1).  Run:  bend run-c file.bend <depth>
toBendFold :: HVM a b -> HVM (b :* b) b -> String
toBendFold leaf comb = bendPrelude ++ unlines
  [ ""
  , "type BTree:"
  , "  Leaf { value }"
  , "  Node { left, right }"
  , "def leafFn(v):"
  , "  l = " ++ render leaf
  , "  return l(v)"
  , "def combFn(p):"
  , "  c = " ++ render comb
  , "  return c(p)"
  , "def foldGo(t):"
  , "  match t:"
  , "    case BTree/Leaf:"
  , "      return leafFn(t.value)"
  , "    case BTree/Node:"
  , "      l = foldGo(t.left)     # independent ─┐ HVM2 folds"
  , "      r = foldGo(t.right)    # independent ─┘ these in parallel"
  , "      return combFn((l, r))"
  , "def genTree(d):"
  , "  switch d:"
  , "    case 0:"
  , "      return BTree/Leaf { value: 1 }"
  , "    case _:"
  , "      a = genTree(d-1)"
  , "      b = genTree(d-1)"
  , "      return BTree/Node { left: a, right: b }"
  , "def main(d):"
  , "  return foldGo(genTree(d))"
  ]

-- ── CCC instances (mirror ConCat.Syntactic.Syn; emit Bend combinator names) ──

instance Category HVM where
  id  = app0 "idC"
  (.) = app2 "comp"

instance AssociativePCat HVM where
  lassocP = app0 "lassocP"
  rassocP = app0 "rassocP"

instance MonoidalPCat HVM where
  (***)  = app2 "cross"
  first  = app1 "firstC"
  second = app1 "secondC"

instance BraidedPCat HVM where
  swapP = app0 "swapP"

instance ProductCat HVM where
  exl = app0 "exl"
  exr = app0 "exr"
  dup = app0 "dup"

instance UnitCat HVM where
  lunit   = app0 "lunit"
  runit   = app0 "runit"
  lcounit = app0 "lcounit"
  rcounit = app0 "rcounit"

instance TerminalCat HVM where
  it = app0 "itC"

instance ClosedCat HVM where
  apply   = app0 "applyC"
  curry   = app1 "curryC"
  uncurry = app1 "uncurryC"

instance NumCat HVM a where
  negateC = app0 "negateC"
  addC    = app0 "addC"
  subC    = app0 "subC"
  mulC    = app0 "mulC"
  powIC   = app0 "powIC"

instance MinMaxCat HVM a where
  minC = app0 "minC"
  maxC = app0 "maxC"

atomicConst :: Show b => b -> HVM a b
atomicConst b = app1 "constC" (app0 (show b))

instance ConstCat HVM Int     where const = atomicConst
instance ConstCat HVM Integer where const = atomicConst
instance ConstCat HVM Bool    where const = atomicConst
instance ConstCat HVM ()      where const = atomicConst

-- ── Cocartesian (sums) ──
instance AssociativeSCat HVM where
  lassocS = app0 "lassocS"
  rassocS = app0 "rassocS"

instance BraidedSCat HVM where
  swapS = app0 "swapS"

instance MonoidalSCat HVM where
  (+++) = app2 "plusC"
  left  = app1 "leftC"
  right = app1 "rightC"

instance CoproductCat HVM where
  inl = app0 "inlC"
  inr = app0 "inrC"
  jam = app0 "jamC"

instance DistribCat HVM where
  distl = app0 "distl"
  distr = app0 "distr"

-- ── Comparison / boolean / conditional (defensive; cheap) ──
instance BoolCat HVM where
  notC = app0 "notC"
  andC = app0 "andC"
  orC  = app0 "orC"
  xorC = app0 "xorC"

instance EqCat HVM a where
  equal    = app0 "equalC"
  notEqual = app0 "notEqualC"

instance Ord a => OrdCat HVM a where
  lessThan           = app0 "lessThanC"
  greaterThan        = app0 "greaterThanC"
  lessThanOrEqual    = app0 "leqC"
  greaterThanOrEqual = app0 "geqC"

instance IfCat HVM a where
  ifC = app0 "ifC"
