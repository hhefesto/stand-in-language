-- Telomare: A Denotational Specification of a Total Functional Language
-- Following Conal Elliott's Denotational Design + Type Class Morphisms methodology.
--
-- Core idea: every computation is a function (Tel → Maybe (a × Tel)).
-- Tel (the "telomere") strictly decreases on each recursive unfolding,
-- guaranteeing totality. Time and space are bounded by initial tel.

{-# OPTIONS --guardedness #-}
module telomare-backwards where

open import Data.Nat             using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Maybe           using (Maybe; just; nothing; _>>=_)
open import Data.Product         using (_×_; _,_; proj₁; proj₂)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Unit            using (⊤; tt)
open import Data.Bool            using (Bool; true; false; not; if_then_else_)
open import Function             using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Agda.Primitive                        using (lzero)

-- ─────────────────────────────────────────────────────────────────────────────
-- § 1.  SEMANTIC MODEL  (Denotational Design: choose the model first)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- The denotation of every computation is:
--
--   ⟦ e : τ ⟧ : Tel → Maybe (⟦τ⟧ × Tel)
--
-- where Tel = ℕ (the "telomere").
-- • just (v , g') means: produced value v, g' tel remains.
-- • nothing       means: telomere exhausted — program halts gracefully.
--
-- This is the Kleisli category of the monad TelM.

Tel : Set
Tel = ℕ

TelM : Set → Set
TelM A = Tel → Maybe (A × Tel)

-- ─────────────────────────────────────────────────────────────────────────────
-- § 2.  TelM IS A MONAD  (instances follow from the semantic model — TCM)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- TCM = Type Class Morphism (Elliott, ICFP 2009).
-- A TCM is a function h : A → B that is a homomorphism for a given type class:
-- the class structure on A corresponds to the class structure on B via h.
-- Here h = ⟦·⟧ (the denotation function).
--
-- TCM principle (Elliott): "the instance's meaning follows the meaning's instance."
-- TelM A ≅ StateT Tel Maybe A, so all instances are derived homomorphically.

return-tel : {A : Set} → A → TelM A
return-tel a g = just (a , g)          -- pure values cost 0 tel

bind-tel : {A B : Set} → TelM A → (A → TelM B) → TelM B
bind-tel m f g = m g >>= λ { (a , g') → f a g' }

-- Consume exactly 1 unit of tel (one "step" / one telomere shortening)
step : {A : Set} → TelM A → TelM A
step m zero    = nothing               -- telomere exhausted
step m (suc g) = m g                   -- consume 1, continue

-- ─────────────────────────────────────────────────────────────────────────────
-- § 3.  TYPES OF THE OBJECT LANGUAGE
-- ─────────────────────────────────────────────────────────────────────────────

data Ty : Set where
  unit  : Ty
  bool  : Ty
  nat   : Ty
  _⊗_   : Ty → Ty → Ty              -- product
  _⊕_   : Ty → Ty → Ty              -- sum
  _⇒_   : Ty → Ty → Ty              -- function (costs tel on apply)

-- Denotation of types as Agda types
⟦_⟧T : Ty → Set
⟦ unit  ⟧T = ⊤
⟦ bool  ⟧T = Bool
⟦ nat   ⟧T = ℕ
⟦ A ⊗ B ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
⟦ A ⊕ B ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T
⟦ A ⇒ B ⟧T = ⟦ A ⟧T → TelM ⟦ B ⟧T   -- functions live in TelM

-- ─────────────────────────────────────────────────────────────────────────────
-- § 4.  THE KLEISLI CATEGORY OF TelM
--       (Compiling to Categories: programs are morphisms in this category)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Objects  : Agda types (or ⟦τ⟧T for object-language types)
-- Morphisms: A →K B  =  A → TelM B
--
-- Identity and composition satisfy the category laws provably.

infixr 0 _→K_
_→K_ : Set → Set → Set
A →K B = A → TelM B

idK : {A : Set} → A →K A
idK = return-tel

_∘K_ : {A B C : Set} → (B →K C) → (A →K B) → (A →K C)
(g ∘K f) a = bind-tel (f a) g

-- Cartesian structure (fork / projections)
forkK : {A B C : Set} → (A →K B) → (A →K C) → (A →K (B × C))
forkK f g a = bind-tel (f a) λ b →
              bind-tel (g a) λ c →
              return-tel (b , c)

exlK : {A B : Set} → (A × B) →K A
exlK = return-tel ∘ proj₁

exrK : {A B : Set} → (A × B) →K B
exrK = return-tel ∘ proj₂

-- ─────────────────────────────────────────────────────────────────────────────
-- § 5.  THE ONLY RECURSION PRIMITIVE — fix with mandatory tel consumption
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Every unfolding of fix costs 1 tel.
-- Therefore recursion depth ≤ initial tel.  Totality follows immediately.
--
-- Implementation note: Agda requires structural recursion.  We satisfy this
-- with the "fuel" pattern: fix-aux recurses on an explicit Tel fuel argument
-- that decreases by 1 on each unfolding.  The computation tel t' is threaded
-- independently.  fix ties the fuel to the computation's own tel supply,
-- so the bound is tight: depth ≤ initial tel.

private
  fix-aux : {A : Set} → Tel → ((A →K A) → (A →K A)) → A →K A
  fix-aux zero    _    _ _       = nothing          -- fuel exhausted ⟹ halt
  fix-aux (suc f) body a g       = body (fix-aux f body) a g

fix : {A : Set} → ((A →K A) → (A →K A)) → A →K A
fix body a g = fix-aux g body a g
-- The fuel equals the tel: each unfolding reduces both by 1 (via body's
-- internal step calls), keeping the bound tight.

-- Generalised fixpoint: input type S may differ from output type R.
-- (fix is the special case S = R.)
-- Used by `limited` where the state type and result type can differ —
-- e.g. gcd : ℕ×ℕ →K ℕ  (state is a pair, result is a single number).
private
  fixT-aux : {S R : Set} → Tel → ((S →K R) → S →K R) → S →K R
  fixT-aux zero    _    _ _ = nothing
  fixT-aux (suc f) body s   = step (body (fixT-aux f body) s)
  -- `step` here means: each unfolding costs 1 tel AND 1 fuel.
  -- For a computation needing n recursive calls:
  --   tel consumed  = n + 1   (n recursive steps + 1 base step)
  --   tel remaining = t₀ − (n + 1)   when t₀ > n

fixT : {S R : Set} → ((S →K R) → S →K R) → S →K R
fixT body s g = fixT-aux g body s g

-- Iteration derived from fix (nat recursion):
--   iter n base step_fn  runs step_fn exactly n times (or until tel runs out)
iter : {A : Set} → ℕ → A → (A →K A) → TelM A
iter zero    acc _  = return-tel acc
iter (suc n) acc sf = bind-tel (sf acc) (λ acc' → iter n acc' sf)

-- ─────────────────────────────────────────────────────────────────────────────
-- § 6.  COMPLEXITY BOUNDS  (derived from the semantic model)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Let c : TelM A.  Run it with initial tel t₀.
--
--   Time  (steps taken) = t₀ − t_final    ≤ t₀
--   Depth (call depth)  ≤ t₀              (each recursive call costs ≥ 1)
--   Space               = O(depth × frame) = O(t₀)
--
-- Formally: if c t₀ = just (v , t_f) then the number of `step` calls ≤ t₀.

-- Helper: tel consumed
tel-consumed : {A : Set} → TelM A → Tel → Maybe ℕ
tel-consumed c g₀ = c g₀ >>= λ { (_ , gf) → just (g₀ ∸ gf) }

-- ─────────────────────────────────────────────────────────────────────────────
-- § 7.  TOTALITY THEOREM
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Every TelM computation terminates: it returns just or nothing, never diverges.
-- This holds by construction — TelM A = Tel → Maybe (A × Tel) is a total function.
-- No partiality, no ⊥, no coinduction needed.
--
-- Proof sketch (by induction on tel):
--   Base:  step m 0       = nothing                       ✓ terminates
--   Step:  step m (suc t) = m t   (recurse on strictly smaller tel)  ✓

-- Stated as a proposition: running any TelM computation is decidable.
data Result (A : Set) : Set where
  halted   : Result A           -- out of tel
  finished : A → ℕ → Result A  -- value + tel remaining

run : {A : Set} → TelM A → Tel → Result A
run c g with c g
... | nothing       = halted
... | just (v , gf) = finished v gf

-- ─────────────────────────────────────────────────────────────────────────────
-- § 8.  TYPE CLASS MORPHISM LAWS  (Elliott's TCM principle as propositions)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- The denotation ⟦·⟧ must be a homomorphism for Category:
--
--   ⟦ id ⟧       ≡ idK
--   ⟦ g ∘ f ⟧    ≡ ⟦g⟧ ∘K ⟦f⟧
--
-- Stated for the Kleisli category laws:

-- Left identity:  idK ∘K f ≡ f
left-id : {A B : Set} (f : A →K B) (a : A) (t : Tel) →
          (idK ∘K f) a t ≡ f a t
left-id f a t with f a t
... | nothing      = refl
... | just (b , t') = refl

-- Right identity: f ∘K idK ≡ f
right-id : {A B : Set} (f : A →K B) (a : A) (t : Tel) →
           (f ∘K idK) a t ≡ f a t
right-id f a t with f a t
... | nothing      = refl
... | just (b , t') = refl

-- ─────────────────────────────────────────────────────────────────────────────
-- § 9.  TELOMARE LIMITED RECURSION  { x , y , z }
-- ─────────────────────────────────────────────────────────────────────────────
--
-- In Telomare, { x , y , z } v means:
--
--   x : S →K Bool   -- test: if truthy, keep recursing; if falsy, take base
--   y : (S →K R) → S →K R  -- body: given recur, compute one step
--   z : S →K R      -- base: answer returned when x fails
--
-- Unfolding:
--   { x , y , z } v  =  if x(v)  then  y (fix {...}) v
--                                 else  z v
--
-- Which is exactly:  fix (λ recur v → if x(v) then y(recur)(v) else z(v))
--
-- The tel (telomere) bounds the number of times the test x can succeed.
-- When tel runs out, the whole computation returns nothing (halts gracefully).

limited : {S R : Set}
        → (S →K Bool)              -- x : test
        → ((S →K R) → S →K R)     -- y : body  (takes recur explicitly)
        → (S →K R)                 -- z : base  (when test fails)
        → S →K R
limited test body base =
  fixT (λ recur s →
    bind-tel (test s) (λ b →
      if b then body recur s
           else base s))

-- ── Law: { x , y , z } unfolds exactly once ──────────────────────────────
--
-- limited test body base v g
--   = if test(v) then body (limited test body base) v (g-1)
--                else base v (g-1)
--
-- (The -1 comes from fix's single tel decrement per unfolding.)

-- ─────────────────────────────────────────────────────────────────────────────
-- § 10.  TELOMARE EXAMPLES TRANSCRIBED
-- ─────────────────────────────────────────────────────────────────────────────
--
-- These mirror the .tel standard library and test files, now typed in TelM.

-- 10a.  d2c  (data-to-Church)  from Prelude.tel
--
--   d2c = \n f b -> { id
--                   , \recur i  -> f (recur (left i))
--                   , \i -> b
--                   } n
--
--   State S = ℕ  (the Peano number being consumed)
--   Result R = (ℕ → ℕ) → ℕ → ℕ  (Church numeral: \f b -> ...)
--   test  = id          (non-zero ↔ still counting)
--   body  = \recur i -> f (recur (pred i))
--   base  = \i -> b     (return accumulated base)
--
-- In Agda (simplified to Church-as-iterated-function on ℕ):

d2c : ℕ → (ℕ → ℕ) → ℕ →K ℕ
d2c n f b = limited
              (λ i → return-tel (if i ≡? zero then false else true))
              (λ recur i → bind-tel (recur (pred i)) (λ r → return-tel (f r)))
              (λ _ → return-tel b)
              n
  where
    pred : ℕ → ℕ
    pred zero    = zero
    pred (suc k) = k
    _≡?_ : ℕ → ℕ → Bool
    zero  ≡? zero  = true
    _     ≡? _     = false

-- 10b.  isEven  from tc.tel
--
--   isEven = \n -> { \i -> left i
--                  , \recur i -> recur (left (left i), not (right i))
--                  , \i -> right i
--                  } (n, 1)
--
--   State S = ℕ × Bool  (remaining count, parity accumulator)
--   Result R = Bool
--   test  = \(count,_) -> count ≠ 0
--   body  = \recur (count, parity) -> recur (pred count, not parity)
--   base  = \(_,parity) -> parity

isEven : ℕ →K Bool
isEven n = limited
             (λ s → return-tel (if proj₁ s ≡ᵇ zero then false else true))
             (λ recur s → recur (pred (proj₁ s) , not (proj₂ s)))
             (λ s → return-tel (proj₂ s))
             (n , true)
  where
    _≡ᵇ_ : ℕ → ℕ → Bool
    zero  ≡ᵇ zero  = true
    _     ≡ᵇ _     = false
    pred : ℕ → ℕ
    pred zero    = zero
    pred (suc k) = k

-- 10c.  map from Prelude.tel — described structurally:
--
--   map = \f -> { id
--               , \recur l -> (f (left l), recur (right l))
--               , \l -> 0
--               }
--
--   = limited id
--             (\recur l -> (f (head l), recur (tail l)))
--             (\l -> [])
--
--   The test is `id`: a non-empty list is truthy, empty list is falsy.
--   Each recursive call strips one element — depth = length of input.
--   Tel bounds the length of lists the program can process.

-- ─────────────────────────────────────────────────────────────────────────────
-- § 11.  FIBONACCI
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Iterative Fibonacci using `limited` ({x, y, z} in Telomare syntax):
--
--   State S = ℕ × ℕ × ℕ   (counter, fib_k, fib_{k+1})
--   Result R = ℕ
--
--   x = test  : \s -> counter ≠ 0        (keep going while counter > 0)
--   y = body  : \recur (cnt, a, b) ->
--                 recur (cnt − 1, b, a + b)   (one Fibonacci step)
--   z = base  : \(_, a, _) -> a               (return accumulated fib_k)
--
--   Initial state: (n, 0, 1)  so after n steps we have (0, fib n, fib (n+1))
--
-- Tel cost: exactly n + 1 steps  (n recursive + 1 base case).
-- fib n terminates for any tel ≥ n + 1.

private
  isNonZero : ℕ → Bool
  isNonZero zero    = false
  isNonZero (suc _) = true

  predℕ : ℕ → ℕ
  predℕ zero    = zero
  predℕ (suc k) = k

FibState : Set
FibState = ℕ × ℕ × ℕ    -- (counter, a = fib_k, b = fib_{k+1})

fib : ℕ →K ℕ
fib n = limited {S = FibState} {R = ℕ}
          -- x : test — continue while counter ≠ 0
          (λ (s : FibState) → return-tel (isNonZero (proj₁ s)))
          -- y : body — one Fibonacci step
          (λ (recur : FibState →K ℕ) (s : FibState) →
            let cnt = proj₁ s
                a   = proj₁ (proj₂ s)
                b   = proj₂ (proj₂ s)
            in recur (predℕ cnt , b , a + b))
          -- z : base — return accumulated fib value
          (λ (s : FibState) → return-tel (proj₁ (proj₂ s)))
          -- initial state
          (n , 0 , 1)

-- ── Running Fibonacci ───────────────────────────────────────────────────────
--
-- `run c t` returns:
--   finished v t'  — value v computed, t' tel remaining
--   halted         — tel exhausted before completion
--
-- For fib n: tel needed = n + 1.
-- Tel consumed per run = n + 1  (one step per recursive call + base case).
-- Tel remaining        = t₀ − (n + 1).
--
-- To evaluate: in Agda, normalise with C-c C-n on any of these names.

-- tel = n + 2 throughout: always leaves exactly 1 tel remaining
fib-0  : Result ℕ ;  fib-0  = run (fib 0)  2
fib-1  : Result ℕ ;  fib-1  = run (fib 1)  3
fib-2  : Result ℕ ;  fib-2  = run (fib 2)  4
fib-3  : Result ℕ ;  fib-3  = run (fib 3)  5
fib-4  : Result ℕ ;  fib-4  = run (fib 4)  6
fib-5  : Result ℕ ;  fib-5  = run (fib 5)  7
fib-6  : Result ℕ ;  fib-6  = run (fib 6)  8
fib-7  : Result ℕ ;  fib-7  = run (fib 7)  9
fib-8  : Result ℕ ;  fib-8  = run (fib 8)  10
fib-9  : Result ℕ ;  fib-9  = run (fib 9)  11
fib-10 : Result ℕ ;  fib-10 = run (fib 10) 12

-- Out-of-tel example:
fib-10-starved : Result ℕ
fib-10-starved = run (fib 10) 5    -- needs 11, given 5 → halted

-- ─────────────────────────────────────────────────────────────────────────────
-- § 12.  EXAMPLE PROGRAMS  (non-recursive)
-- ─────────────────────────────────────────────────────────────────────────────

-- Addition — pure (uses Agda's built-in +), costs 0 tel
addK : (ℕ × ℕ) →K ℕ
addK (n , m) = return-tel (n + m)

-- Multiplication by repeated addition — O(n) tel steps
mulK : (ℕ × ℕ) →K ℕ
mulK (zero  , _) = return-tel zero
mulK (suc n , m) = bind-tel (mulK (n , m)) (λ acc → step (return-tel (acc + m)))

-- ─────────────────────────────────────────────────────────────────────────────
-- § 12b.  MAP-THEN-FOLD: sum of successors
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Given a list of ℕ, map suc over it, then fold with addition.
--
--   sumOfSuc [1, 2, 3]  =  (1+1) + (2+1) + (3+1) + 0  =  9
--
-- In Telomare syntax (using Prelude.tel's map and foldr):
--
--   sumOfSuc = \xs -> foldr (\a b -> plus (d2c a) b) $0 (map succ xs)
--
-- Below we define mapK, foldrK, and compose them in the Kleisli category.
-- Each recursive step costs 1 tel, so processing a list of length n
-- costs n tel for map + n tel for fold = 2n tel total (unfused).

open import Data.List using (List; []; _∷_)

-- mapK mirrors Prelude.tel's:
--   map = \f -> { id
--               , \recur l -> (f (left l), recur (right l))
--               , \l -> 0
--               }
--
-- In the denotational specification we use Agda's List directly.
-- Structural recursion on List corresponds to limited's traversal of
-- nested pairs — each cons cell costs 1 tel (one `step`).
--
-- State S = List A  (input list, consumed head-first)
-- Result R = List B (output list, built by consing)
-- test  = non-empty?    (Telomare: id — non-zero is truthy)
-- body  = \recur l -> (f (head l), recur (tail l))
-- base  = \_ -> []      (Telomare: \l -> 0)

mapK : {A B : Set} → (A →K B) → List A →K List B
mapK f []       = return-tel []                  -- base: empty → empty
mapK f (x ∷ xs) = step (                         -- 1 tel per element
  bind-tel (f x)       λ y  →
  bind-tel (mapK f xs) λ ys →
  return-tel (y ∷ ys))

-- foldrK mirrors Prelude.tel's:
--   foldr = \f b ta -> let fixed = { id
--                                  , \recur l accum -> f (left l)
--                                                        (recur (right l) accum)
--                                  , \l accum -> accum
--                                  }
--                      in fixed ta b
--
-- State S = List A  (input list, consumed head-first)
-- Result R = B      (accumulated value)
-- test  = non-empty?
-- body  = \recur l accum -> f (head l) (recur (tail l) accum)
-- base  = \_ accum -> accum

foldrK : {A B : Set} → (A → B →K B) → B → List A →K B
foldrK f b []       = return-tel b               -- base: return accumulator
foldrK f b (x ∷ xs) = step (                     -- 1 tel per element
  bind-tel (foldrK f b xs) λ acc →
  f x acc)

-- Successor in Kleisli — pure, costs 0 tel
sucK : ℕ →K ℕ
sucK n = return-tel (suc n)

-- Curried addition in Kleisli — pure, costs 0 tel
plusK : ℕ → ℕ →K ℕ
plusK m n = return-tel (m + n)

-- Composition: map suc, then fold with addition.
--
--   sumOfSuc [1,2,3]
--     = foldrK (+) 0 (mapK suc [1,2,3])     -- two phases
--     = foldrK (+) 0 [2,3,4]                 -- after map: 3 tel consumed
--     = 2 + (3 + (4 + 0))                    -- fold:      3 tel consumed
--     = 9                                     -- total:     6 tel consumed
--
-- Tel cost: n steps for mapK + n steps for foldrK = 2n steps.
-- For list of length n: needs tel ≥ 2n.  Remaining = t₀ − 2n.

sumOfSuc : List ℕ →K ℕ
sumOfSuc xs =
  bind-tel (mapK sucK xs)  λ ys →    -- Phase 1: map suc
  foldrK plusK 0 ys                    -- Phase 2: fold (+) 0

-- ── Running examples ────────────────────────────────────────────────
-- To evaluate in Agda: C-c C-n on any of these names.

-- tel = 2n + 1 throughout: always leaves exactly 1 tel remaining
sumOfSuc-empty : Result ℕ ;  sumOfSuc-empty = run (sumOfSuc []) 1
-- → finished 0 1       (no elements, 0 steps)

sumOfSuc-1 : Result ℕ ;  sumOfSuc-1 = run (sumOfSuc (1 ∷ [])) 3
-- → finished 2 1       (suc 1 = 2, sum [2] = 2)

sumOfSuc-123 : Result ℕ ;  sumOfSuc-123 = run (sumOfSuc (1 ∷ 2 ∷ 3 ∷ [])) 7
-- → finished 9 1       (map suc [1,2,3] = [2,3,4], sum = 9)

sumOfSuc-12345 : Result ℕ ;  sumOfSuc-12345 = run (sumOfSuc (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])) 11
-- → finished 20 1      (map suc [1..5] = [2..6], sum = 20)

-- Out-of-tel example: 5 elements needs 10 steps, giving only 5 → halted
sumOfSuc-starved : Result ℕ
sumOfSuc-starved = run (sumOfSuc (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])) 5

-- ─────────────────────────────────────────────────────────────────────────────
-- § 12.  SUMMARY OF THE SPECIFICATION
-- ─────────────────────────────────────────────────────────────────────────────
--
--  Semantic model   ⟦e : τ⟧  =  Tel → Maybe (⟦τ⟧ × Tel)          (§1)
--
--  Monad            return-tel, bind-tel, step                      (§2)
--
--  Types            unit | bool | nat | A⊗B | A⊕B | A⇒B           (§3)
--
--  Category         A →K B = A → TelM B                            (§4)
--                   idK, ∘K, forkK, exlK, exrK
--
--  Recursion        fix (1 tel per unfolding, fuel pattern)         (§5)
--
--  Complexity       time ≤ t₀,  space = O(t₀)                      (§6)
--
--  Totality         by construction: TelM is total                  (§7)
--
--  Correctness      TCM laws proved (idK left/right identity)       (§8)
--
--  Limited recur.   { x , y , z }  =  limited x y z                (§9)
--
--    limited test body base
--      = fix (λ recur s → bind-tel (test s) (λ b →
--                           if b then body recur s
--                                else base s))
--
--    x (test)  decides whether to keep recursing
--    y (body)  takes recur explicitly; runs when test succeeds
--    z (base)  the answer returned when test fails
--
--  Examples         d2c, isEven  (§10)
--  Fibonacci        fib, fib-0..fib-10, fib-10-starved  (§11)
--
-- Key design decisions (following Elliott):
--  • Model chosen first (TelM); all instances derived homomorphically.
--  • fix is the ONLY recursion primitive; tel enforces totality.
--  • { x , y , z } is NOT a new primitive — it is derived from fix.
--  • Time and space bounds are read off directly from the initial tel.
--  • Swapping the category gives different interpretations of the same
--    program (execution, cost analysis, tracing) — "Compiling to Categories".

-- ─────────────────────────────────────────────────────────────────────────────
-- § 14.  FELIX INTEGRATION  (github.com/conal/felix)
--
--  Felix is Conal Elliott's Agda library for category-theoretic denotational
--  design. It provides formal interfaces — Category, Cartesian, CategoryH —
--  that our Kleisli category of TelM already satisfies.
--
--  Here we instantiate those interfaces, making the connection explicit:
--
--    FR.Category  _→K_   — raw category (idK and ∘K)
--    FR.Cartesian _→K_   — Cartesian structure (forkK, exlK, exrK)
--    FL.Category  _→K_   — lawful category (identity laws + associativity)
--
--  The denotation function ⟦_⟧ : Telomare syntax → _→K_ would be a
--  FL.Homomorphism.CategoryH, making the TCM principle machine-checkable.
-- ─────────────────────────────────────────────────────────────────────────────

import Felix.Object      as FO
import Felix.Equiv       as FE
import Felix.Raw         as FR
import Felix.Laws        as FL
import Felix.Homomorphism as FH

-- 14a.  Products for Set — needed so Felix knows ⊤ and × for objects
instance
  Set-Products : FO.Products Set
  Set-Products = record { ⊤ = ⊤ ; _×_ = _×_ }

-- 14b.  Equivalence on Kleisli morphisms: pointwise propositional equality
--       f ≈ g  iff  ∀ a t → f a t ≡ g a t
instance
  →K-Equiv : FE.Equivalent lzero _→K_
  →K-Equiv = record
    { _≈_   = λ f g → ∀ a t → f a t ≡ g a t
    ; equiv = record
        { refl  = λ _ _ → refl
        ; sym   = λ p a t → sym (p a t)
        ; trans = λ p q a t → trans (p a t) (q a t)
        }
    }

-- 14c.  Raw Category: idK and ∘K satisfy Felix's Category interface
instance
  →K-RawCat : FR.Category _→K_
  →K-RawCat = record { id = idK ; _∘_ = _∘K_ }

-- 14d.  Raw Cartesian: forkK / exlK / exrK satisfy Felix's Cartesian interface
instance
  →K-RawCart : FR.Cartesian _→K_
  →K-RawCart = record { ! = λ _ → return-tel tt ; _▵_ = forkK ; exl = exlK ; exr = exrK }

-- 14e.  Proofs for the lawful Category instance
--
--  We need three lemmas beyond §8's left-id / right-id:
--    Maybe->>=-assoc : monad associativity for Maybe (needed for assoc-tel)
--    assoc-tel       : ((h ∘K g) ∘K f) a t ≡ (h ∘K (g ∘K f)) a t
--    >>=-congˡ       : helper for congruence proof
--    ∘≈-tel          : h ≈ k → f ≈ g → h ∘K f ≈ k ∘K g  (pointwise)

private
  -- Associativity of Kleisli composition by direct case analysis on f a t.
  assoc-tel : {A B C D : Set} {f : A →K B} {g : B →K C} {h : C →K D}
            → ∀ a t → ((h ∘K g) ∘K f) a t ≡ (h ∘K (g ∘K f)) a t
  assoc-tel {f = f} {g} {h} a t with f a t
  ... | nothing       = refl
  ... | just (b , t') with g b t'
  ...   | nothing        = refl
  ...   | just (c , t'') = refl

  -- Congruence of >>= in the first argument (the Maybe value).
  >>=-congˡ : ∀ {α β : Set} (m : Maybe α) {f g : α → Maybe β}
            → (∀ x → f x ≡ g x) → (m >>= f) ≡ (m >>= g)
  >>=-congˡ nothing  _  = refl
  >>=-congˡ (just x) pf = pf x

  -- Congruence of Kleisli composition:
  --   h ≈ k  →  f ≈ g  →  h ∘K f ≈ k ∘K g  (all ≈ are pointwise)
  ∘≈-tel : ∀ {α β γ : Set} {h k : β →K γ} {f g : α →K β}
         → (∀ b t → h b t ≡ k b t)
         → (∀ a t → f a t ≡ g a t)
         → ∀ a t → (h ∘K f) a t ≡ (k ∘K g) a t
  ∘≈-tel {h = h} {g = g} h≈k f≈g a t =
    trans (cong (λ m → m >>= λ { (b , t') → h b t' }) (f≈g a t))
          (>>=-congˡ (g a t) λ { (b , t') → h≈k b t' })

-- 14f.  Lawful Category instance: _→K_ satisfies Felix's Laws.Category
instance
  →K-LawCat : FL.Category _→K_
  →K-LawCat = record
    { identityˡ = λ {_} {_} {f}             → left-id  f
    ; identityʳ = λ {_} {_} {f}             → right-id f
    ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} → assoc-tel {f = f} {g = g} {h = h}
    ; ∘≈        = λ {_} {_} {_} {f} {g} {h} {k} → ∘≈-tel   {h = h} {k = k} {f = f} {g = g}
    }

-- ─────────────────────────────────────────────────────────────────────────────
-- § 15.  DENOTATION HOMOMORPHISM  (the TCM principle, machine-checked)
--
-- We define Telomare's SYNTAX CATEGORY _⇨S_ and prove that the denotation
-- function ⟦_⟧ is a Felix CategoryH (functor) into the Kleisli category _→K_.
--
-- This makes the TCM equations machine-checked:
--
--   ⟦ idS    ⟧ = idK              (F-id,  by definition)
--   ⟦ g ∘S f ⟧ = ⟦g⟧ ∘K ⟦f⟧     (F-∘,   by definition)
--   f ≈S g   ⟹  ⟦f⟧ ≈ ⟦g⟧       (F-cong, proved below)
--
-- Any violation would be an abstraction leak: implementation behaviour
-- diverges from the semantic model, making equational reasoning unsound.
-- ─────────────────────────────────────────────────────────────────────────────

-- 15a.  Syntax morphisms — the free category over Telomare's primitives.
--       Objects are Telomare types (Ty); morphisms are terms-in-context.
infix 0 _⇨S_
data _⇨S_ : Ty → Ty → Set where
  idS   : {A : Ty} → A ⇨S A
  _∘S_  : {A B C : Ty} → (B ⇨S C) → (A ⇨S B) → (A ⇨S C)
  !S    : {A : Ty} → A ⇨S unit
  forkS : {A B C : Ty} → (A ⇨S B) → (A ⇨S C) → (A ⇨S (B ⊗ C))
  exlS  : {A B : Ty} → (A ⊗ B) ⇨S A
  exrS  : {A B : Ty} → (A ⊗ B) ⇨S B

-- 15b.  Syntactic equivalence — the equational theory of the syntax category.
--       Identifies morphisms up to the category laws (identity, associativity,
--       congruence) without collapsing to propositional equality on terms.
infix 4 _≈S_
data _≈S_ : {A B : Ty} → (A ⇨S B) → (A ⇨S B) → Set where
  reflS   : {A B : Ty} {f : A ⇨S B}
          → f ≈S f
  symS    : {A B : Ty} {f g : A ⇨S B}
          → f ≈S g → g ≈S f
  transS  : {A B : Ty} {f g h : A ⇨S B}
          → f ≈S g → g ≈S h → f ≈S h
  -- Category laws (generating the equational theory)
  ∘-idlS  : {A B : Ty} {f : A ⇨S B}
          → (idS ∘S f) ≈S f
  ∘-idrS  : {A B : Ty} {f : A ⇨S B}
          → (f ∘S idS) ≈S f
  ∘-assS  : {A B C D : Ty} {f : A ⇨S B} {g : B ⇨S C} {h : C ⇨S D}
          → ((h ∘S g) ∘S f) ≈S (h ∘S (g ∘S f))
  ∘-congS : {A B C : Ty} {f f' : A ⇨S B} {g g' : B ⇨S C}
          → g ≈S g' → f ≈S f' → (g ∘S f) ≈S (g' ∘S f')

-- 15c.  Denotation of syntax morphisms into the Kleisli category.
--       ⟦_⟧ maps each syntactic term to its semantic Kleisli morphism.
⟦_⟧ : {A B : Ty} → (A ⇨S B) → (⟦ A ⟧T →K ⟦ B ⟧T)
⟦ idS        ⟧ = idK
⟦ g ∘S f     ⟧ = ⟦ g ⟧ ∘K ⟦ f ⟧
⟦ !S         ⟧ = λ _ → return-tel tt
⟦ forkS f g  ⟧ = forkK ⟦ f ⟧ ⟦ g ⟧
⟦ exlS       ⟧ = exlK
⟦ exrS       ⟧ = exrK

-- 15d.  Felix instances for the syntax category.

-- Equivalence: use the syntactic equational theory as the setoid.
instance
  ⇨S-Equiv : FE.Equivalent lzero _⇨S_
  ⇨S-Equiv = record
    { _≈_   = _≈S_
    ; equiv = record { refl = reflS ; sym = symS ; trans = transS }
    }

-- Raw category: idS and _∘S_ directly.
instance
  ⇨S-RawCat : FR.Category _⇨S_
  ⇨S-RawCat = record { id = idS ; _∘_ = _∘S_ }

-- Lawful category: the syntactic laws are the constructors of _≈S_.
instance
  ⇨S-LawCat : FL.Category _⇨S_
  ⇨S-LawCat = record
    { identityˡ = λ {_} {_} {f}             → ∘-idlS  {f = f}
    ; identityʳ = λ {_} {_} {f}             → ∘-idrS  {f = f}
    ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} → ∘-assS  {f = f} {g = g} {h = h}
    ; ∘≈        = λ {_} {_} {_} {f} {g} {h} {k} → ∘-congS {f = f} {f' = g} {g = h} {g' = k}
    }

-- 15e.  Homomorphism structure.

-- Object map: Ty → Set via ⟦_⟧T.
instance
  Ty→Set-Hₒ : FH.Homomorphismₒ Ty Set
  Ty→Set-Hₒ = record { Fₒ = ⟦_⟧T }

-- Morphism map: _⇨S_ → _→K_ via ⟦_⟧.
instance
  ⟦⟧-H : FH.Homomorphism _⇨S_ _→K_
  ⟦⟧-H = record { Fₘ = ⟦_⟧ }

-- 15f.  ⟦_⟧ preserves syntactic equivalence (F-cong).
--       Each constructor of _≈S_ maps to the corresponding law on _→K_.
⟦⟧-cong : {A B : Ty} {f g : A ⇨S B}
         → f ≈S g
         → ∀ a t → ⟦ f ⟧ a t ≡ ⟦ g ⟧ a t
⟦⟧-cong reflS                               a t = refl
⟦⟧-cong (symS p)                            a t = sym   (⟦⟧-cong p a t)
⟦⟧-cong (transS p q)                        a t = trans (⟦⟧-cong p a t) (⟦⟧-cong q a t)
⟦⟧-cong (∘-idlS  {f = f})                  a t = left-id  ⟦ f ⟧ a t
⟦⟧-cong (∘-idrS  {f = f})                  a t = right-id ⟦ f ⟧ a t
⟦⟧-cong (∘-assS  {f = f} {g = g} {h = h})  a t = assoc-tel {f = ⟦ f ⟧} {g = ⟦ g ⟧} {h = ⟦ h ⟧} a t
⟦⟧-cong (∘-congS {f = f} {f' = f'} {g = g} {g' = g'} p q) a t =
  ∘≈-tel {h = ⟦ g ⟧} {k = ⟦ g' ⟧} {f = ⟦ f ⟧} {g = ⟦ f' ⟧} (⟦⟧-cong p) (⟦⟧-cong q) a t

-- 15g.  THE HOMOMORPHISM THEOREM.
--       ⟦_⟧ is a CategoryH — a functor from the syntax category to _→K_.
--
--       F-id and F-∘ hold by DEFINITION (refl): the denotation of idS is idK,
--       and the denotation of composition IS Kleisli composition.
--       F-cong is proved by induction on the syntactic equivalence above.
instance
  ⟦⟧-CategoryH : FH.CategoryH _⇨S_ _→K_
  ⟦⟧-CategoryH = record
    { F-cong = ⟦⟧-cong
    ; F-id   = λ _ _ → refl    -- ⟦ idS ⟧ = idK,          definitionally
    ; F-∘    = λ _ _ → refl    -- ⟦ g ∘S f ⟧ = ⟦g⟧ ∘K ⟦f⟧, definitionally
    }

-- ─────────────────────────────────────────────────────────────────────────────
-- § 13.  MAIN  (run fibonacci results via GHC backend)
-- ─────────────────────────────────────────────────────────────────────────────

open import IO            using (IO; putStrLn; Main)
open import Data.Nat.Show using (show)
open import Data.String   using (String; _++_)

showVal : Result ℕ → String
showVal halted          = "?"
showVal (finished v _)  = show v

showResultRow : String → Result ℕ → String
showResultRow label r = label ++ " = " ++ showVal r
                ++ "  [tel remaining: " ++ telLeft r ++ "]"
  where
    telLeft : Result ℕ → String
    telLeft halted          = "exhausted"
    telLeft (finished _ g)  = show g

main : Main
main = IO.run
  (putStrLn "Fibonacci sequence (fib 0 .. fib 10):"                IO.>>
   putStrLn (showResultRow "fib( 0)" fib-0)   IO.>>
   putStrLn (showResultRow "fib( 1)" fib-1)   IO.>>
   putStrLn (showResultRow "fib( 2)" fib-2)   IO.>>
   putStrLn (showResultRow "fib( 3)" fib-3)   IO.>>
   putStrLn (showResultRow "fib( 4)" fib-4)   IO.>>
   putStrLn (showResultRow "fib( 5)" fib-5)   IO.>>
   putStrLn (showResultRow "fib( 6)" fib-6)   IO.>>
   putStrLn (showResultRow "fib( 7)" fib-7)   IO.>>
   putStrLn (showResultRow "fib( 8)" fib-8)   IO.>>
   putStrLn (showResultRow "fib( 9)" fib-9)   IO.>>
   putStrLn (showResultRow "fib(10)" fib-10)  IO.>>
   putStrLn ""                                                       IO.>>
   putStrLn ("Out-of-tel: fib(10) with tel 5 → " ++ showVal fib-10-starved)
                                                                     IO.>>
   putStrLn ""                                                       IO.>>
   putStrLn "Sum of successors — sumOfSuc xs = foldr (+) 0 (map suc xs):"  IO.>>
   putStrLn (showResultRow "sumOfSuc []"          sumOfSuc-empty)    IO.>>
   putStrLn (showResultRow "sumOfSuc [1]"         sumOfSuc-1)        IO.>>
   putStrLn (showResultRow "sumOfSuc [1,2,3]"     sumOfSuc-123)      IO.>>
   putStrLn (showResultRow "sumOfSuc [1,2,3,4,5]" sumOfSuc-12345)   IO.>>
   putStrLn ""                                                       IO.>>
   putStrLn ("Out-of-tel: sumOfSuc [1..5] with tel 5 → " ++ showVal sumOfSuc-starved))
