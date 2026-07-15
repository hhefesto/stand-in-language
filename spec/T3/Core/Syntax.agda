------------------------------------------------------------------------
-- T3.Core.Syntax — morphisms of the Telomare core category E.
--
-- Core morphisms:
--
--   * assocS/unassocS/lunitS — value-trivial affine SMC plumbing the
--     point-free examples need.
--   * whileS — fuel + test iteration. Its test probes the loop state
--     WITHOUT consuming it — an implicit copy, priced by the graded
--     semantics (chargeProbe in T3.Sem.Graded), never smuggled for free.
--   * guardS — the ⊕-error refinement primitive: run a predicate over the
--     input, pass it through on inj₁, error on inj₂.  Same implicit-copy
--     pricing as whileS's probe.  This is the core target of surface
--     refinements (charter §2.9); refinement failure is an error VALUE.
--
-- The affine discipline: weakening (weakS, exlS, exrS) is free; there is NO fork and NO dup on
-- ordinary objects — contraction exists only at !A (dupS) and, as a
-- measured-justified exemption, at machine atoms (dupNatS).
--
-- The EAL exponential is dupS/boxS/boxValS/mergeS and NOTHING ELSE:
--   der : !A ⇨ A   and   dig : !A ⇨ !!A   deliberately DO NOT EXIST.
-- Their absence is what fixes box depth before reduction.
--
-- boxValS soundness (easy to get
-- wrong): promotion is EMPTY-CONTEXT only, (unit ⇨ B) → (unit ⇨ !B).
-- A general A ⇨ !A would smuggle contraction: dupS ∘ boxVal would copy an
-- unboxed open input.
--
-- Decision: foldS keeps the pragmatic typing
-- (elements consumed affinely from the orchestration level).  The faithful
-- story stratifies the list type itself; milestone M5's length-space model
-- is the arbiter — if this typing admits no realizer there, the list must
-- stratify.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Core.Syntax where

open import Data.Nat using (ℕ; suc; _⊔_)

open import T3.Core.Ty

infixr 2 _⇨_
infixr 9 _∘S_

data _⇨_ : Ty → Ty → Set where
  -- category
  idS      : {A : Ty} → A ⇨ A
  _∘S_     : {A B C : Ty} → B ⇨ C → A ⇨ B → A ⇨ C
  -- affine symmetric monoidal
  _⊗S_     : {A B C D : Ty} → A ⇨ B → C ⇨ D → (A ⊗ C) ⇨ (B ⊗ D)
  swapS    : {A B : Ty} → (A ⊗ B) ⇨ (B ⊗ A)
  assocS   : {A B C : Ty} → ((A ⊗ B) ⊗ C) ⇨ (A ⊗ (B ⊗ C))
  unassocS : {A B C : Ty} → (A ⊗ (B ⊗ C)) ⇨ ((A ⊗ B) ⊗ C)
  exlS     : {A B : Ty} → (A ⊗ B) ⇨ A          -- weakening on the right
  exrS     : {A B : Ty} → (A ⊗ B) ⇨ B          -- weakening on the left
  weakS    : {A : Ty} → A ⇨ unit               -- weakening
  runitS   : {A : Ty} → A ⇨ (A ⊗ unit)         -- unit intro, right
  lunitS   : {A : Ty} → A ⇨ (unit ⊗ A)         -- unit intro, left
  -- coproducts + distributivity
  inlS     : {A B : Ty} → A ⇨ (A ⊕ B)
  inrS     : {A B : Ty} → B ⇨ (A ⊕ B)
  caseS    : {A B C : Ty} → A ⇨ C → B ⇨ C → (A ⊕ B) ⇨ C
  distlS   : {A B C : Ty} → (A ⊗ (B ⊕ C)) ⇨ ((A ⊗ B) ⊕ (A ⊗ C))
  -- data: lists, naturals
  nilS     : {A : Ty} → unit ⇨ listT A
  consS    : {A : Ty} → (A ⊗ listT A) ⇨ listT A
  unconsS  : {A : Ty} → listT A ⇨ (unit ⊕ (A ⊗ listT A))
  natOutS  : nat ⇨ (unit ⊕ nat)                -- costs 1 tel (a real look)
  sucS     : nat ⇨ nat
  addS     : (nat ⊗ nat) ⇨ nat
  constS   : {A : Ty} → ℕ → A ⇨ nat
  dupNatS  : nat ⇨ (nat ⊗ nat)                 -- atom exemption (dup grade 1)
  -- refinement guard (⊕-error primitive; implicit probe copy, priced)
  guardS   : {A : Ty} → A ⇨ (unit ⊕ unit) → A ⇨ (A ⊕ unit)
    -- test convention: inj₁ = pass, inj₂ = fail.
  -- EAL exponential — the ENTIRE duplication interface
  dupS     : {A : Ty} → ! A ⇨ (! A ⊗ ! A)      -- contraction, only at !
  boxS     : {A B : Ty} → A ⇨ B → (! A ⇨ ! B)  -- promotion (functoriality)
  boxValS  : {B : Ty} → unit ⇨ B → (unit ⇨ ! B)
    -- promotion with EMPTY context (see header)
  mergeS   : {A B : Ty} → (! A ⊗ ! B) ⇨ ! (A ⊗ B)
  -- fuel-carrying recursion: the output lives ONE LEVEL DEEPER than the
  -- orchestration (design doc §7).  Fuel is data; totality is manifest.
  mapS     : {A B : Ty} → A ⇨ B → listT A ⇨ ! (listT B)
  iterS    : {A : Ty} → A ⇨ A → (nat ⊗ ! A) ⇨ ! A
  foldS    : {A B : Ty} → (B ⊗ A) ⇨ B → (listT A ⊗ ! B) ⇨ ! B
  whileS   : {A : Ty} → A ⇨ (unit ⊕ unit) → A ⇨ A → (nat ⊗ ! A) ⇨ ! A
    -- test convention: inj₁ = stop, inj₂ = continue.  At most `fuel`
    -- probes; charges per taken step (T3.Sem.Graded chargeStep) plus a
    -- probe charge per test (the implicit copy of the loop state).

-- Box depth: the static number whose fixedness is both theorems (design
-- doc §6).  iterS/foldS/whileS bodies run one level down, hence the suc.
depth : {A B : Ty} → A ⇨ B → ℕ
depth idS           = 0
depth (g ∘S f)      = depth g ⊔ depth f
depth (f ⊗S g)      = depth f ⊔ depth g
depth swapS         = 0
depth assocS        = 0
depth unassocS      = 0
depth exlS          = 0
depth exrS          = 0
depth weakS         = 0
depth runitS        = 0
depth lunitS        = 0
depth inlS          = 0
depth inrS          = 0
depth (caseS l r)   = depth l ⊔ depth r
depth distlS        = 0
depth nilS          = 0
depth consS         = 0
depth unconsS       = 0
depth natOutS       = 0
depth sucS          = 0
depth addS          = 0
depth (constS _)    = 0
depth dupNatS       = 0
depth (guardS t)    = depth t
depth dupS          = 0
depth (boxS f)      = suc (depth f)
depth (boxValS f)   = suc (depth f)
depth mergeS        = 0
depth (mapS f)      = suc (depth f)
depth (iterS f)     = suc (depth f)
depth (foldS f)     = suc (depth f)
depth (whileS t s)  = suc (depth t ⊔ depth s)

-- towerHeight: the coarse, honest cost report ("worst case is a
-- depth-high tower in the size of the level-0 data") [cited: Girard,
-- Danos–Joinet].  NB this is deliberately NOT an instance of the
-- input-indexed graded semantics (T3.Sem.Graded): it is the sup over all
-- inputs — a quotient of the grade, read directly off the syntax.
towerHeight : {A B : Ty} → A ⇨ B → ℕ
towerHeight = depth
