------------------------------------------------------------------------
-- T3.Compiler.ClosedRecursion -- closed recursion placement.
--
-- This module formalizes only the categorical translation used by the
-- constrained source slice. It does not model or make claims about parsing,
-- free-variable checking, module loading, or the Haskell implementation.
-- Seeds, fold inputs, loop bodies/tests, and final continuations arrive with
-- Direct evidence; consequently every promotion below has empty context.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Compiler.ClosedRecursion where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value
open import T3.Surface.Ty
open import T3.Surface.Syntax
open import T3.Surface.Sem
open import T3.Place using (ε; ε-factor)
open import T3.Compiler.Direct using (Direct; direct-erases)

-- Literal-bounded iteration from an empty-context seed, followed by a
-- continuation promoted functorially over the boxed result.
closedIterS : {A C : Ty}
            → ℕ → (unit ⇨ A) → (A ⇨ A) → (A ⇨ C) → (unit ⇨ ! C)
closedIterS {A} {C} n seed step cont =
  boxS {A} {C} cont ∘S iterS {A} step
    ∘S (constS {unit} n ⊗S boxValS {A} seed) ∘S runitS

closedIterU : {A C : Ty}
            → ℕ
            → (unitᵤ ⇨U strip A)
            → (strip A ⇨U strip A)
            → (strip A ⇨U strip C)
            → (unitᵤ ⇨U strip C)
closedIterU {A} n seed step cont =
  cont ∘U iterU {strip A} step
    ∘U (constU {unitᵤ} n ⊗U seed) ∘U runitU

closedIter-erases
  : {A C : Ty} (n : ℕ)
    {seedU : unitᵤ ⇨U strip A} {stepU : strip A ⇨U strip A}
    {contU : strip A ⇨U strip C}
    {seedS : unit ⇨ A} {stepS : A ⇨ A} {contS : A ⇨ C}
  → Direct seedU seedS → Direct stepU stepS → Direct contU contS
  → ε (closedIterS {A} {C} n seedS stepS contS)
    ≡ closedIterU {A} {C} n seedU stepU contU
closedIter-erases {A} {C} n dseed dstep dcont
  rewrite direct-erases {A = unit} {B = A} dseed
        | direct-erases {A = A} {B = A} dstep
        | direct-erases {A = A} {B = C} dcont = refl

closedIter-factor
  : {A C : Ty} (n : ℕ)
    {seedU : unitᵤ ⇨U strip A} {stepU : strip A ⇨U strip A}
    {contU : strip A ⇨U strip C}
    {seedS : unit ⇨ A} {stepS : A ⇨ A} {contS : A ⇨ C}
  → (dseed : Direct seedU seedS) (dstep : Direct stepU stepS)
  → (dcont : Direct contU contS) → (u : ⟦ unit ⟧T)
  → stripV (! C) (⟦ closedIterS {A} {C} n seedS stepS contS ⟧V u)
    ≡ ⟦ closedIterU {A} {C} n seedU stepU contU ⟧VS (stripV unit u)
closedIter-factor {A} {C} n {seedS = seedS} {stepS} {contS}
                  dseed dstep dcont u =
  trans (ε-factor (closedIterS {A} {C} n seedS stepS contS) u)
    (cong (λ h → ⟦ h ⟧VS (stripV unit u))
      (closedIter-erases {A} {C} n dseed dstep dcont))

-- Closed list fold. Elements remain at orchestration level, matching foldS;
-- only the accumulator seed and result are boxed.
closedFoldS : {A B C : Ty}
            → (unit ⇨ listT A) → (unit ⇨ B)
            → ((B ⊗ A) ⇨ B) → (B ⇨ C) → (unit ⇨ ! C)
closedFoldS {A} {B} {C} input seed step cont =
  boxS {B} {C} cont ∘S foldS {A} {B} step
    ∘S (input ⊗S boxValS {B} seed) ∘S runitS

closedFoldU : {A B C : Ty}
            → (unitᵤ ⇨U listᵤ (strip A)) → (unitᵤ ⇨U strip B)
            → ((strip B ⊗ᵤ strip A) ⇨U strip B)
            → (strip B ⇨U strip C) → (unitᵤ ⇨U strip C)
closedFoldU {A} {B} input seed step cont =
  cont ∘U foldU {strip A} {strip B} step
    ∘U (input ⊗U seed) ∘U runitU

closedFold-erases
  : {A B C : Ty}
    {inputU : unitᵤ ⇨U listᵤ (strip A)} {seedU : unitᵤ ⇨U strip B}
    {stepU : (strip B ⊗ᵤ strip A) ⇨U strip B}
    {contU : strip B ⇨U strip C}
    {inputS : unit ⇨ listT A} {seedS : unit ⇨ B}
    {stepS : (B ⊗ A) ⇨ B} {contS : B ⇨ C}
  → Direct inputU inputS → Direct seedU seedS
  → Direct stepU stepS → Direct contU contS
  → ε (closedFoldS {A} {B} {C} inputS seedS stepS contS)
    ≡ closedFoldU {A} {B} {C} inputU seedU stepU contU
closedFold-erases {A} {B} {C} dinput dseed dstep dcont
  rewrite direct-erases {A = unit} {B = listT A} dinput
        | direct-erases {A = unit} {B = B} dseed
        | direct-erases {A = B ⊗ A} {B = B} dstep
        | direct-erases {A = B} {B = C} dcont = refl

closedFold-factor
  : {A B C : Ty}
    {inputU : unitᵤ ⇨U listᵤ (strip A)} {seedU : unitᵤ ⇨U strip B}
    {stepU : (strip B ⊗ᵤ strip A) ⇨U strip B}
    {contU : strip B ⇨U strip C}
    {inputS : unit ⇨ listT A} {seedS : unit ⇨ B}
    {stepS : (B ⊗ A) ⇨ B} {contS : B ⇨ C}
  → (dinput : Direct inputU inputS) (dseed : Direct seedU seedS)
  → (dstep : Direct stepU stepS) (dcont : Direct contU contS)
  → (u : ⟦ unit ⟧T)
  → stripV (! C)
      (⟦ closedFoldS {A} {B} {C} inputS seedS stepS contS ⟧V u)
    ≡ ⟦ closedFoldU {A} {B} {C} inputU seedU stepU contU ⟧VS
      (stripV unit u)
closedFold-factor {A} {B} {C} {inputS = inputS} {seedS} {stepS} {contS}
                  dinput dseed dstep dcont u =
  trans (ε-factor (closedFoldS {A} {B} {C} inputS seedS stepS contS) u)
    (cong (λ h → ⟦ h ⟧VS (stripV unit u))
      (closedFold-erases {A} {B} {C} dinput dseed dstep dcont))

-- Literal-capped closed while. inj1 stops and inj2 continues, as specified by
-- whileS/whileU; the test and step are direct, non-promoted morphisms.
closedWhileS : {A C : Ty}
             → ℕ → (unit ⇨ A) → (A ⇨ (unit ⊕ unit))
             → (A ⇨ A) → (A ⇨ C) → (unit ⇨ ! C)
closedWhileS {A} {C} n seed test step cont =
  boxS {A} {C} cont ∘S whileS {A} test step
    ∘S (constS {unit} n ⊗S boxValS {A} seed) ∘S runitS

closedWhileU : {A C : Ty}
             → ℕ → (unitᵤ ⇨U strip A)
             → (strip A ⇨U (unitᵤ ⊕ᵤ unitᵤ))
             → (strip A ⇨U strip A) → (strip A ⇨U strip C)
             → (unitᵤ ⇨U strip C)
closedWhileU {A} n seed test step cont =
  cont ∘U whileU {strip A} test step
    ∘U (constU {unitᵤ} n ⊗U seed) ∘U runitU

closedWhile-erases
  : {A C : Ty} (n : ℕ)
    {seedU : unitᵤ ⇨U strip A}
    {testU : strip A ⇨U (unitᵤ ⊕ᵤ unitᵤ)}
    {stepU : strip A ⇨U strip A} {contU : strip A ⇨U strip C}
    {seedS : unit ⇨ A} {testS : A ⇨ (unit ⊕ unit)}
    {stepS : A ⇨ A} {contS : A ⇨ C}
  → Direct seedU seedS → Direct testU testS
  → Direct stepU stepS → Direct contU contS
  → ε (closedWhileS {A} {C} n seedS testS stepS contS)
    ≡ closedWhileU {A} {C} n seedU testU stepU contU
closedWhile-erases {A} {C} n dseed dtest dstep dcont
  rewrite direct-erases {A = unit} {B = A} dseed
        | direct-erases {A = A} {B = unit ⊕ unit} dtest
        | direct-erases {A = A} {B = A} dstep
        | direct-erases {A = A} {B = C} dcont = refl

closedWhile-factor
  : {A C : Ty} (n : ℕ)
    {seedU : unitᵤ ⇨U strip A}
    {testU : strip A ⇨U (unitᵤ ⊕ᵤ unitᵤ)}
    {stepU : strip A ⇨U strip A} {contU : strip A ⇨U strip C}
    {seedS : unit ⇨ A} {testS : A ⇨ (unit ⊕ unit)}
    {stepS : A ⇨ A} {contS : A ⇨ C}
  → (dseed : Direct seedU seedS) (dtest : Direct testU testS)
  → (dstep : Direct stepU stepS) (dcont : Direct contU contS)
  → (u : ⟦ unit ⟧T)
  → stripV (! C)
      (⟦ closedWhileS {A} {C} n seedS testS stepS contS ⟧V u)
    ≡ ⟦ closedWhileU {A} {C} n seedU testU stepU contU ⟧VS
      (stripV unit u)
closedWhile-factor {A} {C} n {seedS = seedS} {testS} {stepS} {contS}
                   dseed dtest dstep dcont u =
  trans (ε-factor (closedWhileS {A} {C} n seedS testS stepS contS) u)
    (cong (λ h → ⟦ h ⟧VS (stripV unit u))
      (closedWhile-erases {A} {C} n dseed dtest dstep dcont))

-- One MergeS node combines two independently closed boxed results. Repeated
-- application gives the right-associated environment assembled by Haskell.
closedMergeS : {A B : Ty}
             → (unit ⇨ ! A) → (unit ⇨ ! B) → (unit ⇨ ! (A ⊗ B))
closedMergeS {A} {B} left right =
  mergeS {A} {B} ∘S (left ⊗S right) ∘S runitS

closedMergeU : {A B : Ty}
             → (unitᵤ ⇨U strip A) → (unitᵤ ⇨U strip B)
             → (unitᵤ ⇨U (strip A ⊗ᵤ strip B))
closedMergeU {A} {B} left right =
  idU {strip A ⊗ᵤ strip B} ∘U (left ⊗U right) ∘U runitU

closedMerge-erases
  : {A B : Ty}
    {leftS : unit ⇨ ! A} {rightS : unit ⇨ ! B}
    {leftU : unitᵤ ⇨U strip A} {rightU : unitᵤ ⇨U strip B}
  → ε leftS ≡ leftU → ε rightS ≡ rightU
  → ε (closedMergeS {A} {B} leftS rightS)
    ≡ closedMergeU {A} {B} leftU rightU
closedMerge-erases {A} {B} refl refl = refl

closedMerge-factor
  : {A B : Ty}
    {leftS : unit ⇨ ! A} {rightS : unit ⇨ ! B}
    {leftU : unitᵤ ⇨U strip A} {rightU : unitᵤ ⇨U strip B}
  → (hl : ε leftS ≡ leftU) (hr : ε rightS ≡ rightU)
  → (u : ⟦ unit ⟧T)
  → stripV (! (A ⊗ B)) (⟦ closedMergeS {A} {B} leftS rightS ⟧V u)
    ≡ ⟦ closedMergeU {A} {B} leftU rightU ⟧VS (stripV unit u)
closedMerge-factor {A} {B} {leftS = leftS} {rightS} {leftU} {rightU} hl hr u =
  trans (ε-factor (closedMergeS {A} {B} leftS rightS) u)
    (cong (λ h → ⟦ h ⟧VS (stripV unit u))
      (closedMerge-erases {A} {B} {leftS = leftS} {rightS = rightS}
        {leftU = leftU} {rightU = rightU} hl hr))
