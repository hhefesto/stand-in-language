------------------------------------------------------------------------
-- T3.Categorical.Interpretation -- conservative T3 instances and squares.
--
-- Raw Core and Surface homs remain syntax trees.  Category equations below
-- hold only under the explicitly supplied value-extensional HomEq.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Categorical.Interpretation where

open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Product using (_×_; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import T3.Categorical.Vocabulary
open import T3.Core.Ty
import T3.Core.Syntax as C
import T3.Sem.Value as V
open import T3.Surface.Ty
import T3.Surface.Syntax as S
import T3.Surface.Sem as SV
import T3.Place as P
import T3.Compiler.Direct as D
import T3.Sem.Graded as G
import T3.Abstract as A

CoreCategoryOps : CategoryOps
CoreCategoryOps = record
  { Obj = Ty
  ; Hom = C._⇨_
  ; id = C.idS
  ; _then_ = λ f g → g C.∘S f
  }

CoreTensorOps : TensorOps CoreCategoryOps
CoreTensorOps = record
  { tensorObj = _⊗_; tensor = C._⊗S_; swap = C.swapS
  ; assoc = C.assocS; unassoc = C.unassocS
  }

CoreAffineOps : AffineOps CoreCategoryOps CoreTensorOps
CoreAffineOps = record
  { unitObj = unit; discard = C.weakS; exl = C.exlS; exr = C.exrS
  ; runit = C.runitS; lunit = C.lunitS
  }

CoreSumOps : SumOps CoreCategoryOps
CoreSumOps = record { sumObj = _⊕_; inl = C.inlS; inr = C.inrS; case = C.caseS }

CoreDistributivityOps : DistributivityOps CoreCategoryOps CoreTensorOps CoreSumOps
CoreDistributivityOps = record { distl = C.distlS }

CoreNatOps : NatOps CoreCategoryOps CoreTensorOps CoreAffineOps CoreSumOps
CoreNatOps = record
  { natObj = nat; natOut = C.natOutS; sucNat = C.sucS
  ; addNat = C.addS; constNat = C.constS
  }

CoreListOps : ListOps CoreCategoryOps CoreTensorOps CoreAffineOps CoreSumOps
CoreListOps = record
  { listObj = listT; nil = C.nilS; cons = C.consS; uncons = C.unconsS }

CoreExceptionalCopyOps : ExceptionalCopyOps CoreCategoryOps CoreTensorOps
CoreExceptionalCopyOps = record { copyObj = nat; copyAt = C.dupNatS }

CoreWitnessedCopyOps : WitnessedCopyOps CoreCategoryOps CoreTensorOps
CoreWitnessedCopyOps = record { CopyWitness = Copyable; copyWith = C.copyS }

CoreBangOps : RestrictedBangOps CoreCategoryOps CoreTensorOps CoreAffineOps
CoreBangOps = record
  { bang = !_; copyBang = C.dupS; mapBang = C.boxS
  ; promoteVal = C.boxValS; mergeBang = C.mergeS
  }

CoreClosureOps : ClosureOps CoreCategoryOps CoreTensorOps
CoreClosureOps = record { lolly = _⊸_; curry = C.curryS; apply = C.applyS }

CoreClosureRecursionOps : ClosureRecursionOps CoreCategoryOps CoreTensorOps
  CoreAffineOps CoreSumOps CoreListOps CoreBangOps CoreClosureOps
CoreClosureRecursionOps = record { mapClosure = C.mapCS }

CoreGuardOps : GuardOps CoreCategoryOps CoreTensorOps CoreAffineOps CoreSumOps
CoreGuardOps = record { guard = C.guardS }

CoreBoundedRecursionOps : BoundedRecursionOps CoreCategoryOps CoreTensorOps
  CoreAffineOps CoreSumOps CoreNatOps CoreListOps CoreBangOps
CoreBoundedRecursionOps = record
  { map = C.mapS; iterate = C.iterS; fold = C.foldS; while = C.whileS }

SurfaceCategoryOps : CategoryOps
SurfaceCategoryOps = record
  { Obj = UTy
  ; Hom = S._⇨U_
  ; id = S.idU
  ; _then_ = λ f g → g S.∘U f
  }

SurfaceTensorOps : TensorOps SurfaceCategoryOps
SurfaceTensorOps = record
  { tensorObj = _⊗ᵤ_; tensor = S._⊗U_; swap = S.swapU
  ; assoc = S.assocU; unassoc = S.unassocU
  }

SurfaceAffineOps : AffineOps SurfaceCategoryOps SurfaceTensorOps
SurfaceAffineOps = record
  { unitObj = unitᵤ; discard = S.weakU; exl = S.exlU; exr = S.exrU
  ; runit = S.runitU; lunit = S.lunitU
  }

SurfaceSumOps : SumOps SurfaceCategoryOps
SurfaceSumOps = record
  { sumObj = _⊕ᵤ_; inl = S.inlU; inr = S.inrU; case = S.caseU }

SurfaceDistributivityOps : DistributivityOps SurfaceCategoryOps
  SurfaceTensorOps SurfaceSumOps
SurfaceDistributivityOps = record { distl = S.distlU }

SurfaceNatOps : NatOps SurfaceCategoryOps SurfaceTensorOps
  SurfaceAffineOps SurfaceSumOps
SurfaceNatOps = record
  { natObj = natᵤ; natOut = S.natOutU; sucNat = S.sucU
  ; addNat = S.addU; constNat = S.constU
  }

SurfaceListOps : ListOps SurfaceCategoryOps SurfaceTensorOps
  SurfaceAffineOps SurfaceSumOps
SurfaceListOps = record
  { listObj = listᵤ; nil = S.nilU; cons = S.consU; uncons = S.unconsU }

SurfaceCopyOps : CopyOps SurfaceCategoryOps SurfaceTensorOps
SurfaceCopyOps = record { copy = S.dupU }

SurfaceClosureOps : ClosureOps SurfaceCategoryOps SurfaceTensorOps
SurfaceClosureOps = record { lolly = _⊸ᵤ_; curry = S.curryU; apply = S.applyU }

-- Surface recursion is box-free, so it is exposed explicitly rather than as
-- an instance of RestrictedBangOps.
record SurfaceBoundedRecursion : Set₁ where
  field
    map     : {X Y : UTy} → X S.⇨U Y → listᵤ X S.⇨U listᵤ Y
    iterate : {X : UTy} → X S.⇨U X → (natᵤ ⊗ᵤ X) S.⇨U X
    fold    : {X Y : UTy} → (Y ⊗ᵤ X) S.⇨U Y
            → (listᵤ X ⊗ᵤ Y) S.⇨U Y
    while   : {X : UTy} → X S.⇨U (unitᵤ ⊕ᵤ unitᵤ) → X S.⇨U X
            → (natᵤ ⊗ᵤ X) S.⇨U X

SurfaceBoundedRecursionOps : SurfaceBoundedRecursion
SurfaceBoundedRecursionOps = record
  { map = S.mapU; iterate = S.iterU; fold = S.foldU; while = S.whileU }

CoreValueInterpretationOps : InterpretationOps CoreCategoryOps
CoreValueInterpretationOps = record { Carrier = ⟦_⟧T; interp = V.⟦_⟧V }

CoreValueInterpretationLaws : InterpretationLaws CoreCategoryOps
  CoreValueInterpretationOps
CoreValueInterpretationLaws = record
  { interp-id = λ _ → refl; interp-then = λ _ _ _ → refl }

CoreValueInterpretation : InterpretationHom CoreCategoryOps
CoreValueInterpretation = record
  { action = CoreValueInterpretationOps; laws = CoreValueInterpretationLaws }

CoreValueEq : HomEq CoreCategoryOps
CoreValueEq = record { _≈_ = λ f g → ∀ a → V.⟦ f ⟧V a ≡ V.⟦ g ⟧V a }

CoreValueEqLaws : HomEqLaws CoreCategoryOps CoreValueEq
CoreValueEqLaws = record
  { ≈-refl = λ _ → refl
  ; ≈-sym = λ h a → sym (h a)
  ; ≈-trans = λ h k a → trans (h a) (k a)
  }

private
  core-then-cong : {X Y Z : Ty} {f f′ : X C.⇨ Y} {g g′ : Y C.⇨ Z}
    → (∀ x → V.⟦ f ⟧V x ≡ V.⟦ f′ ⟧V x)
    → (∀ y → V.⟦ g ⟧V y ≡ V.⟦ g′ ⟧V y)
    → ∀ x → V.⟦ g C.∘S f ⟧V x ≡ V.⟦ g′ C.∘S f′ ⟧V x
  core-then-cong {f′ = f′} {g = g} hf hg x =
    trans (cong V.⟦ g ⟧V (hf x)) (hg (V.⟦ f′ ⟧V x))

CoreValueCategoryLaws : CategoryLaws CoreCategoryOps CoreValueEq
CoreValueCategoryLaws = record
  { identity-left = λ _ _ → refl
  ; identity-right = λ _ _ → refl
  ; associative = λ _ _ _ _ → refl
  ; then-cong = λ {X} {Y} {Z} {f} {f′} {g} {g′} →
      core-then-cong {X} {Y} {Z} {f} {f′} {g} {g′}
  }

SurfaceValueInterpretationOps : InterpretationOps SurfaceCategoryOps
SurfaceValueInterpretationOps = record { Carrier = ⟦_⟧U; interp = SV.⟦_⟧VS }

SurfaceValueInterpretationLaws : InterpretationLaws SurfaceCategoryOps
  SurfaceValueInterpretationOps
SurfaceValueInterpretationLaws = record
  { interp-id = λ _ → refl; interp-then = λ _ _ _ → refl }

SurfaceValueInterpretation : InterpretationHom SurfaceCategoryOps
SurfaceValueInterpretation = record
  { action = SurfaceValueInterpretationOps; laws = SurfaceValueInterpretationLaws }

SurfaceValueEq : HomEq SurfaceCategoryOps
SurfaceValueEq = record { _≈_ = λ f g → ∀ a → SV.⟦ f ⟧VS a ≡ SV.⟦ g ⟧VS a }

SurfaceValueEqLaws : HomEqLaws SurfaceCategoryOps SurfaceValueEq
SurfaceValueEqLaws = record
  { ≈-refl = λ _ → refl
  ; ≈-sym = λ h a → sym (h a)
  ; ≈-trans = λ h k a → trans (h a) (k a)
  }

private
  surface-then-cong : {X Y Z : UTy} {f f′ : X S.⇨U Y} {g g′ : Y S.⇨U Z}
    → (∀ x → SV.⟦ f ⟧VS x ≡ SV.⟦ f′ ⟧VS x)
    → (∀ y → SV.⟦ g ⟧VS y ≡ SV.⟦ g′ ⟧VS y)
    → ∀ x → SV.⟦ g S.∘U f ⟧VS x ≡ SV.⟦ g′ S.∘U f′ ⟧VS x
  surface-then-cong {f′ = f′} {g = g} hf hg x =
    trans (cong SV.⟦ g ⟧VS (hf x)) (hg (SV.⟦ f′ ⟧VS x))

SurfaceValueCategoryLaws : CategoryLaws SurfaceCategoryOps SurfaceValueEq
SurfaceValueCategoryLaws = record
  { identity-left = λ _ _ → refl
  ; identity-right = λ _ _ → refl
  ; associative = λ _ _ _ _ → refl
  ; then-cong = λ {X} {Y} {Z} {f} {f′} {g} {g′} →
      surface-then-cong {X} {Y} {Z} {f} {f′} {g} {g′}
  }

SurfaceSyntaxEq : HomEq SurfaceCategoryOps
SurfaceSyntaxEq = record { _≈_ = _≡_ }

ErasureCategoryHomOps : CategoryHomOps CoreCategoryOps SurfaceCategoryOps
ErasureCategoryHomOps = record { mapObj = strip; mapHom = P.ε }

ErasureCategoryHomLaws : CategoryHomLaws CoreCategoryOps SurfaceCategoryOps
  SurfaceSyntaxEq ErasureCategoryHomOps
ErasureCategoryHomLaws = record
  { map-id = refl; map-then = λ _ _ → refl }

ErasureCategoryHom : CategoryHom CoreCategoryOps SurfaceCategoryOps SurfaceSyntaxEq
ErasureCategoryHom = record
  { action = ErasureCategoryHomOps; laws = ErasureCategoryHomLaws }

-- Erasure preserves the category operations by computation.
erasure-id-hom : {X : Ty} → P.ε (C.idS {X}) ≡ S.idU
erasure-id-hom = refl

erasure-then-hom : {X Y Z : Ty} (f : X C.⇨ Y) (g : Y C.⇨ Z)
                 → P.ε (g C.∘S f) ≡ (P.ε g S.∘U P.ε f)
erasure-then-hom f g = refl

-- The interpretation square for erasure: relational in general
-- (closures), propositional at first-order endpoints.
erasure-value-relates : {X Y : Ty} (f : X C.⇨ Y)
  {x : ⟦ X ⟧T} {u : ⟦ strip X ⟧U}
  → P.≈ε X x u → P.≈ε Y (V.⟦ f ⟧V x) (SV.⟦ P.ε f ⟧VS u)
erasure-value-relates = P.ε-rel

erasure-value-commutes : {X Y : Ty} → P.fo X → P.fo Y
  → (f : X C.⇨ Y) (x : ⟦ X ⟧T)
  → stripV Y (V.⟦ f ⟧V x) ≡ SV.⟦ P.ε f ⟧VS (stripV X x)
erasure-value-commutes = P.ε-factor

-- Direct elaboration is a section of erasure on every successful derivation.
direct-erasure-section : {X Y : Ty} {f : strip X S.⇨U strip Y} {g : X C.⇨ Y}
  → D.Direct f g → P.ε g ≡ f
direct-erasure-section = D.direct-erases

direct-value-square : {X Y : Ty} → P.fo X → P.fo Y
  → {f : strip X S.⇨U strip Y} {g : X C.⇨ Y}
  → D.Direct f g → (x : ⟦ X ⟧T)
  → stripV Y (V.⟦ g ⟧V x) ≡ SV.⟦ f ⟧VS (stripV X x)
direct-value-square = D.direct-factor

-- Every graded interpretation projects homomorphically to value
-- semantics, up to the graded logical relation (equality below arrows).
graded-value-square : (R : G.CostAlgebra) {X Y : Ty} (f : X C.⇨ Y)
  {gx : G.GVal (G.CostAlgebra.ℳ R) X} {x : ⟦ X ⟧T}
  → G.≈G (G.CostAlgebra.ℳ R) X gx x
  → G.≈G (G.CostAlgebra.ℳ R) Y (proj₂ (G.Interp.⟦_⟧G R f gx)) (V.⟦ f ⟧V x)
graded-value-square R = G.Interp.G-val R

-- Fuel precision: bounded while is exactly an iterate using no more fuel.
while-fuel-precision : {X : Set} (n : ℕ) (test : X → ⊤ ⊎ ⊤)
  (step : X → X) (x : X)
  → Σ ℕ (λ k → (k ≤ n) × (V.whileV n test step x ≡ V.iterV k step x))
while-fuel-precision = A.whileV-runs-as-iterV

-- Once a stop verdict is reached, extending fuel commutes with evaluation.
while-fuel-extension : {X : Set} (n k : ℕ) (test : X → ⊤ ⊎ ⊤)
  (step : X → X) (x : X)
  → test (V.whileV n test step x) ≡ inj₁ tt
  → V.whileV (n + k) test step x ≡ V.whileV n test step x
while-fuel-extension = A.while-stable
