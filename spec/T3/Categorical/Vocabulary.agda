------------------------------------------------------------------------
-- T3.Categorical.Vocabulary -- equation-free categorical capabilities.
--
-- Operations and laws are deliberately separate.  In particular, merely
-- constructing a CategoryOps value does not quotient its homs or assert any
-- equations about them.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Categorical.Vocabulary where

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

record CategoryOps : Set₁ where
  infixr 9 _then_
  field
    Obj    : Set
    Hom    : Obj → Obj → Set
    id     : {A : Obj} → Hom A A
    _then_ : {A B C : Obj} → Hom A B → Hom B C → Hom A C

record HomEq (C : CategoryOps) : Set₁ where
  open CategoryOps C
  field
    _≈_ : {A B : Obj} → Hom A B → Hom A B → Set

record HomEqLaws (C : CategoryOps) (E : HomEq C) : Set₁ where
  open CategoryOps C
  open HomEq E
  field
    ≈-refl  : {A B : Obj} {f : Hom A B} → f ≈ f
    ≈-sym   : {A B : Obj} {f g : Hom A B} → f ≈ g → g ≈ f
    ≈-trans : {A B : Obj} {f g h : Hom A B} → f ≈ g → g ≈ h → f ≈ h

record CategoryLaws (C : CategoryOps) (E : HomEq C) : Set₁ where
  open CategoryOps C
  open HomEq E
  field
    identity-left  : {A B : Obj} (f : Hom A B) → (id then f) ≈ f
    identity-right : {A B : Obj} (f : Hom A B) → (f then id) ≈ f
    associative    : {A B C D : Obj}
                   → (f : Hom A B) (g : Hom B C) (h : Hom C D)
                   → ((f then g) then h) ≈ (f then (g then h))
    then-cong      : {A B C : Obj} {f f′ : Hom A B} {g g′ : Hom B C}
                   → f ≈ f′ → g ≈ g′ → (f then g) ≈ (f′ then g′)

record TensorOps (C : CategoryOps) : Set₁ where
  open CategoryOps C
  field
    tensorObj : Obj → Obj → Obj
    tensor    : {A B C D : Obj} → Hom A B → Hom C D
              → Hom (tensorObj A C) (tensorObj B D)
    swap      : {A B : Obj} → Hom (tensorObj A B) (tensorObj B A)
    assoc     : {A B D : Obj}
              → Hom (tensorObj (tensorObj A B) D) (tensorObj A (tensorObj B D))
    unassoc   : {A B D : Obj}
              → Hom (tensorObj A (tensorObj B D)) (tensorObj (tensorObj A B) D)

record AffineOps (C : CategoryOps) (T : TensorOps C) : Set₁ where
  open CategoryOps C
  open TensorOps T
  field
    unitObj : Obj
    discard : {A : Obj} → Hom A unitObj
    exl     : {A B : Obj} → Hom (tensorObj A B) A
    exr     : {A B : Obj} → Hom (tensorObj A B) B
    runit   : {A : Obj} → Hom A (tensorObj A unitObj)
    lunit   : {A : Obj} → Hom A (tensorObj unitObj A)

record SumOps (C : CategoryOps) : Set₁ where
  open CategoryOps C
  field
    sumObj : Obj → Obj → Obj
    inl    : {A B : Obj} → Hom A (sumObj A B)
    inr    : {A B : Obj} → Hom B (sumObj A B)
    case   : {A B D : Obj} → Hom A D → Hom B D → Hom (sumObj A B) D

record DistributivityOps (C : CategoryOps) (T : TensorOps C)
                         (S : SumOps C) : Set₁ where
  open CategoryOps C
  open TensorOps T
  open SumOps S
  field
    distl : {A B D : Obj}
          → Hom (tensorObj A (sumObj B D))
                (sumObj (tensorObj A B) (tensorObj A D))

record NatOps (C : CategoryOps) (T : TensorOps C) (A : AffineOps C T)
              (S : SumOps C) : Set₁ where
  open CategoryOps C
  open TensorOps T
  open AffineOps A
  open SumOps S
  field
    natObj : Obj
    natOut : Hom natObj (sumObj unitObj natObj)
    sucNat : Hom natObj natObj
    addNat : Hom (tensorObj natObj natObj) natObj
    constNat : {X : Obj} → ℕ → Hom X natObj

record ListOps (C : CategoryOps) (T : TensorOps C) (A : AffineOps C T)
               (S : SumOps C) : Set₁ where
  open CategoryOps C
  open TensorOps T
  open AffineOps A
  open SumOps S
  field
    listObj : Obj → Obj
    nil     : {X : Obj} → Hom unitObj (listObj X)
    cons    : {X : Obj} → Hom (tensorObj X (listObj X)) (listObj X)
    uncons  : {X : Obj}
            → Hom (listObj X) (sumObj unitObj (tensorObj X (listObj X)))

record CopyOps (C : CategoryOps) (T : TensorOps C) : Set₁ where
  open CategoryOps C
  open TensorOps T
  field copy : {A : Obj} → Hom A (tensorObj A A)

record ExceptionalCopyOps (C : CategoryOps) (T : TensorOps C) : Set₁ where
  open CategoryOps C
  open TensorOps T
  field
    copyObj : Obj
    copyAt  : Hom copyObj (tensorObj copyObj copyObj)

record RestrictedBangOps (C : CategoryOps) (T : TensorOps C)
                         (A : AffineOps C T) : Set₁ where
  open CategoryOps C
  open TensorOps T
  open AffineOps A
  field
    bang       : Obj → Obj
    copyBang   : {X : Obj} → Hom (bang X) (tensorObj (bang X) (bang X))
    mapBang    : {X Y : Obj} → Hom X Y → Hom (bang X) (bang Y)
    promoteVal : {Y : Obj} → Hom unitObj Y → Hom unitObj (bang Y)
    mergeBang  : {X Y : Obj}
               → Hom (tensorObj (bang X) (bang Y)) (bang (tensorObj X Y))

record GuardOps (C : CategoryOps) (T : TensorOps C) (A : AffineOps C T)
                (S : SumOps C) : Set₁ where
  open CategoryOps C
  open AffineOps A
  open SumOps S
  field guard : {X : Obj} → Hom X (sumObj unitObj unitObj)
              → Hom X (sumObj X unitObj)

record BoundedRecursionOps (C : CategoryOps) (T : TensorOps C)
                           (A : AffineOps C T) (S : SumOps C)
                           (N : NatOps C T A S) (L : ListOps C T A S)
                           (B : RestrictedBangOps C T A) : Set₁ where
  open CategoryOps C
  open TensorOps T
  open AffineOps A
  open SumOps S
  open NatOps N
  open ListOps L
  open RestrictedBangOps B
  field
    map     : {X Y : Obj} → Hom X Y → Hom (listObj X) (bang (listObj Y))
    iterate : {X : Obj} → Hom X X → Hom (tensorObj natObj (bang X)) (bang X)
    fold    : {X Y : Obj} → Hom (tensorObj Y X) Y
            → Hom (tensorObj (listObj X) (bang Y)) (bang Y)
    while   : {X : Obj} → Hom X (sumObj unitObj unitObj) → Hom X X
            → Hom (tensorObj natObj (bang X)) (bang X)

-- An interpretation is also split into its action and its equations.
record InterpretationOps (C : CategoryOps) : Set₁ where
  open CategoryOps C
  field
    Carrier : Obj → Set
    interp  : {A B : Obj} → Hom A B → Carrier A → Carrier B

record InterpretationLaws (C : CategoryOps) (I : InterpretationOps C) : Set₁ where
  open CategoryOps C
  open InterpretationOps I
  field
    interp-id   : {A : Obj} (a : Carrier A) → interp id a ≡ a
    interp-then : {A B D : Obj} (f : Hom A B) (g : Hom B D) (a : Carrier A)
                → interp (f then g) a ≡ interp g (interp f a)

record InterpretationHom (C : CategoryOps) : Set₁ where
  field
    action : InterpretationOps C
    laws   : InterpretationLaws C action

-- A map of equation-free category operations.  Its laws say only that the
-- chosen identity and composition operations are preserved in the target
-- HomEq; they do not manufacture category laws for either raw hom syntax.
record CategoryHomOps (C D : CategoryOps) : Set₁ where
  private
    module C = CategoryOps C
    module D = CategoryOps D
  field
    mapObj : C.Obj → D.Obj
    mapHom : {A B : C.Obj} → C.Hom A B → D.Hom (mapObj A) (mapObj B)

record CategoryHomLaws (C D : CategoryOps) (E : HomEq D)
                       (F : CategoryHomOps C D) : Set₁ where
  private
    module C = CategoryOps C
    module D = CategoryOps D
  open HomEq E
  open CategoryHomOps F
  field
    map-id : {A : C.Obj}
           → mapHom {A} {A} C.id ≈ D.id {mapObj A}
    map-then : {A B Z : C.Obj} (f : C.Hom A B) (g : C.Hom B Z)
             → mapHom (C._then_ f g)
               ≈ D._then_ {mapObj A} {mapObj B} {mapObj Z}
                            (mapHom f) (mapHom g)

record CategoryHom (C D : CategoryOps) (E : HomEq D) : Set₁ where
  field
    action : CategoryHomOps C D
    laws   : CategoryHomLaws C D E action
