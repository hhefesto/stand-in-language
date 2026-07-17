------------------------------------------------------------------------
-- Costed data copy: correctness of the copyS primitive.
--
-- Copyable evidence lives in T3.Core.Ty (every first-order data type is
-- copyable; future non-data objects will not be).  copyS is a primitive
-- core constructor (T3.Core.Syntax) rather than a derived term because a
-- structural list copy is not derivable at level 0 — the old derivation
-- (dupNatS/dupS leaves + shuffle) only reached Unit/Nat/products/bang.
-- The primitive charges its full sizeT in the dup grade; value semantics
-- makes it an honest pair.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Core.Copyable where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value

copyS-correct : {A : Ty} → (p : Copyable A) → (a : ⟦ A ⟧T)
              → ⟦ copyS p ⟧V a ≡ (a , a)
copyS-correct _ _ = refl
