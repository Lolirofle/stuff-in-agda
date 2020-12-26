module Type.Isomorphism where

open import Functional
import      Lvl
open import Structure.Setoid.WithLvl
open import Structure.Function.Domain hiding (inverseₗ ; inverseᵣ)
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level

module _
  (A : Type{ℓ₁})
  (B : Type{ℓ₂})
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  where

  record _≅_ : Type{ℓ₁ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₑ₂} where
    field
      left  : A ← B
      right : A → B
      ⦃ inverseₗ ⦄ : Inverseₗ(right)(left)
      ⦃ inverseᵣ ⦄ : Inverseᵣ(right)(left)
