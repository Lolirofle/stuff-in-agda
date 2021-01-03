module Data.Either.Equiv where

import      Lvl
open import Data.Either as Either
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Operator
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B : Type{ℓ}

record Extensionality ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (equiv : Equiv{ℓₑ}(A ‖ B)) : Type{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₑ} where
  constructor intro
  private instance _ = equiv
  field
     ⦃ Left-function ⦄  : Function Left
     ⦃ Right-function ⦄ : Function Right
     ⦃ Left-injective ⦄   : Injective Left
     ⦃ Right-injective ⦄  : Injective Right
     Left-Right-inequality : ∀{x : A}{y : B} → (Left x ≢ Right y)
