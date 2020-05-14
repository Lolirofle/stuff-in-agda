module Syntax.Do where

import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A B : Type{ℓ}

record DoNotation (F : Type{ℓ₁} → Type{ℓ₂}) : Type{Lvl.𝐒(ℓ₁) ⊔ ℓ₂} where
  constructor intro
  field
    return : A → F(A)
    _>>=_  : F(A) → (A → F(B)) → F(B)
open DoNotation ⦃ … ⦄ public
