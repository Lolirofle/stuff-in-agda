module Type.Dependent where

import      Lvl
open import Type

record Π {ℓ₁ ℓ₂} (A : Type{ℓ₁}) (B : A → Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor intro
  field
    elim : (a : A) → B(a)

record Σ {ℓ₁ ℓ₂} (A : Type{ℓ₁}) (B : A → Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  constructor intro
  field
    elem  : A
    proof : B(elem)
