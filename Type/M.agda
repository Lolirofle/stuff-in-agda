module Type.M where

import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A : Type{ℓ}
private variable B : A → Type{ℓ}

-- TODO: Is this definition of M correct? Compare with Type.W.
record M (A : Type{ℓ₁}) (B : A → Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  coinductive
  field
    label    : A
    recursor : B(label) → M A B
