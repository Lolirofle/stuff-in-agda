module Lvl where

open import Type

open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (lzero to 𝟎; lsuc to 𝐒)

private variable ℓ : Level

-- Wraps a lower level set in a higher level wrapper set.
record Up {ℓ₁ ℓ₂} (T : Type{ℓ₁}) : Type{ℓ₁ ⊔ ℓ₂} where
  constructor up
  field obj : T

of : Type{ℓ} → Level
of {ℓ} _ = ℓ

of-type : Type{𝐒(ℓ)} → Level
of-type {ℓ} _ = ℓ
