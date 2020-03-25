module Lvl where

open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (lzero to 𝟎; lsuc to 𝐒)

-- Wraps a lower level set in a higher level wrapper set.
record Up {ℓ₁ ℓ₂} (T : Set(ℓ₁)) : Set(ℓ₁ ⊔ ℓ₂) where
  constructor up
  field obj : T

of : ∀{ℓ} → Set(ℓ) → Level
of {ℓ} _ = ℓ
