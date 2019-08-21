module Lvl where

open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (lzero to 𝟎; lsuc to 𝐒)

-- Wraps a lower level set in a higher level wrapper set.
data Up {ℓ₁ ℓ₂} (T : Set(ℓ₁)) : Set(ℓ₁ ⊔ ℓ₂) where
  instance up : T → Up(T)
