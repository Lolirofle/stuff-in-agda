module Lvl where

open import Type

open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (lzero to 𝟎; lsuc to 𝐒)

-- Wraps a lower level set in a higher level wrapper set.
record Up {ℓ₁ ℓ₂} (T : Type{ℓ₂}) : Type{ℓ₁ ⊔ ℓ₂} where
  constructor up
  field obj : T

of : ∀{ℓ} → Type{ℓ} → Level
of {ℓ} _ = ℓ
{-# INLINE of #-}

ofType : ∀{ℓ} → Type{𝐒(ℓ)} → Level
ofType {ℓ} _ = ℓ
{-# INLINE ofType #-}
