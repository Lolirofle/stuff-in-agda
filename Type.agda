module Type{ℓ} where

open import Agda.Primitive public
  using ()
  renaming (Set to TYPE ; Setω to Typeω)

Type : TYPE(_)
Type = TYPE(ℓ)
{-# INLINE Type #-}

module Type where
  -- Returns the type of a certain value
  of : ∀{T : Type} → T → Type
  of {T} _ = T
  {-# INLINE of #-}
