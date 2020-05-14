module Type {ℓ} where

Type : _
Type = Set(ℓ)

-- Assures that a value has a certain type
type-ascript : (T : Type) → T → T
type-ascript T x = x

infixl 10 type-ascript
syntax type-ascript T x = x :of: T

-- Returns the type of a certain value
type-of : ∀{T : Type} → T → Type
type-of {T} _ = T

open import Agda.Primitive public
  using ()
  renaming (Setω to Typeω)

