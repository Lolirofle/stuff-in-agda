module Functional.TypeRaise where

import      Lvl
open import Numeral.Natural
open import Type

-- Repeated function type like an n-ary operator.
-- Examples:
--   (a →̂ b)(0) = (b)
--   (a →̂ b)(1) = (a → b)
--   (a →̂ b)(2) = (a → a → b)
--   (a →̂ b)(3) = (a → a → a → b)
--   (a →̂ b)(4) = (a → a → a → a → b)
_→̂_ : ∀{ℓ₁ ℓ₂} → Type{ℓ₁} → Type{ℓ₁ Lvl.⊔ ℓ₂} → ℕ → Type{ℓ₁ Lvl.⊔ ℓ₂}
_→̂_ {ℓ₁}{ℓ₂} A B 𝟎      = B
_→̂_ {ℓ₁}{ℓ₂} A B (𝐒(n)) = A → (_→̂_ {ℓ₁}{ℓ₂} A B n)

