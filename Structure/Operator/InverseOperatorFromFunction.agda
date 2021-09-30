module Structure.Operator.InverseOperatorFromFunction where

import      Lvl
open import Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}

-- Constructs a right inverse operator from a operator with an inverse function.
-- Examples:
--   _−_ : ℤ → ℤ → ℤ
--   x − y = x + (− y) = invOpᵣ(_+_)(−_)
--
--   _/_ : ℚ₊ → ℚ₊ → ℚ₊
--   x / y = x ⋅ (⅟ y) = invOpᵣ(_⋅_)(⅟_)
invOpᵣ : (A → B → C) → (B → B) → (A → B → C)
invOpᵣ(_▫_)(inv) x y = x ▫ inv(y)

-- Constructs a left inverse operator from a operator with an inverse function.
invOpₗ : (A → B → C) → (A → A) → (A → B → C)
invOpₗ(_▫_)(inv) x y = inv(x) ▫ y
