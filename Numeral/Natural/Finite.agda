module Numeral.Natural.Finite where

import Level as Lvl
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Structure.Function.Domain
open import Type

-- The finite set of natural numbers (0,..,n).
-- Positive integers including zero less than a specified integer.
data Finite-ℕ : ℕ → Set where
  Finite-𝟎 : ∀{n} → Finite-ℕ(n)                   -- Zero
  Finite-𝐒 : ∀{n} → Finite-ℕ(n) → Finite-ℕ(𝐒(n)) -- Successor function

-- Definition of a finite set/type
Finite : ∀{ℓ₁ ℓ₂} → Type{ℓ₂} → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
Finite {ℓ₁}{ℓ₂} (T) = ∃{ℓ₁ Lvl.⊔ ℓ₂}{Lvl.𝟎}{ℕ}(n ↦ (∃{ℓ₁}{ℓ₂}{T → Finite-ℕ(n)}(f ↦ Injective{ℓ₁}(f))))
-- TODO: Create a module Relator.Injection like Relator.Bijection
