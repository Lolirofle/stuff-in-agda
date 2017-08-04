module Numeral.Natural.Function where

open import Numeral.Natural
open import Numeral.Natural.Oper

-- Maximum function
-- Returns the greatest number
max : ℕ → ℕ → ℕ
max a b = a + (b −₀ a)

-- Minimum function
-- Returns the smallest number
min : ℕ → ℕ → ℕ
min a b = (a + b) −₀ max(a)(b)

-- min and max as binary operators
infixl 100 _[max]_ _[min]_
_[max]_ = max
_[min]_ = min

module Theorems{ℓ} where
  import      Level as Lvl
  open import Logic.Propositional{ℓ}
  open import Numeral.Natural.Relation{ℓ}
  open import Relator.Equals{ℓ}
  open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}

  postulate min-commutativity : Commutativity(min)
  postulate max-commutativity : Commutativity(max)

  postulate min-associativity : Associativity(min)
  postulate max-associativity : Associativity(max)

  postulate min-orderₗ : ∀{a b} → (min(a)(b) ≤ a)
  postulate max-orderₗ : ∀{a b} → (max(a)(b) ≥ a)

  postulate min-orderᵣ : ∀{a b} → (min(a)(b) ≤ b)
  postulate max-orderᵣ : ∀{a b} → (max(a)(b) ≥ b)

  postulate min-arg : ∀{a b} → (min(a)(b) ≡ a)∨(min(a)(b) ≡ b)
  postulate max-arg : ∀{a b} → (max(a)(b) ≡ a)∨(max(a)(b) ≡ b)

  postulate min-defₗ : ∀{a b} → (a ≤ b) → (min(a)(b) ≡ a)
  postulate max-defₗ : ∀{a b} → (a ≥ b) → (max(a)(b) ≡ b)

  postulate min-defᵣ : ∀{a b} → (b ≤ a) → (min(a)(b) ≡ b)
  postulate max-defᵣ : ∀{a b} → (b ≥ a) → (max(a)(b) ≡ a)
