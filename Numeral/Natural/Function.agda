module Numeral.Natural.Function where

open import Numeral.Natural
open import Numeral.Natural.Oper

-- Maximum function
-- Returns the greatest number
max : ℕ → ℕ → ℕ
max a      𝟎      = a
max 𝟎      b      = b
max (𝐒(a)) (𝐒(b)) = 𝐒(max a b)

-- Minimum function
-- Returns the smallest number
min : ℕ → ℕ → ℕ
min a      𝟎      = 𝟎
min 𝟎      b      = 𝟎
min (𝐒(a)) (𝐒(b)) = 𝐒(min a b)
-- min a b = (a + b) −₀ max(a)(b)

-- min and max as binary operators
infixl 100 _[max]_ _[min]_
_[max]_ = max
_[min]_ = min

module Theorems{ℓ} where
  import      Lvl
  open import Functional
  open import Logic.Propositional{ℓ}
  open import Numeral.Natural.Relation{ℓ}
  open import Numeral.Natural.Oper.Properties{ℓ}
  open import Relator.Equals{ℓ}
  open import Relator.Equals.Proofs{ℓ}
  open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}

  max-elementary : ∀{a b} → (max(a)(b) ≡ a + (b −₀ a))
  max-elementary {𝟎}    {𝟎}    = [≡]-intro
  max-elementary {𝟎}    {𝐒(b)} = [≡]-intro
  max-elementary {𝐒(a)} {𝟎}    = [≡]-intro
  max-elementary {𝐒(a)} {𝐒(b)} = [≡]-with(𝐒) (max-elementary {a} {b})

  postulate min-elementary : ∀{a b} → (min(a)(b) ≡ b −₀ (b −₀ a))
  -- min-elementary {𝟎}    {𝟎}    = [≡]-intro
  -- min-elementary {𝟎}    {𝐒(b)} = [≡]-intro
  -- min-elementary {𝐒(a)} {𝟎}    = [≡]-intro
  -- min-elementary {𝐒(a)} {𝐒(b)} = [≡]-with(𝐒) (min-elementary {a} {b})
  -- 𝐒(b) −₀ (𝐒(b) −₀ 𝐒(a))
  -- 𝐒(b) −₀ (b −₀ a)

  -- min-with-max : ∀{a b} → (min(a)(b) ≡ (a + b) −₀ max(a)(b))
  -- min-with-max {a}{b} = [≡]-elimᵣ (max-elementary{a}{b}) {expr ↦ (min(a)(b) ≡ (a + b) −₀ expr)} (min-elementary{a}{b})
  -- (a + b) −₀ max(a)(b)
  -- (a + b) −₀ (a + (b −₀ a))
  -- b −₀ (b −₀ a)

  postulate min-commutativity : Commutativity(min)
  postulate min-associativity : Associativity(min)
  postulate min-orderₗ : ∀{a b} → (min(a)(b) ≤ a)
  postulate min-orderᵣ : ∀{a b} → (min(a)(b) ≤ b)
  postulate min-arg : ∀{a b} → (min(a)(b) ≡ a)∨(min(a)(b) ≡ b)
  postulate min-defₗ : ∀{a b} → (a ≤ b) → (min(a)(b) ≡ a)
  postulate min-defᵣ : ∀{a b} → (b ≤ a) → (min(a)(b) ≡ b)

  postulate max-commutativity : Commutativity(max)
  postulate max-associativity : Associativity(max)
  postulate max-orderₗ : ∀{a b} → (max(a)(b) ≥ a)
  postulate max-orderᵣ : ∀{a b} → (max(a)(b) ≥ b)
  postulate max-arg : ∀{a b} → (max(a)(b) ≡ a)∨(max(a)(b) ≡ b)
  postulate max-defₗ : ∀{a b} → (a ≥ b) → (max(a)(b) ≡ b)
  postulate max-defᵣ : ∀{a b} → (b ≥ a) → (max(a)(b) ≡ a)
