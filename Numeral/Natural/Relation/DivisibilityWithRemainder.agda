module Numeral.Natural.Relation.DivisibilityWithRemainder where

import      Lvl
open import Logic
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Type

-- Divisibility with a remainder.
-- `(y ∣ x)(r)` means that `y` is divisible by `x − r`.
-- Note: `(0 ∣ᵣₑₘ _)(_)` is impossible to construct (0 is never a divisor by this definition).
data _∣ᵣₑₘ_ : (y : ℕ) → ℕ → 𝕟(y) → Stmt{Lvl.𝟎} where
  DivRem𝟎 : ∀{y : ℕ}  {r : 𝕟(y)} → (y ∣ᵣₑₘ 𝕟-to-ℕ(r))(r)
  DivRem𝐒 : ∀{y x : ℕ}{r : 𝕟(y)} → (y ∣ᵣₑₘ x)(r) → (y ∣ᵣₑₘ (x + y))(r)

_∣₊_ : ℕ → ℕ → Stmt
𝟎    ∣₊ x = ⊥
𝐒(y) ∣₊ x = (𝐒(y) ∣ᵣₑₘ x)(𝟎)

-- The quotient extracted from the proof of divisibility.
[∣ᵣₑₘ]-quotient : ∀{y x}{r} → (y ∣ᵣₑₘ x)(r) → ℕ
[∣ᵣₑₘ]-quotient DivRem𝟎     = 𝟎
[∣ᵣₑₘ]-quotient (DivRem𝐒 p) = 𝐒([∣ᵣₑₘ]-quotient p)

-- The remainder extracted from the proof of divisibility.
[∣ᵣₑₘ]-remainder : ∀{y x}{r} → (y ∣ᵣₑₘ x)(r) → 𝕟(y)
[∣ᵣₑₘ]-remainder{r = r} _ = r

data _∣ᵣₑₘ₀_ : (y : ℕ) → ℕ → ℕ → Stmt{Lvl.𝟎} where
  base₀ : ∀{y}    → (y ∣ᵣₑₘ₀ 𝟎)(𝟎)
  base₊ : ∀{y r}  → (y ∣ᵣₑₘ₀ r)(r) → (𝐒(y) ∣ᵣₑₘ₀ 𝐒(r))(𝐒(r))
  step : ∀{y x r} → (y ∣ᵣₑₘ₀ x)(r) → (y ∣ᵣₑₘ₀ (x + y))(r)
