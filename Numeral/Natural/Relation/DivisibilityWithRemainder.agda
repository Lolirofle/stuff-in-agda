module Numeral.Natural.Relation.DivisibilityWithRemainder where

import      Lvl
open import Logic
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Type

-- Divisibility with a remainder.
-- `(y ∣ x)(r)` means that `y` is divisible by `x − r` when all variables are interpreted as being in ℤ.
-- Note: `(0 ∣ᵣₑₘ _)(_)` is impossible to construct (0 is never a divisor by this definition).
data _∣ᵣₑₘ_ : (y : ℕ) → ℕ → 𝕟(y) → Stmt{Lvl.𝟎} where
  DivRem𝟎 : ∀{y : ℕ}  {r : 𝕟(y)} → (y ∣ᵣₑₘ toℕ(r))(r)
  DivRem𝐒 : ∀{y x : ℕ}{r : 𝕟(y)} → (y ∣ᵣₑₘ x)(r) → (y ∣ᵣₑₘ (x + y))(r)

_∣₊_ : ℕ → ℕ → Stmt
𝟎    ∣₊ x = ⊥
𝐒(y) ∣₊ x = (𝐒(y) ∣ᵣₑₘ x)(𝟎)

-- The quotient extracted from a proof of divisibility with a remainder.
[∣ᵣₑₘ]-quotient : ∀{y x}{r} → (y ∣ᵣₑₘ x)(r) → ℕ
[∣ᵣₑₘ]-quotient DivRem𝟎     = 𝟎
[∣ᵣₑₘ]-quotient (DivRem𝐒 p) = 𝐒([∣ᵣₑₘ]-quotient p)

-- The remainder extracted from a proof of divisibility with a remainder.
[∣ᵣₑₘ]-remainder : ∀{y x}{r} → (y ∣ᵣₑₘ x)(r) → 𝕟(y)
[∣ᵣₑₘ]-remainder{r = r} _ = r

{- TODO: Is this correct
data _∣ᵣₑₘ₀_ : ℕ → ℕ → ℕ → Stmt{Lvl.𝟎} where
  zero : ∀{y}    → (y ∣ᵣₑₘ₀ 𝟎)(𝟎)
  step : ∀{y x r}  → (y ∣ᵣₑₘ₀ x)(r) → (y ∣ᵣₑₘ₀ 𝐒(x))(𝐒(r))
  add  : ∀{y x r} → (y ∣ᵣₑₘ₀ x)(r) → (y ∣ᵣₑₘ₀ (x + y))(r)

open import Relator.Equals

test : ∀{y x r} → (p q : (y ∣ᵣₑₘ₀ x)(r)) → (p ≡ q)
test p q = {!!}
-}
