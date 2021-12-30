module Numeral.Finite.Functions where

import Lvl
open import Syntax.Number
open import Functional.Instance
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural hiding (𝐏)
import      Numeral.Natural.Function as ℕ
import      Numeral.Natural.Function.Proofs as ℕ
open import Numeral.Natural.Oper

-- Maximum function.
-- Returns the greatest number.
max : ∀{a b} → 𝕟(a) → 𝕟(b) → 𝕟(ℕ.max a b)
max        𝟎      𝟎      = 𝟎
max {a}{b} (𝐒(x)) 𝟎      = bound-[≤] ([∧]-elimₗ (ℕ.max-order {a}{b})) (𝐒(x))
max {a}{b} 𝟎      (𝐒(y)) = bound-[≤] ([∧]-elimᵣ (ℕ.max-order {a}{b})) (𝐒(y))
max        (𝐒(x)) (𝐒(y)) = 𝐒(max x y)

-- Minimum function.
-- Returns the smallest number.
min : ∀{a b} → 𝕟(a) → 𝕟(b) → 𝕟(ℕ.min a b)
min 𝟎      𝟎      = 𝟎
min (𝐒(_)) 𝟎      = 𝟎
min 𝟎      (𝐒(_)) = 𝟎
min (𝐒(x)) (𝐒(y)) = 𝐒(min x y)
