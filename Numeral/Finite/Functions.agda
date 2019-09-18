module Numeral.Finite.Functions where

import Lvl
open import Syntax.Number
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Function renaming (max to maxℕ ; min to minℕ)
open import Numeral.Natural.Oper

-- Maximum function
-- Returns the greatest number
max : ∀{a b} → 𝕟(a) → 𝕟(b) → 𝕟(maxℕ a b)
max {a}{b} x      𝟎      = bound-maxₗ {a}{b} (x)
max {a}{b} 𝟎      y      = bound-maxᵣ {a}{b} (y)
max        (𝐒(x)) (𝐒(y)) = 𝐒(max x y)

-- Minimum function
-- Returns the smallest number
min : ∀{a b} → 𝕟(a) → 𝕟(b) → 𝕟(minℕ a b)
min 𝟎      𝟎      = 𝟎
min (𝐒(_)) 𝟎      = 𝟎
min 𝟎      (𝐒(_)) = 𝟎
min (𝐒(x)) (𝐒(y)) = 𝐒(min x y)
