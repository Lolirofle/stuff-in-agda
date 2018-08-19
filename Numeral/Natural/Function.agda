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
