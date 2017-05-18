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
