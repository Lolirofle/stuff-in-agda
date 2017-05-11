module Numeral.Natural.Function where

open import Numeral.Natural
open import Numeral.Natural.Oper

max : ℕ → ℕ → ℕ
max a b = a + (b −₀ a)

min : ℕ → ℕ → ℕ
min a b = (a + b) −₀ max(a)(b)

_[max]_ = max
_[min]_ = min
