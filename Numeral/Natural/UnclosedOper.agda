module Numeral.Natural.UnclosedOper where

open import Numeral.Integer as ℤ
  using (ℤ)
open import Numeral.Natural
open import Numeral.Natural.Oper

-- Subtraction
_−_ : ℕ → ℕ → ℤ
x − 𝟎 = ℤ.+ x
𝟎 − 𝐒(x) = ℤ.−𝐒(x)
𝐒(x) − 𝐒(y) = ℤ.+(x −₀ y)
