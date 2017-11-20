module Numeral.Natural.UnclosedOper where

open import Numeral.Integer as ℤ
  using (ℤ)
open import Numeral.Natural
open import Numeral.Natural.Oper
import Numeral.Sign as Sign

infix  10010 _−_

-- Subtraction
_−_ : ℕ → ℕ → ℤ
x − 𝟎       = ℤ.+ₙ x
𝟎 − 𝐒(x)    = ℤ.−𝐒ₙ(x)
𝐒(x) − 𝐒(y) = ℤ.+ₙ(x −₀ y)

-- Construction of an integer with the sign and numeral components
signed : (Sign.+|−) → ℕ → ℤ
signed (Sign.+) n = ℤ.+ₙ n
signed (Sign.−) n = ℤ.−ₙ n
