module Numeral.Natural.UnclosedOper where

open import Numeral.Integer as ℤ
  using (ℤ)
open import Numeral.Natural
open import Numeral.Natural.Oper
import Numeral.Sign as Sign

infix  10010 _−_

-- Subtraction
_−_ : ℕ → ℕ → ℤ
x − 𝟎 = ℤ.+ x
𝟎 − 𝐒(x) = ℤ.−𝐒(x)
𝐒(x) − 𝐒(y) = ℤ.+(x −₀ y)

-- Construction of an integer with the sign and numeral components
signed : (Sign.+|−) → ℕ → ℤ
signed (Sign.+) n = ℤ.+ n
signed (Sign.−) n = ℤ.− n
