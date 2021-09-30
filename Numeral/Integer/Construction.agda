module Numeral.Integer.Construction where

open import Numeral.Integer
open import Numeral.Natural as ℕ using (ℕ)
import      Numeral.Sign       as Sign
import      Numeral.Sign.Oper0 as Sign

-- Unclosed total subtraction from natural numbers to integers
_−ₙ_ : ℕ → ℕ → ℤ
x      −ₙ ℕ.𝟎    = ℤ.+ₙ x
ℕ.𝟎    −ₙ ℕ.𝐒(x) = ℤ.−𝐒ₙ(x)
ℕ.𝐒(x) −ₙ ℕ.𝐒(y) = x −ₙ y

-- Construction of an integer with a sign and its numeral component.
signed : (Sign.+|−) → ℕ → ℤ
signed Sign.➕ = +ₙ_
signed Sign.➖ = −ₙ_

signed0 : (Sign.+|0|−) → ℕ → ℤ
signed0(Sign.➕) (ℕ.𝐒(n)) = +𝐒ₙ(n)
signed0(Sign.➖) (ℕ.𝐒(n)) = −𝐒ₙ(n)
{-# CATCHALL #-}
signed0 _        _       = 𝟎
