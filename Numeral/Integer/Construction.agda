module Numeral.Integer.Construction where

open import Numeral.Charge hiding (𝟎)
open import Numeral.Integer
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Sign

-- Unclosed total subtraction from natural numbers to integers
_−ₙ_ : ℕ → ℕ → ℤ
x      −ₙ ℕ.𝟎    = +ₙ x
ℕ.𝟎    −ₙ ℕ.𝐒(x) = −𝐒ₙ(x)
ℕ.𝐒(x) −ₙ ℕ.𝐒(y) = x −ₙ y

-- Construction of an integer with a sign and its numeral component.
signed : Sign → ℕ → ℤ
signed ➕ = +ₙ_
signed ➖ = −ₙ_

signed0 : Charge → ℕ → ℤ
signed0 ➕(ℕ.𝐒(n)) = +𝐒ₙ(n)
signed0 ➖(ℕ.𝐒(n)) = −𝐒ₙ(n)
{-# CATCHALL #-}
signed0 _        _       = 𝟎
