module Numeral.Integer.Sign where

open import Numeral.Natural
  using (ℕ)
open import Numeral.Integer
open import Numeral.Sign as Sign
  using (+|− ; +|0|−)

sign : ℤ → (+|−)
sign(+ₙ _) = Sign.➕
sign(−𝐒ₙ _) = Sign.➖

sign0 : ℤ → (+|0|−)
sign0(𝟎) = Sign.𝟎
sign0(+𝐒ₙ _) = Sign.➕
sign0(−𝐒ₙ _) = Sign.➖

signum0 : ℤ → ℤ
signum0(𝟎) = 𝟎
signum0(+𝐒ₙ _) = +𝐒ₙ(ℕ.𝟎)
signum0(−𝐒ₙ _) = −𝐒ₙ(ℕ.𝟎)
