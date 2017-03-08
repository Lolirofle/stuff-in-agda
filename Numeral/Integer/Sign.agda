module Numeral.Integer.Sign where

open import Numeral.Integer
open import Numeral.Integer.Oper
import Numeral.Sign as Sign

sign : ℤ → Sign.+|−
sign(+ _) = Sign.+
sign(−𝐒 _) = Sign.−

sign0 : ℤ → Sign.+|0|−
sign0(𝟎) = Sign.[0]
sign0(+𝐒 _) = Sign.+
sign0(−𝐒 _) = Sign.−

signum0 : ℤ → ℤ
signum0(𝟎) = 𝟎
signum0(+𝐒 _) = 𝐒(𝟎)
signum0(−𝐒 _) = 𝐏(𝟎)
