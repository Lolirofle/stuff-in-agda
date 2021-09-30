module Numeral.Integer.Function where

open import Numeral.Integer
open import Numeral.Natural as ℕ using (ℕ)
import      Numeral.Sign as Sign

------------------------------------------
-- Unary operations

-- Predecessor
𝐏 : ℤ → ℤ
𝐏(+𝐒ₙ(n)) = +ₙ n
𝐏(𝟎)      = −𝐒ₙ(ℕ.𝟎)
𝐏(−𝐒ₙ(n)) = −𝐒ₙ(ℕ.𝐒(n))

-- Successor
𝐒 : ℤ → ℤ
𝐒(+ₙ n)        = +ₙ ℕ.𝐒(n)
𝐒(−𝐒ₙ(ℕ.𝟎))    = +ₙ ℕ.𝟎
𝐒(−𝐒ₙ(ℕ.𝐒(n))) = −𝐒ₙ(n)

-- Identity
+_ : ℤ → ℤ
+ n = n

-- Negation
−_ : ℤ → ℤ
− 𝟎 = 𝟎
− (+𝐒ₙ(n)) = −𝐒ₙ(n)
− (−𝐒ₙ(n)) = +𝐒ₙ(n)

-- Absolute value
abs : ℤ → ℤ
abs(+ₙ x)  = +ₙ x
abs(−𝐒ₙ x) = +𝐒ₙ x

------------------------------------------
-- Operations by signs

step : (Sign.+|−) → ℤ → ℤ
step(Sign.➕) = 𝐒
step(Sign.➖) = 𝐏

signOn : (Sign.+|−) → ℤ → ℤ
signOn(Sign.➕) = +_
signOn(Sign.➖) = −_
