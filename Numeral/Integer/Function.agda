module Numeral.Integer.Function where

open import Numeral.Integer
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Sign using (Sign ; ➕ ; ➖)

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
infixl 10100 +_

-- Negation
−_ : ℤ → ℤ
− 𝟎 = 𝟎
− (+𝐒ₙ(n)) = −𝐒ₙ(n)
− (−𝐒ₙ(n)) = +𝐒ₙ(n)
infixl 10100 −_

-- Absolute value
abs : ℤ → ℤ
abs(+ₙ x)  = +ₙ x
abs(−𝐒ₙ x) = +𝐒ₙ x

------------------------------------------
-- Operations by signs

step : Sign → ℤ → ℤ
step ➕ = 𝐒
step ➖ = 𝐏

signOn : Sign → ℤ → ℤ
signOn ➕ = +_
signOn ➖ = −_
