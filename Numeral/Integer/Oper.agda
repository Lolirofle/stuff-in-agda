module Numeral.Integer.Oper where

open import Numeral.Natural              as ℕ using (ℕ)
import      Numeral.Natural.Oper         as ℕ
import      Numeral.Natural.UnclosedOper as ℕ
open import Numeral.Integer
open import Numeral.Integer.Sign
import      Numeral.Sign      as Sign
import      Numeral.Sign.Oper as Sign

------------------------------------------
-- Unary operations

-- Predecessor
𝐏 : ℤ → ℤ
𝐏(𝟎)      = −𝐒ₙ(ℕ.𝟎)
𝐏(+𝐒ₙ(n)) = +ₙ n
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
abs(−𝐒ₙ x) = 𝐒(+ₙ x)

------------------------------------------
-- Binary operations

infixl 10010 _+_
infixl 10020 _⋅_

-- Addition
_+_ : ℤ → ℤ → ℤ
(+ₙ x) + (+ₙ y) = +ₙ (x ℕ.+ y)
(−𝐒ₙ x) + (−𝐒ₙ y) = −𝐒ₙ(x ℕ.+ (ℕ.𝐒(y)))
(+ₙ x) + (−𝐒ₙ(y)) = x ℕ.− ℕ.𝐒(y)
(−𝐒ₙ(x)) + (+ₙ y) = y ℕ.− ℕ.𝐒(x)

-- Subtraction
_−_ : ℤ → ℤ → ℤ
x − y = x + (− y)

-- Multiplication
_⋅_ : ℤ → ℤ → ℤ
x ⋅ y = ℕ.signed ((sign x) Sign.⨯ (sign y)) ((absₙ x) ℕ.⋅ (absₙ y))
