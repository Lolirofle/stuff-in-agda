module Numeral.Integer.Oper where

open import Numeral.Natural              as ℕ using (ℕ)
import      Numeral.Natural.Oper         as ℕ
open import Numeral.Natural.UnclosedOper using () renaming (_−_ to _−ₙ_ ; signed0 to signedℕ)
open import Numeral.Integer
open import Numeral.Integer.Sign
import      Numeral.Sign       as Sign
import      Numeral.Sign.Oper0 as Sign

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
-- Binary operations

infixl 10010 _+_
infixl 10020 _⋅_

-- Addition
_+_ : ℤ → ℤ → ℤ
(+ₙ  x) + (+ₙ  y) = +ₙ (x ℕ.+ y)
(−𝐒ₙ x) + (−𝐒ₙ y) = −𝐒ₙ(ℕ.𝐒(x ℕ.+ y))
(+ₙ  x) + (−𝐒ₙ y) = x −ₙ ℕ.𝐒(y)
(−𝐒ₙ x) + (+ₙ  y) = (+ₙ y) + (−𝐒ₙ x)

-- Subtraction
_−_ : ℤ → ℤ → ℤ
x − y = x + (− y)

-- Multiplication
_⋅_ : ℤ → ℤ → ℤ
x ⋅ y = signedℕ ((sign0 x) Sign.⨯ (sign0 y)) ((absₙ x) ℕ.⋅ (absₙ y))

-- Distance
_𝄩_ : ℤ → ℤ → ℕ
(+ₙ  x)     𝄩 (+ₙ  y)     = x ℕ.𝄩 y
(−𝐒ₙ x)     𝄩 (−𝐒ₙ y)     = x ℕ.𝄩 y
(+ₙ(ℕ.𝟎))   𝄩 (−𝐒ₙ y)     = ℕ.𝐒(y)
(+ₙ(ℕ.𝐒 x)) 𝄩 (−𝐒ₙ y)     = ℕ.𝐒((+ₙ x) 𝄩 (−𝐒ₙ y))
(−𝐒ₙ x)     𝄩 (+ₙ(ℕ.𝟎))   = ℕ.𝐒(x)
(−𝐒ₙ x)     𝄩 (+ₙ(ℕ.𝐒 y)) = ℕ.𝐒((−𝐒ₙ x) 𝄩 (+ₙ y))
