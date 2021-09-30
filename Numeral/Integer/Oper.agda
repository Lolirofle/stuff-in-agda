module Numeral.Integer.Oper where

open import Numeral.Natural      as ℕ using (ℕ)
import      Numeral.Natural.Oper as ℕ
open import Numeral.Integer
open import Numeral.Integer.Construction
open import Numeral.Integer.Function
open import Numeral.Integer.Sign
import      Numeral.Sign       as Sign
import      Numeral.Sign.Oper0 as Sign

-- Addition
_+_ : ℤ → ℤ → ℤ
(+ₙ  x) + (+ₙ  y) = +ₙ (x ℕ.+ y)
(−𝐒ₙ x) + (−𝐒ₙ y) = −𝐒ₙ(ℕ.𝐒(x ℕ.+ y))
(+ₙ  x) + (−𝐒ₙ y) = x −ₙ ℕ.𝐒(y)
(−𝐒ₙ x) + (+ₙ  y) = (+ₙ y) + (−𝐒ₙ x)
infixl 10010 _+_

-- Subtraction
_−_ : ℤ → ℤ → ℤ
x − y = x + (− y)
infixl 10010 _−_

-- Multiplication
_⋅_ : ℤ → ℤ → ℤ
x ⋅ y = signed0 ((sign0 x) Sign.⨯ (sign0 y)) ((absₙ x) ℕ.⋅ (absₙ y))
infixl 10020 _⋅_

-- Distance
_𝄩_ : ℤ → ℤ → ℕ
(+ₙ  x) 𝄩 (+ₙ  y) = x ℕ.𝄩 y
(−𝐒ₙ x) 𝄩 (−𝐒ₙ y) = x ℕ.𝄩 y
𝟎       𝄩 (−𝐒ₙ y) = ℕ.𝐒(y)
(−𝐒ₙ x) 𝄩 𝟎       = ℕ.𝐒(x)
(+𝐒ₙ x) 𝄩 (−𝐒ₙ y) = ℕ.𝐒((+ₙ x) 𝄩 (−𝐒ₙ y))
(−𝐒ₙ x) 𝄩 (+𝐒ₙ y) = ℕ.𝐒((−𝐒ₙ x) 𝄩 (+ₙ y))
infixl 10010 _𝄩_
