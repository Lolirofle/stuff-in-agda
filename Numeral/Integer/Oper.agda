module Numeral.Integer.Oper where

open import Numeral.Natural as ℕ
  using (ℕ)
import Numeral.Natural.Oper as ℕ
import Numeral.Natural.UnclosedOper as ℕ
open import Numeral.Integer
open import Numeral.Integer.Sign
import Numeral.Sign as Sign
import Numeral.Sign.Oper as Sign

------------------------------------------
-- Unary operations

-- Predecessor
𝐏 : ℤ → ℤ
𝐏(+ ℕ.𝟎) = −𝐒(ℕ.𝟎)
𝐏(+(ℕ.𝐒(n))) = + n
𝐏(−𝐒 n) = −𝐒 (ℕ.𝐒(n))

-- Successor
𝐒 : ℤ → ℤ
𝐒(+ n) = + ℕ.𝐒(n)
𝐒(−𝐒 ℕ.𝟎) = + ℕ.𝟎
𝐒(−𝐒 (ℕ.𝐒(n))) = −𝐒(n)

-- TODO: Rename operators and constructors to something better?
-- Identity
+₁_ : ℤ → ℤ
+₁ n = n

-- Negation
−₁_ : ℤ → ℤ
−₁ 𝟎 = 𝟎
−₁ (+𝐒(n)) = −𝐒(n)
−₁ (−𝐒(n)) = +𝐒(n)

------------------------------------------
-- Binary operations

-- Addition
_+_ : ℤ → ℤ → ℤ
(+ x) + (+ y) = + (x ℕ.+ y)
(−𝐒 x) + (−𝐒 y) = −𝐒(x ℕ.+ (ℕ.𝐒(y)))
(+ x) + (−𝐒(y)) = x ℕ.− ℕ.𝐒(y)
(−𝐒(x)) + (+ y) = y ℕ.− ℕ.𝐒(x)

-- Subtraction
_−_ : ℤ → ℤ → ℤ
x − y = x + (−₁ y)

-- Multiplication
_⋅_ : ℤ → ℤ → ℤ
x ⋅ y = ℕ.signed ((sign x) Sign.⋅ (sign y)) ((abs x) ℕ.⋅ (abs y))
