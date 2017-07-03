module Numeral.Integer.Oper where

open import Numeral.Natural as ℕ
  using (ℕ)
  renaming (𝟎 to 𝟎ₙ ; 𝐒 to 𝐒ₙ)
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
𝐏(+ 𝟎ₙ) = −𝐒(𝟎ₙ)
𝐏(+(𝐒ₙ(n))) = + n
𝐏(−𝐒 n) = −𝐒(𝐒ₙ(n))

-- Successor
𝐒 : ℤ → ℤ
𝐒(+ n) = + 𝐒ₙ(n)
𝐒(−𝐒 𝟎ₙ) = + 𝟎ₙ
𝐒(−𝐒 (𝐒ₙ(n))) = −𝐒(n)

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

infixl 10010 _+_
infixl 10020 _⋅_

-- Addition
_+_ : ℤ → ℤ → ℤ
(+ x) + (+ y) = + (x ℕ.+ y)
(−𝐒 x) + (−𝐒 y) = −𝐒(x ℕ.+ (𝐒ₙ(y)))
(+ x) + (−𝐒(y)) = x ℕ.− 𝐒ₙ(y)
(−𝐒(x)) + (+ y) = y ℕ.− 𝐒ₙ(x)

-- Subtraction
_−_ : ℤ → ℤ → ℤ
x − y = x + (−₁ y)

-- Multiplication
_⋅_ : ℤ → ℤ → ℤ
x ⋅ y = ℕ.signed ((sign x) Sign.⋅ (sign y)) ((abs x) ℕ.⋅ (abs y))
