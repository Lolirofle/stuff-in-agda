module Numeral.Natural.Oper where

open import Numeral.Natural

-- Addition
infixl 5 _+_
_+_ : ℕ → ℕ → ℕ
x + 𝟎 = x
x + 𝐒(y) = 𝐒(x + y)
{-# BUILTIN NATPLUS _+_ #-}

-- Multiplication
infixl 6 _⋅_
_⋅_ : ℕ → ℕ → ℕ
x ⋅ 𝟎 = 𝟎
x ⋅ 𝐒(y) = x + (x ⋅ y)
{-# BUILTIN NATTIMES _⋅_ #-}

-- Exponentiation
_^_ : ℕ → ℕ → ℕ
x ^ 𝟎 = 𝐒(𝟎)
x ^ 𝐒(y) = x ⋅ (x ^ y)

-- Factorial
_! : ℕ → ℕ
𝟎 ! = 𝐒(𝟎)
𝐒(x) ! = 𝐒(x) ⋅ (x !)



-- Closed subtraction
_−₀_ : ℕ → ℕ → ℕ
x −₀ 𝟎 = x
𝟎 −₀ 𝐒(x) = 𝟎
𝐒(x) −₀ 𝐒(y) = x −₀ y
{-# BUILTIN NATMINUS _−₀_ #-}

-- Closed division
-- _/₀ _ : ℕ → ℕ → ℕ
-- 𝟎 /₀ x = 𝟎
-- x /₀ 𝟎 = 𝟎
-- 𝐒(x) /₀ y = 𝐒((x −₀ y) /₀ 𝐒(y))

-- 15/5 = 1+((15−5)/5)
-- 15/5 = 1+(10/5)
-- 15/5 = 1+1+(5/5)
-- 15/5 = 1+1+1+(0/5)
-- 15/5 = 1+1+1+0
