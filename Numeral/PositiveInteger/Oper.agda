module Numeral.PositiveInteger.Oper where

open import Numeral.PositiveInteger

infixl 10010 _+_
infixl 10020 _⋅_
infixl 10030 _^_

-- Addition
_+_ : ℕ₊ → ℕ₊ → ℕ₊
x + 𝟏    = 𝐒(x)
x + 𝐒(y) = 𝐒(x + y)

-- Multiplication
_⋅_ : ℕ₊ → ℕ₊ → ℕ₊
x ⋅ 𝟏    = x
x ⋅ 𝐒(y) = x + (x ⋅ y)

-- Exponentiation
_^_ : ℕ₊ → ℕ₊ → ℕ₊
x ^ 𝟏    = x
x ^ 𝐒(y) = x ⋅ (x ^ y)

-- Factorial
_! : ℕ₊ → ℕ₊
𝟏 !    = 𝟏
𝐒(x) ! = 𝐒(x) ⋅ (x !)

open import Data.Option
open import Data.Option.Functions
-- Truncated subtraction
_−₀_ : ℕ₊ → ℕ₊ → Option(ℕ₊)
𝟏    −₀ _    = None
𝐒(x) −₀ 𝟏    = Some x
𝐒(x) −₀ 𝐒(y) = x −₀ y

open import Data.Boolean
open import Type
_≤?_ : ℕ₊ → ℕ₊ → Bool
𝟏    ≤? _    = 𝑇
𝐒(x) ≤? 𝟏    = 𝐹
𝐒(x) ≤? 𝐒(y) = x ≤? y
