module Numeral.PositiveInteger.Oper where

open import Functional
open import Numeral.Natural as ℕ using (ℕ)
import      Numeral.Natural.Oper as ℕ
open import Numeral.PositiveInteger

infixl 10010 _+_
infixl 10020 _⋅_
infixl 10030 _^_

-- Addition
_+_ : ℕ₊ → ℕ₊ → ℕ₊
_+_ = ℕ.𝐏 ∘₂ ((ℕ._+_) on₂ ℕ.𝐒)

-- Multiplication
_⋅_ : ℕ₊ → ℕ₊ → ℕ₊
_⋅_ = ℕ.𝐏 ∘₂ ((ℕ._⋅_) on₂ ℕ.𝐒)

-- Exponentiation
_^_ : ℕ₊ → ℕ₊ → ℕ₊
_^_ = ℕ.𝐏 ∘₂ ((ℕ._^_) on₂ ℕ.𝐒)

-- Factorial
_! : ℕ₊ → ℕ₊
_! = ℕ.𝐏 ∘ (ℕ._!) ∘ ℕ.𝐒

-- Truncated subtraction
_−₀_ : ℕ₊ → ℕ₊ → ℕ
𝟏    −₀ _    = ℕ.𝟎
𝐒(x) −₀ 𝟏    = toℕ x
𝐒(x) −₀ 𝐒(y) = x −₀ y

open import Data.Boolean
import      Numeral.Natural.Oper.Comparisons as ℕ

_≤?_ : ℕ₊ → ℕ₊ → Bool
_≤?_ = (ℕ._≤?_) on₂ 𝐒
