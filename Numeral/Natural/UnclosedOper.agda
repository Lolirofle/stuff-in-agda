module Numeral.Natural.UnclosedOper where

import Lvl
open import Data.Option as Option using (Option)
open import Numeral.Finite as 𝕟
  using (𝕟)
import      Numeral.Finite.Bound{Lvl.𝟎} as 𝕟bound
open import Numeral.Integer as ℤ
  using (ℤ)
open import Numeral.Natural
open import Numeral.Natural.Oper
import Numeral.Sign as Sign

infix  10010 _−_

-- Unclosed total subtraction from natural numbers to integers
_−_ : ℕ → ℕ → ℤ
x − 𝟎       = ℤ.+ₙ x
𝟎 − 𝐒(x)    = ℤ.−𝐒ₙ(x)
𝐒(x) − 𝐒(y) = x − y

-- Construction of an integer with the sign and numeral components
signed : (Sign.+|−) → ℕ → ℤ
signed (Sign.➕) (n) = ℤ.+ₙ n
signed (Sign.➖) (n) = ℤ.−ₙ n

signed0 : (Sign.+|0|−) → ℕ → ℤ
signed0(Sign.➕) (ℕ.𝐒(n)) = ℤ.+𝐒ₙ(n)
signed0(Sign.➖) (ℕ.𝐒(n)) = ℤ.−𝐒ₙ(n)
signed0(_)      (_)      = ℤ.𝟎

-- TODO _/_ : ℕ → ℕ → ℚ

-- Unclosed total subtraction from natural numbers to an optional natural number.
-- When the subtraction gives a negative number semantically, this operation gives Option.None.
_−?_ : ℕ → ℕ → Option(ℕ)
a    −? 𝟎    = Option.Some(a)
𝟎    −? 𝐒(b) = Option.None
𝐒(a) −? 𝐒(b) = a −? b

-- Unclosed total floored division
{-# TERMINATING #-}
_⌊/₀⌋_ : ℕ → ℕ → ℕ
𝟎 ⌊/₀⌋ y = 𝟎
x ⌊/₀⌋ 𝟎 = 𝟎
x ⌊/₀⌋ y with (x −? y)
... | Option.Some(xy) = 𝐒(xy ⌊/₀⌋ y)
... | Option.None     = 𝟎

-- Unclosed total subtraction from natural numbers to an optional natural number.
-- When dividing by 0, this operation gives Option.None.
{-# TERMINATING #-}
_⌊/⌋?_ : ℕ → ℕ → Option(ℕ)
𝟎 ⌊/⌋? y = Option.Some(𝟎)
x ⌊/⌋? 𝟎 = Option.None
x ⌊/⌋? y with (x −? y)
... | Option.Some(xy) = Option.map 𝐒(xy ⌊/⌋? y)
... | Option.None     = Option.Some(𝟎)

-- Unclosed total subtraction from natural numbers to an optional natural number.
-- When dividing by 0 or the division gives a rational number semantically, this operation gives Option.None.
{-# TERMINATING #-}
_/?_ : ℕ → ℕ → Option(ℕ)
𝟎 /? y = Option.Some(𝟎)
x /? 𝟎 = Option.None
x /? y with (x −? y)
... | Option.Some(xy) = Option.map 𝐒(xy /? y)
... | Option.None     = Option.None

-- Unclosed total subtraction from natural numbers to finite natural numbers
_−₀fin_ : (x : ℕ) → ℕ → 𝕟(𝐒(x))
𝟎    −₀fin _    = 𝕟.𝟎
𝐒(x) −₀fin 𝟎    = 𝕟.𝐒(x −₀fin 𝟎)
𝐒(x) −₀fin 𝐒(y) = 𝕟bound.bound-𝐒 (x −₀fin y)

-- Unclosed total subtraction from a natural number and a finite natural number to a finite natural number
_−fin_ : (x : ℕ) → 𝕟(𝐒(x)) → 𝕟(𝐒(x))
𝟎    −fin 𝕟.𝟎    = 𝕟.𝟎
𝐒(x) −fin 𝕟.𝟎    = 𝕟.𝐒(x −fin 𝕟.𝟎)
𝐒(x) −fin 𝕟.𝐒(y) = 𝕟bound.bound-𝐒 (x −fin y)
