module Numeral.Natural.Oper.Divisibility where

import      Lvl
open import Data
open import Data.Boolean
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Modulo

-- Divisibility check
_∣?_ : ℕ → ℕ → Bool
𝟎    ∣? _ = 𝐹
𝐒(y) ∣? x = zero?(x mod 𝐒(y))

-- Divisibility check
_∣₀?_ : ℕ → ℕ → Bool
𝟎 ∣₀? 𝟎    = 𝑇
𝟎 ∣₀? 𝐒(_) = 𝐹
𝐒(y) ∣₀? x = zero?(x mod 𝐒(y))

{-
open import Numeral.Natural.Oper
open import Numeral.Natural.UnclosedOper
open import Data.Option as Option using (Option)

{-# TERMINATING #-}
_∣?_ : ℕ → ℕ → Bool
_    ∣? 𝟎    = 𝑇
𝟎    ∣? 𝐒(_) = 𝐹
𝐒(x) ∣? 𝐒(y) with (x −? y)
... | Option.Some(xy) = xy ∣? 𝐒(y)
... | Option.None     = 𝐹
-}
