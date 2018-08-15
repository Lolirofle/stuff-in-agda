module Numeral.Natural.Oper.Divisibility where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.Option as Option using (Option)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.UnclosedOper

-- Divisibility check
{-# TERMINATING #-}
_∣?_ : ℕ → ℕ → Bool
_    ∣? 𝟎    = 𝑇
𝟎    ∣? 𝐒(_) = 𝐹
x    ∣? y with (x −? y)
... | Option.Some(xy) = xy ∣? y
... | Option.None     = 𝐹
