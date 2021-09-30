module Numeral.Natural.Oper.CeiledDivision where

import Lvl
open import Data
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation

infixl 10100 _⌈/⌉_

-- Ceiled division operation (rounding up).
{-# TERMINATING #-}
_⌈/⌉_ : ℕ → (m : ℕ) → .⦃ _ : Positive(m) ⦄ → ℕ
𝟎       ⌈/⌉ m@(𝐒 _) = 𝟎
a@(𝐒 _) ⌈/⌉ m@(𝐒 _) = 𝐒((a −₀ m) ⌈/⌉ m)

_⌈/⌉₀_ : ℕ → ℕ → ℕ
_ ⌈/⌉₀ 𝟎    = 𝟎
a ⌈/⌉₀ 𝐒(m) = a ⌈/⌉ 𝐒(m)
{-# INLINE _⌈/⌉₀_ #-}
