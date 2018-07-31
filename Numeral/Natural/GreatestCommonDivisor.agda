module Numeral.Natural.GreatestCommonDivisor where

import Lvl
open import Numeral.Integer as ℤ
  using (ℤ)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Properties{Lvl.𝟎}

{-# TERMINATING #-}
gcd : ℕ → ℕ → ℕ
gcd(a)(𝟎) = a
gcd(a)(𝐒(b)) = gcd(𝐒(b))(_mod_ a (𝐒(b)) ⦃ [𝐒]-not-0 ⦄)

-- lcm : ℕ → ℕ → ℕ
-- lcm(a)(b) = (a ⋅ b) / gcd(a)(b)
