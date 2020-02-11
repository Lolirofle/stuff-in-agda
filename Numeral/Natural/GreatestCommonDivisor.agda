module Numeral.Natural.GreatestCommonDivisor where

import Lvl
open import Data
open import Numeral.Integer as ℤ
  using (ℤ)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs

{-# TERMINATING #-}
gcd : ℕ → ℕ → ℕ
gcd(a)(𝟎) = a
gcd(a)(𝐒(b)) = gcd(𝐒(b))(a mod 𝐒(b))

lcm : ℕ → ℕ → ℕ
lcm(a)(b) = (a ⋅ b) ⌊/⌋₀ gcd(a)(b)

-- TODO: Prove (gcd(a)(b) ∣ a) and (gcd(a)(b) ∣ b)
