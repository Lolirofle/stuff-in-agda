module Numeral.Natural.Function.Coprimalize where

open import Data.Tuple
open import Numeral.Natural
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Oper.FlooredDivision

-- Two numbers without their common divisors (without their common primes).
-- This will result in two coprime numbers that have the same ratio as the original numbers.
-- Example:
--   168           = 2³⋅3⋅7
--   30            = 2⋅3⋅5
--   gcd(168 , 30) = 2⋅3
--   168 / gcd(168 , 30) = 2³⋅3⋅7 / 2⋅3 = 2²⋅7 = 28
--   30  / gcd(168 , 30) = 2⋅3⋅5 / 2⋅3 = 5
--   coprimalize(168 , 30) = (28 , 5)
coprimalize : (ℕ ⨯ ℕ) → (ℕ ⨯ ℕ)
coprimalize(x , y) = let g = gcd x y in ((x ⌊/⌋₀ g) , (y ⌊/⌋₀ g))
