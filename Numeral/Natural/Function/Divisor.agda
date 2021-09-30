module Numeral.Natural.Function.Divisor where

open import Data.List
import      Data.Option.Functions as Option
open import Numeral.Natural
open import Numeral.Natural.LinearSearch
open import Numeral.Natural.Oper.Divisibility

-- The "smallest" divisor of a number.
-- When 0 or 1, it is the actual smallest divisor.
-- When greater than 1, it is the smallest divisor greater than 1.
leastDivisor : ℕ → ℕ
leastDivisor 0          = 0
leastDivisor 1          = 1
leastDivisor n@(𝐒(𝐒 _)) = (findBoundedMin 2 n (_∣₀? n)) Option.or n

divisors : ℕ → List(ℕ)
divisors n = findBoundedAll 2 n (_∣₀? n)
