module Numeral.Natural.Oper.Modulo where

open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.UnclosedOper

infixl 10100 _mod_

-- Difference between the value before and after the floored division operation.
_mod_ : ℕ → ℕ → ℕ
_mod_ a b = a −₀ ((a ⌊/₀⌋ b) ⋅ b)

-- postulate _ : (a + b) mod b ≡ a mod b
{-
6 mod 3
3 mod 3
0 mod 3

8 mod 3
5 mod 3
2 mod 3

4 mod 3
1 mod 3

2 mod 3
-}
