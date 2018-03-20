module Numeral.Natural.Oper.Modulo{ℓ} where

-- Difference between the value before and after the floored division operation.
_mod_ : ℕ → ℕ → ℕ
_mod_ a b = a −₀ ((a / b) ⋅ b)

postulate _ : (a + b) mod b ≡ a mod b
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
