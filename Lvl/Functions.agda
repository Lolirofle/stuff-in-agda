module Lvl.Functions where

open import Lvl
open import Numeral.Natural

add : ℕ → Lvl.Level → Lvl.Level
add ℕ.𝟎     ℓ = ℓ
add (ℕ.𝐒 n) ℓ = Lvl.𝐒(add n ℓ)
