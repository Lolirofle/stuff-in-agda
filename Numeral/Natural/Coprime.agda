module Numeral.Natural.Coprime where

open import Logic
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Relation.Divisibility
open import Relator.Equals

private variable n x y : ℕ

-- Two numbers are coprime when their only divisor is 1.
record Coprime (x : ℕ) (y : ℕ) : Stmt{Lvl.𝟎} where
  constructor intro
  field proof : (n ∣ x) → (n ∣ y) → (n ≡ 1)

