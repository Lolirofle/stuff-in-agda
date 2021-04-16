module Numeral.Natural.Function.Coprimalize where

open import Data.Tuple
open import Numeral.Natural
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Oper.FlooredDivision

coprimalize : (ℕ ⨯ ℕ) → (ℕ ⨯ ℕ)
coprimalize(x , y) = ((x ⌊/⌋₀ gcd(x)(y)) , (y ⌊/⌋₀ gcd(x)(y)))

{- TODO: Maybe prove something like (b ∣ a) → ((d ∣ (a / b)) ↔ ((d ∣ a) ∧ (d ∤ b))) if it holds?
open import Numeral.Natural.Coprime
open import Relator.Equals

Coprime-coprimalize : ∀{xy} → uncurry Coprime(coprimalize xy)
Coprime.proof Coprime-coprimalize nx ny = {!!} where

n ∣ (x ⌊/⌋₀ gcd(x)(y))
(n ∣ x) ∧ (n ∤ gcd(x)(y))
-}
