module Numeral.Natural.Oper.FlooredDivision where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Comparisons.Proofs
open import Numeral.Natural.Relation.Order
open import Relator.Equals

infixl 10100 _⌊/⌋_

-- Inductive definition of an algorithm for division.
-- `[ d , b ] a' div b'` should be interpreted as following:
--   `d` is the result of the algorithm that is being incremented as it runs.
--   `b` is the predecessor of the original denominator. This is constant throughout the whole process.
--   `a'` is the numerator. This is decremented as it runs.
--   `b'` is the predecessor of the temporary denominator. This is decremented as it runs.
-- By decrementing both `a'` and `b'`, and incrementing `d` when 'b`' reaches 0, it counts how many times `b` "fits into" `a`. 
-- Note: See Numeral.Natural.Oper.Modulo for a similiar algorithm used to determine the modulo.
[_,_]_div_ : ℕ → ℕ → ℕ → ℕ → ℕ
[ d , _ ] 𝟎     div _     = d
[ d , b ] 𝐒(a') div 𝟎     = [ 𝐒(d) , b ] a' div b
[ d , b ] 𝐒(a') div 𝐒(b') = [ d   , b ] a' div b'
{-# BUILTIN NATDIVSUCAUX [_,_]_div_ #-}

-- Floored division operation.
_⌊/⌋_ : ℕ → (m : ℕ) → ⦃ _ : IsTrue(positive?(m)) ⦄ → ℕ
a ⌊/⌋ 𝐒(m) = [ 𝟎 , m ] a div m

_⌊/⌋₀_ : ℕ → ℕ → ℕ
_ ⌊/⌋₀ 𝟎    = 𝟎
a ⌊/⌋₀ 𝐒(m) = a ⌊/⌋ 𝐒(m)
{-# INLINE _⌊/⌋₀_ #-}
