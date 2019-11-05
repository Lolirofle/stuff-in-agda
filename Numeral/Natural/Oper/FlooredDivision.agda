module Numeral.Natural.Oper.FlooredDivision where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Logic.Propositional.Theorems
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Relator.Equals

infixl 10100 _⌊/⌋_

-- Note: See Numeral.Natural.Oper.Modulo
[_,_]_div_ : ℕ → ℕ → ℕ → ℕ → ℕ
[ d , _ ] 𝟎     div _     = d
[ d , b ] 𝐒(a') div 𝟎     = [ 𝐒(d) , b ] a' div b
[ d , b ] 𝐒(a') div 𝐒(b') = [ d   , b ] a' div b'
{-# BUILTIN NATDIVSUCAUX [_,_]_div_ #-}

-- Floored division operation.
_⌊/⌋_ : ℕ → (m : ℕ) → ⦃ _ : IsTrue(m ≢? 𝟎)⦄ → ℕ
a ⌊/⌋ 𝐒(m) = [ 𝟎 , m ] a div m

_⌊/⌋₀_ : ℕ → ℕ → ℕ
_ ⌊/⌋₀ 𝟎    = 𝟎
a ⌊/⌋₀ 𝐒(m) = a ⌊/⌋ 𝐒(m)
{-# INLINE _⌊/⌋₀_ #-}
