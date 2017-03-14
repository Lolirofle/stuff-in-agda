module Numeral.Integer where

open import Numeral.Natural as ℕ
  using (ℕ)
import Numeral.Natural.Oper as ℕ

data ℤ : Set where
  +_  : ℕ → ℤ
  −𝐒_ : ℕ → ℤ

{-# BUILTIN INTEGER         ℤ #-}
{-# BUILTIN INTEGERPOS     +_ #-}
{-# BUILTIN INTEGERNEGSUC −𝐒_ #-}

------------------------------------------
-- Constructors and deconstructors

-- Constructing negative number from ℕ
−_ : ℕ → ℤ
− ℕ.𝟎 = + ℕ.𝟎
− (ℕ.𝐒(x)) = −𝐒 x

-- Intuitive constructor patterns
pattern +𝐒 n = + (ℕ.𝐒(n))
pattern 𝟎 = + ℕ.𝟎

-- Absolute value
abs : ℤ → ℕ
abs(+ x)  = x
abs(−𝐒 x) = x
