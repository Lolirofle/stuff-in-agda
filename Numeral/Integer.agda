module Numeral.Integer where

open import Numeral.Natural as ℕ
  using (ℕ)
import Numeral.Natural.Oper as ℕ

-- Integers
data ℤ : Set where
  +_  : ℕ → ℤ -- Positive integers including zero (0,1,..)
  −𝐒_ : ℕ → ℤ -- Negative integers (..,-1)

{-# BUILTIN INTEGER        ℤ #-}
{-# BUILTIN INTEGERPOS     +_ #-}
{-# BUILTIN INTEGERNEGSUC −𝐒_ #-}

------------------------------------------
-- Constructors and deconstructors

-- Constructing negative number from ℕ
−_ : ℕ → ℤ
− ℕ.𝟎 = + ℕ.𝟎
− (ℕ.𝐒(x)) = −𝐒 x

-- Intuitive constructor patterns
pattern +𝐒 n = + (ℕ.𝐒(n)) -- Positive integers (1,..)
pattern 𝟎 = + ℕ.𝟎 -- Zero

-- Absolute value
abs : ℤ → ℕ
abs(+ x)  = x
abs(−𝐒 x) = ℕ.𝐒(x)
