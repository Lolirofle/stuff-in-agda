module Numeral.Integer where

open import Numeral.Natural as ℕ
  using (ℕ)
  renaming (𝟎 to 𝟎ₙ ; 𝐒 to 𝐒ₙ)
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
− 𝟎ₙ = + 𝟎ₙ
− (𝐒ₙ(x)) = −𝐒(x)

-- Intuitive constructor patterns
pattern +𝐒 n = + (𝐒ₙ(n)) -- Positive integers (1,..)
pattern 𝟎 = + 𝟎ₙ -- Zero

-- Absolute value
abs : ℤ → ℕ
abs(+ x)  = x
abs(−𝐒 x) = 𝐒ₙ(x)

-- Syntax
record From-negative-ℕ (T : Set) : Set where
  field from-negative-ℕ : ℕ → T
open From-negative-ℕ {{...}} public
{-# BUILTIN FROMNEG from-negative-ℕ #-}

instance
  ℤ-From-negative-ℕ : From-negative-ℕ (ℤ)
  from-negative-ℕ ⦃ ℤ-From-negative-ℕ ⦄ = −_
