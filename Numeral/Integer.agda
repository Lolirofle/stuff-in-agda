module Numeral.Integer where

open import Numeral.Natural      as ℕ using (ℕ)
import      Numeral.Natural.Oper as ℕ
open import Syntax.Number

-- Integers
data ℤ : Set where
  +ₙ_  : ℕ → ℤ -- Positive integers including zero (0,1,..)
  −𝐒ₙ_ : ℕ → ℤ -- Negative integers (..,-1)

{-# BUILTIN INTEGER        ℤ  #-}
{-# BUILTIN INTEGERPOS     +ₙ_ #-}
{-# BUILTIN INTEGERNEGSUC −𝐒ₙ_ #-}

------------------------------------------
-- Constructors and deconstructors

-- Constructing negative number from ℕ
−ₙ_ : ℕ → ℤ
−ₙ (ℕ.𝟎)    = +ₙ ℕ.𝟎
−ₙ (ℕ.𝐒(x)) = −𝐒ₙ(x)

-- Intuitive constructor patterns
pattern 𝟎     = +ₙ (ℕ.𝟎)    -- Zero
pattern +𝐒ₙ n = +ₙ (ℕ.𝐒(n)) -- Positive integers (1,..)

-- Absolute value
absₙ : ℤ → ℕ
absₙ(+ₙ x)   = x
absₙ(−𝐒ₙ(x)) = ℕ.𝐒(x)

-- Syntax
instance
  ℤ-From-negative-ℕ : From-negative-ℕ (ℤ)
  from-negative-ℕ ⦃ ℤ-From-negative-ℕ ⦄ = −ₙ_

instance
  ℤ-From-ℕ : From-ℕ (ℤ)
  from-ℕ ⦃ ℤ-From-ℕ ⦄ = +ₙ_
