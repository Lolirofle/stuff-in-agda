module Numeral.Integer where

import      Lvl
open import Numeral.Natural      as ℕ using (ℕ)
import      Numeral.Natural.Oper as ℕ
open import Syntax.Number
open import Type

-- Integers
data ℤ : Type{Lvl.𝟎} where
  +ₙ_  : ℕ → ℤ -- Positive integers including zero from the naturals (0,1,..).
  −𝐒ₙ_ : ℕ → ℤ -- Negative integers from the naturals (..,−2,−1).

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
pattern 𝟎      = +ₙ(ℕ.𝟎)    -- Zero (0).
pattern +𝐒ₙ_ n = +ₙ(ℕ.𝐒(n)) -- Positive integers from the naturals (1,2,..).
pattern 𝟏      = +ₙ(ℕ.𝟏)    -- One (1).
pattern −𝟏     = −𝐒ₙ(ℕ.𝟎)   -- Negative one (−1).
{-# DISPLAY ℤ.+ₙ_ ℕ.𝟎  = 𝟎 #-}
{-# DISPLAY ℤ.+ₙ_ ℕ.𝟏  = 𝟏 #-}
{-# DISPLAY ℤ.−𝐒ₙ_ ℕ.𝟎 = −𝟏 #-}
{-# DISPLAY ℤ.+ₙ_(ℕ.𝐒(n)) = +𝐒ₙ_ n #-}

-- Absolute value
absₙ : ℤ → ℕ
absₙ(+ₙ x)   = x
absₙ(−𝐒ₙ(x)) = ℕ.𝐒(x)

-- Syntax
instance
  ℤ-InfiniteNegativeNumeral : InfiniteNegativeNumeral(ℤ)
  ℤ-InfiniteNegativeNumeral = InfiniteNegativeNumeral.intro(−ₙ_)

instance
  ℤ-InfiniteNumeral : InfiniteNumeral(ℤ)
  ℤ-InfiniteNumeral = InfiniteNumeral.intro(+ₙ_)
