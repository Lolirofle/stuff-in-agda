module Numeral.Natural.Oper.Comparisons where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Numeral.Natural

-- Equality check
_≡?_ : ℕ → ℕ → Bool
𝟎    ≡? 𝟎    = 𝑇
𝐒(x) ≡? 𝐒(y) = (x ≡? y)
𝟎    ≡? 𝐒(_) = 𝐹
𝐒(_) ≡? 𝟎    = 𝐹
{-# BUILTIN NATEQUALS _≡?_ #-}

-- Non-equality check
_≢?_ : ℕ → ℕ → Bool
x ≢? y = !(x ≡? y)

-- Positivity check
positive? : ℕ → Bool
positive? (𝟎)    = 𝐹
positive? (𝐒(_)) = 𝑇

-- Lesser-than check
_<?_ : ℕ → ℕ → Bool
_    <? 𝟎    = 𝐹
𝟎    <? 𝐒(_) = 𝑇
𝐒(x) <? 𝐒(y) = (x <? y)
{-# BUILTIN NATLESS _<?_ #-}

-- Lesser-than or equals check
_≤?_ : ℕ → ℕ → Bool
x ≤? y = x <? 𝐒(y)

-- Greater-than check
_>?_ : ℕ → ℕ → Bool
x >? y = y <? x

-- Greater-than or equals check
_≥?_ : ℕ → ℕ → Bool
x ≥? y = y ≤? x
