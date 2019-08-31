module Numeral.Natural.Oper.Comparisons where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Numeral.Natural

-- Equality check
_≡?_ : ℕ → ℕ → Bool
𝟎    ≡? 𝟎    = 𝑇
𝐒(a) ≡? 𝐒(b) = (a ≡? b)
_    ≡? _    = 𝐹

-- Non-equality check
_≢?_ : ℕ → ℕ → Bool
x ≢? y = !(x ≡? y)

-- Positivity check
positive? : ℕ → Bool
positive? (𝟎)    = 𝐹
positive? (𝐒(_)) = 𝑇

-- Lesser-than check
_<?_ : ℕ → ℕ → Bool
𝟎    <? 𝐒(_) = 𝑇
𝐒(a) <? 𝐒(b) = (a <? b)
_    <? _    = 𝐹

-- Lesser-than or equals check
_≤?_ : ℕ → ℕ → Bool
𝟎    ≤? _    = 𝑇
𝐒(a) ≤? 𝐒(b) = (a ≤? b)
_    ≤? _    = 𝐹

-- Greater-than check
_>?_ : ℕ → ℕ → Bool
x >? y = y <? x

-- Greater-than or equals check
_≥?_ : ℕ → ℕ → Bool
x ≥? y = y ≤? x
