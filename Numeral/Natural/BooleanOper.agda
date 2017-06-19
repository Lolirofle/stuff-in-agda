module Numeral.Natural.BooleanOper where

import      Level as Lvl
open import Boolean{Lvl.𝟎}
import      Boolean.Operators
open        Boolean.Operators.Programming{Lvl.𝟎}
open import Numeral.Natural

-- Equality check
_≡?_ : ℕ → ℕ → Bool
𝟎    ≡? 𝟎    = 𝑇
𝐒(a) ≡? 𝐒(b) = (a ≡? b)
_    ≡? _    = 𝐹

-- Lesser-than check
_<?_ : ℕ → ℕ → Bool
𝟎    <? 𝐒(_) = 𝑇
𝐒(a) <? 𝐒(b) = (a <? b)
_    <? _    = 𝐹

-- Lesser-than or equals check
_≤?_ : ℕ → ℕ → Bool
𝟎    ≤? _    = 𝑇
𝐒(a) ≤? 𝐒(b) = (a <? b)
_    ≤? _    = 𝐹

-- Greater-than check
_>?_ : ℕ → ℕ → Bool
x >? y = !(x ≤? y)

-- Greater-than or equals check
_≥?_ : ℕ → ℕ → Bool
x ≥? y = !(x <? y)
