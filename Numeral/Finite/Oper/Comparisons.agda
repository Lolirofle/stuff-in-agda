module Numeral.Finite.Oper.Comparisons where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Numeral.Finite
open import Numeral.Sign

-- Equality check
_≡?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
𝟎    ≡? 𝟎    = 𝑇
𝐒(a) ≡? 𝐒(b) = (a ≡? b)
{-# CATCHALL #-}
_    ≡? _    = 𝐹

-- Non-equality check
_≢?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
x ≢? y = !(x ≡? y)

-- Lesser-than check
_<?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
𝟎    <? 𝐒(_) = 𝑇
𝐒(a) <? 𝐒(b) = (a <? b)
{-# CATCHALL #-}
_    <? _    = 𝐹

-- Lesser-than or equals check
_≤?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
𝟎    ≤? _    = 𝑇
𝐒(a) ≤? 𝐒(b) = (a ≤? b)
{-# CATCHALL #-}
_    ≤? _    = 𝐹

-- Greater-than check
_>?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
x >? y = (y <? x)

-- Greater-than or equals check
_≥?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
x ≥? y = (y ≤? x)

-- Compare
_⋚?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → (−|0|+)
𝟎    ⋚? 𝟎    = 𝟎
𝟎    ⋚? 𝐒(b) = ➖
𝐒(a) ⋚? 𝟎    = ➕
𝐒(a) ⋚? 𝐒(b) = a ⋚? b
