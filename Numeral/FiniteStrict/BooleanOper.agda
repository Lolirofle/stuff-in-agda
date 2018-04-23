module Numeral.FiniteStrict.BooleanOper where

import      Lvl
open import Boolean
import      Boolean.Operators
open        Boolean.Operators.Programming
open import Numeral.FiniteStrict

-- Equality check
_≡?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
𝟎    ≡? 𝟎    = 𝑇
𝐒(a) ≡? 𝐒(b) = (a ≡? b)
_    ≡? _    = 𝐹

-- Non-equality check
_≢?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
x ≢? y = !(x ≡? y)

-- Lesser-than check
_<?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
𝟎    <? 𝐒(_) = 𝑇
𝐒(a) <? 𝐒(b) = (a <? b)
_    <? _    = 𝐹

-- Lesser-than or equals check
_≤?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
𝟎    ≤? _    = 𝑇
𝐒(a) ≤? 𝐒(b) = (a <? b)
_    ≤? _    = 𝐹

-- Greater-than check
_>?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
x >? y = !(x ≤? y)

-- Greater-than or equals check
_≥?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
x ≥? y = !(x <? y)