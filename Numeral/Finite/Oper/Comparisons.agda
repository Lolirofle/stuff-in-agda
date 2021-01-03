module Numeral.Finite.Oper.Comparisons where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Numeral.Finite
open import Numeral.Sign

-- Compare
_⋚?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → (−|0|+)
𝟎    ⋚? 𝟎    = 𝟎
𝟎    ⋚? 𝐒(b) = ➖
𝐒(a) ⋚? 𝟎    = ➕
𝐒(a) ⋚? 𝐒(b) = a ⋚? b

-- Equality check
_≡?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
a ≡? b = elim₃ 𝐹 𝑇 𝐹 (a ⋚? b)

-- Non-equality check
_≢?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
x ≢? y = !(x ≡? y)

-- Lesser-than check
_<?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
a <? b = elim₃ 𝑇 𝐹 𝐹 (a ⋚? b)

-- Lesser-than or equals check
_≤?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
a ≤? b = elim₃ 𝑇 𝑇 𝐹 (a ⋚? b)

-- Greater-than check
_>?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
x >? y = (y <? x)

-- Greater-than or equals check
_≥?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
x ≥? y = (y ≤? x)
