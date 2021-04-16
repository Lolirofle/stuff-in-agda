module Numeral.Finite.Oper.Comparisons where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Functional
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
_≡?_ = elim₃ 𝐹 𝑇 𝐹 ∘₂ (_⋚?_)

-- Non-equality check
_≢?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
_≢?_ = elim₃ 𝑇 𝐹 𝑇 ∘₂ (_⋚?_)

-- Lesser-than check
_<?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
_<?_ = elim₃ 𝑇 𝐹 𝐹 ∘₂ (_⋚?_)

-- Lesser-than or equals check
_≤?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
_≤?_ = elim₃ 𝑇 𝑇 𝐹 ∘₂ (_⋚?_)

-- Greater-than check
_>?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
_>?_ = elim₃ 𝐹 𝐹 𝑇 ∘₂ (_⋚?_)

-- Greater-than or equals check
_≥?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Bool
_≥?_ = elim₃ 𝐹 𝑇 𝑇 ∘₂ (_⋚?_)
