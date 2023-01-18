module Numeral.Finite.Oper.Comparisons where

import      Lvl
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Functional
open import Numeral.Charge
open import Numeral.Finite
open import Numeral.Natural

-- Compare
_⋚?_ : ∀{a b} → 𝕟(a) → 𝕟(b) → Charge
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

positive? : ∀{n} → 𝕟(n) → Bool
positive? = _>? (𝟎{1})

isMax : ∀{n} → 𝕟(n) → Bool
isMax {𝐒 𝟎}    𝟎     = 𝑇
isMax {𝐒(𝐒 _)} 𝟎     = 𝐹
isMax          (𝐒 x) = isMax x
