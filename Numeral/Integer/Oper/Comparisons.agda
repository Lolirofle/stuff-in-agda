module Numeral.Integer.Oper.Comparisons where

open import Data.Boolean
open import Functional
import      Lvl
open import Numeral.Charge
open import Numeral.Integer
import      Numeral.Natural.Oper.Comparisons as ℕ
open import Type

-- Compare
_⋚?_ : ℤ → ℤ → Charge
(+ₙ x)  ⋚? (+ₙ y)  = x ℕ.⋚? y
(+ₙ x)  ⋚? (−𝐒ₙ y) = ➕
(−𝐒ₙ x) ⋚? (+ₙ y)  = ➖
(−𝐒ₙ x) ⋚? (−𝐒ₙ y) = y ℕ.⋚? x

-- Equality check
_≡?_ : ℤ → ℤ → Bool
_≡?_ = elim₃ 𝐹 𝑇 𝐹 ∘₂ (_⋚?_)

-- Non-equality check
_≢?_ : ℤ → ℤ → Bool
_≢?_ = elim₃ 𝑇 𝐹 𝑇 ∘₂ (_⋚?_)

-- Lesser-than check
_<?_ : ℤ → ℤ → Bool
_<?_ = elim₃ 𝑇 𝐹 𝐹 ∘₂ (_⋚?_)

-- Lesser-than or equals check
_≤?_ : ℤ → ℤ → Bool
_≤?_ = elim₃ 𝑇 𝑇 𝐹 ∘₂ (_⋚?_)

-- Greater-than check
_>?_ : ℤ → ℤ → Bool
_>?_ = elim₃ 𝐹 𝐹 𝑇 ∘₂ (_⋚?_)

-- Greater-than or equals check
_≥?_ : ℤ → ℤ → Bool
_≥?_ = elim₃ 𝐹 𝑇 𝑇 ∘₂ (_⋚?_)
