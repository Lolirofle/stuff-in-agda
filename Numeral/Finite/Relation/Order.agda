module Numeral.Finite.Relation.Order where

import      Lvl
open import Data.Boolean.Stmt
open import Functional
open import Numeral.Finite
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Natural
open import Type

private variable an bn cn n : ℕ
private variable a : 𝕟(an)
private variable b : 𝕟(bn)
private variable c : 𝕟(cn)

_≤_ : 𝕟(an) → 𝕟(bn) → Type
_≤_ = IsTrue ∘₂ (_≤?_)

_≥_ : 𝕟(an) → 𝕟(bn) → Type
_≥_ = IsTrue ∘₂ (_≥?_)

_<_ : 𝕟(an) → 𝕟(bn) → Type
_<_ = IsTrue ∘₂ (_<?_)

_>_ : 𝕟(an) → 𝕟(bn) → Type
_>_ = IsTrue ∘₂ (_>?_)

_≡_ : 𝕟(an) → 𝕟(bn) → Type
_≡_ = IsTrue ∘₂ (_≡?_)

_≢_ : 𝕟(an) → 𝕟(bn) → Type
_≢_ = IsTrue ∘₂ (_≢?_)

