module Operator.Summation.Range where

import      Lvl
open import Data.List
open import Data.List.Functions
open import Numeral.Natural
open import Type

_‥_ : ℕ → ℕ → List(ℕ)
_   ‥ 𝟎   = ∅
𝟎   ‥ 𝐒 b = 𝟎 ⊰ map 𝐒(𝟎 ‥ b)
𝐒 a ‥ 𝐒 b = map 𝐒(a ‥ b)

‥_ : ℕ → List(ℕ)
‥ b = 𝟎 ‥ b

_‥₌_ : ℕ → ℕ → List(ℕ)
a ‥₌ b = a ‥ 𝐒(b)

‥₌_ : ℕ → List(ℕ)
‥₌ b = 𝟎 ‥₌ b
