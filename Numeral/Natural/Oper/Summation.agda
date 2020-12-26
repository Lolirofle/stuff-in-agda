open import Structure.Operator.Monoid
open import Structure.Setoid
open import Type

module Numeral.Natural.Oper.Summation {ℓ ℓₑ} {T : Type{ℓ}} {_▫_ : T → T → T} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ monoid : Monoid{T = T}(_▫_) ⦄ where
open Monoid(monoid)

import      Lvl
open import Data.List
open import Data.List.Functions
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Structure.Function
open import Structure.Operator

∑ : List(ℕ) → (ℕ → T) → T
∑(r) f = foldᵣ(_▫_) id (map f(r))
