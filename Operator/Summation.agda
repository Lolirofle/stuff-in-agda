open import Structure.Operator.Monoid
open import Structure.Setoid
open import Type

module Operator.Summation {ℓᵢ ℓ ℓₑ} {I : Type{ℓᵢ}} {T : Type{ℓ}} {_▫_ : T → T → T} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ monoid : Monoid{T = T}(_▫_) ⦄ where
open Monoid(monoid)

import      Lvl
open import Data.List
open import Data.List.Functions
open import Structure.Function
open import Structure.Operator

∑ : List(I) → (I → T) → T
∑(r) f = foldᵣ(_▫_) id (map f(r))
