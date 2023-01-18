module Numeral.CoordinateVector.Relations where

open import Logic
import      Lvl
open import Numeral.CoordinateVector
open import Numeral.Natural
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}
private variable d : ℕ

-- The vector's elements are all distinct (the vector contains no duplicate elements).
Distinct : ⦃ equiv : Equiv{ℓₑ}(T) ⦄ → Vector(d)(T) → Stmt
Distinct = Injective ⦃ [≡]-equiv ⦄
