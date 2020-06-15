module Structure.Operator.Vector.FiniteDimensional.LinearMaps.ChangeOfBasis where

open import Functional
import      Lvl
open import Numeral.CoordinateVector as Vec using () renaming (Vector to Vec)
open import Numeral.Finite
open import Numeral.Natural
open import Structure.Function.Multi
open import Structure.Operator.Properties
open import Structure.Operator.Vector.FiniteDimensional
open import Structure.Operator.Vector.LinearCombination
open import Structure.Operator.Vector.LinearMap
open import Structure.Operator.Vector.Proofs
open import Structure.Operator.Vector
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Syntax.Transitivity
open import Type

private variable ℓ ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ : Lvl.Level
private variable V Vₗ Vᵣ S : Type{ℓ}
private variable _+ᵥ_ : V → V → V
private variable _⋅ₛᵥ_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S
private variable n : ℕ
private variable i j k : 𝕟(n)
private variable vf : Vec(n)(V)

module _
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpace : VectorSpace{V = V}{S = S}(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_))
  where

  open VectorSpace(vectorSpace)

  -- changeBasis : LinearOperator(vectorSpace)(linearCombination )
