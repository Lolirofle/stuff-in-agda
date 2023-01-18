import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid
open import Type

module Structure.Operator.Vector.InfiniteDimensional
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ ℓₙ₀}
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  {_+ᵥ_ : V → V → V}
  {_⋅ₛᵥ_ : S → V → V}
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀} ⦄
  where

open VectorSpace(vectorSpace)

open import Data.Tuple using (_⨯_ ; _,_)
open import Logic
open import Logic.Predicate
open import Numeral.CoordinateVector as Vec using () renaming (Vector to Vec)
open import Numeral.CoordinateVector.Relations as Vec
open import Numeral.Finite
open import Numeral.Natural
open import Sets.ExtensionalPredicateSet as PredSet using (PredSet ; _∈_ ; [∋]-binaryRelator)
import      Structure.Operator.Vector.FiniteDimensional as FiniteDimensional
open import Structure.Operator.Vector.LinearCombination ⦃ vectorSpace = vectorSpace ⦄
open import Syntax.Function

private variable ℓ ℓₗ : Lvl.Level
private variable n : ℕ

InfiniteDimensional = ∀{n} → ∃(vf ↦ FiniteDimensional.Spanning ⦃ vectorSpace = vectorSpace ⦄ {n}(vf))

-- TODO: Not sure if correct
-- This states that all finite sequences `vf` of length `n` (in terms of `Vec`) that consists of elements from the set `vs` satisfies `P`.
-- This can be used in infinite-dimensional vector spaces to define linear independence, span and basis by: `∃(n ↦ AllFiniteSubsets(n)(P)(vs))`
AllFiniteSubsets : (n : ℕ) → (Vec(n)(V) → Stmt{ℓ}) → (PredSet{ℓₗ}(V) → Stmt)
AllFiniteSubsets(n) P(vs) = (∀{vf : Vec(n)(V)} ⦃ distinct : Vec.Distinct(vf) ⦄ → (∀{i : 𝕟(n)} → (Vec.proj(vf)(i) ∈ vs)) → P(vf))

LinearlyIndependent : PredSet{ℓₗ}(V) → Stmt
LinearlyIndependent(vs) = ∃(n ↦ AllFiniteSubsets(n)(FiniteDimensional.LinearlyIndependent)(vs))

Spanning : PredSet{ℓₗ}(V) → Stmt
Spanning(vs) = ∃(n ↦ AllFiniteSubsets(n)(FiniteDimensional.Spanning)(vs))

-- Also called: Hamel basis (TODO: I think)
Basis : PredSet{ℓₗ}(V) → Stmt
Basis(vs) = ∃(n ↦ AllFiniteSubsets(n)(FiniteDimensional.Basis)(vs))
