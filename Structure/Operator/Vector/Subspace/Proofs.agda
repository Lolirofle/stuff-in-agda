import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid
open import Type

module Structure.Operator.Vector.Subspace.Proofs
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  {_+ᵥ_ : V → V → V}
  {_⋅ₛᵥ_ : S → V → V}
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) ⦄
  where

open VectorSpace(vectorSpace)

open import Logic.Predicate
open import Logic.Propositional
open import Numeral.CoordinateVector as Vec using () renaming (Vector to Vec)
open import Numeral.Finite
open import Numeral.Natural
open import Sets.ExtensionalPredicateSet as PredSet using (PredSet ; _∈_ ; _∪_ ; ⋂ᵢ ; _⊇_ ; _⊆_)
open import Structure.Container.SetLike using (SetElement)
private open module SetLikeFunctionProperties{ℓ} = Structure.Container.SetLike.FunctionProperties{C = PredSet{ℓ}(V)}{E = V}(_∈_)
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Operator.Vector.LinearCombination        ⦃ vectorSpace = vectorSpace ⦄
open import Structure.Operator.Vector.LinearCombination.Proofs 
open import Structure.Operator.Vector.Subspace                 ⦃ vectorSpace = vectorSpace ⦄
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable I : Type{ℓ}
private variable n : ℕ
private variable vf : Vec(n)(V)
private variable sf : Vec(n)(S)

-- TODO
[⋂ᵢ]-subspace : ∀{Vsf : I → PredSet{ℓ}(V)} → (∀{i} → Subspace(Vsf(i))) → Subspace(⋂ᵢ Vsf)
[∪]-subspace : ∀{Vₛ₁ Vₛ₂} → Subspace{ℓ₁}(Vₛ₁) → Subspace{ℓ₂}(Vₛ₂) → (((Vₛ₁ ⊇ Vₛ₂) ∨ (Vₛ₁ ⊆ Vₛ₂)) ↔ Subspace(Vₛ₁ ∪ Vₛ₂))
