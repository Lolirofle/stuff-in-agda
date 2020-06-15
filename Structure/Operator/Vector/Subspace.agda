import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid.WithLvl
open import Type

module Structure.Operator.Vector.Subspace
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {V : Type{ℓᵥ}} ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  {_+ᵥ_ : V → V → V}
  {_⋅ₛᵥ_ : S → V → V}
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  ⦃ vectorSpace : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) ⦄
  where

open VectorSpace(vectorSpace)

open import Logic
open import Logic.Predicate
open import Logic.Predicate.Equiv
open import Sets.ExtensionalPredicateSet as PredSet using (PredSet ; _∈_ ; [∋]-binaryRelator)
open import Structure.Container.SetLike using (SetElement)
private open module SetLikeFunctionProperties{ℓ} = Structure.Container.SetLike.FunctionProperties{C = PredSet{ℓ}(V)}(_∈_)
open import Structure.Operator.Vector
open import Structure.Operator.Vector.LinearCombination ⦃ vectorSpace = vectorSpace ⦄
open import Syntax.Transitivity

private variable ℓ : Lvl.Level

-- A subspace is a subset of V such that it is a vector space under the same operators.
record Subspace (Vₛ : PredSet{ℓ}(V)) : Stmt{ℓᵥ Lvl.⊔ ℓₛ Lvl.⊔ ℓ} where
  constructor intro
  field
    ⦃ add-closure ⦄ : Vₛ closed-under₂ (_+ᵥ_)
    ⦃ mul-closure ⦄ : ∀{s} → (Vₛ closed-under₁ (s ⋅ₛᵥ_))

  _+_ : SetElement(_∈_)(Vₛ) → SetElement(_∈_)(Vₛ) → SetElement(_∈_)(Vₛ)
  _+_ = [∃]-map₂(_+ᵥ_) (Vₛ closureUnder₂ (_+ᵥ_))

  _⋅_ : S → SetElement(_∈_)(Vₛ) → SetElement(_∈_)(Vₛ)
  _⋅_ s = [∃]-map(s ⋅ₛᵥ_) (Vₛ closureUnder₁ (s ⋅ₛᵥ_))

  -- TODO: A proof of this would be easier if a similar "substructure" relation was defined on groups and fields, but I am not sure if using PredSet is the correct choice (maybe this is unprovable when using this?). Another alternative is to use a general set structure by Structure.Container.SetLike
  postulate is-vectorSpace : VectorSpace{V = SetElement(_∈_)(Vₛ)}{S = S}(_+_)(_⋅_)(_+ₛ_)(_⋅ₛ_)
  -- is-vectorSpace = {!!}

SubspaceObject : ∀{ℓ} → Stmt
SubspaceObject{ℓ} = ∃(Subspace{ℓ})
