import      Lvl
open import Structure.Operator.Vector
open import Structure.Setoid.WithLvl
open import Type

module Structure.Operator.Vector.Subspaces.Span
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
open import Numeral.CoordinateVector as Vec using () renaming (Vector to Vec)
open import Numeral.Finite
open import Numeral.Natural
open import Sets.ExtensionalPredicateSet as PredSet using (PredSet ; _∈_ ; [∋]-binaryRelator)
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

private variable n : ℕ
private variable vf : Vec(n)(V)
private variable sf : Vec(n)(S)

Span : Vec(n)(V) → PredSet(V)
Span(vf) = PredSet.⊶(linearCombination(vf))

Span-subspace : ∀{vf} → Subspace(Span{n}(vf))
∃.witness (_closed-under₂_.proof (Subspace.add-closure (Span-subspace {vf = vf})) ([∃]-intro sf₁) ([∃]-intro sf₂)) = Vec.map₂(_+ₛ_) sf₁ sf₂
∃.proof (_closed-under₂_.proof (Subspace.add-closure (Span-subspace {vf = vf})) {v₁} {v₂} ([∃]-intro sf₁ ⦃ p₁ ⦄) ([∃]-intro sf₂ ⦃ p₂ ⦄)) =
  linearCombination vf (Vec.map₂(_+ₛ_) sf₁ sf₂)            🝖[ _≡_ ]-[ preserving₂(linearCombination vf) (Vec.map₂(_+ₛ_)) (_+ᵥ_) ]
  (linearCombination vf sf₁) +ᵥ (linearCombination vf sf₂) 🝖[ _≡_ ]-[ congruence₂(_+ᵥ_) ⦃ [+ᵥ]-binary-operator ⦄ p₁ p₂ ]
  v₁ +ᵥ v₂                                                 🝖-end
∃.witness (_closed-under₁_.proof (Subspace.mul-closure Span-subspace {s}) ([∃]-intro sf)) = Vec.map(s ⋅ₛ_) sf
∃.proof (_closed-under₁_.proof (Subspace.mul-closure (Span-subspace {vf = vf}) {s}) {v} ([∃]-intro sf ⦃ p ⦄)) =
  linearCombination vf (i ↦ s ⋅ₛ sf(i)) 🝖[ _≡_ ]-[ preserving₁(linearCombination vf) (Vec.map(s ⋅ₛ_)) (s ⋅ₛᵥ_) ]
  s ⋅ₛᵥ (linearCombination vf sf)       🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅ₛᵥ_)(s) p ]
  s ⋅ₛᵥ v                               🝖-end
