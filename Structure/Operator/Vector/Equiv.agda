module Structure.Operator.Vector.LinearMap.Equiv where

open import Functional
open import Function.Proofs
open import Logic.Predicate
import      Lvl
open import Structure.Category
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Operator.Properties
open import Structure.Operator.Vector.LinearMap
open import Structure.Operator.Vector.LinearMaps
open import Structure.Operator.Vector.Proofs
open import Structure.Operator.Vector
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓᵥ ℓᵥₗ ℓᵥᵣ ℓᵥ₁ ℓᵥ₂ ℓᵥ₃ ℓₛ ℓᵥₑ ℓᵥₑₗ ℓᵥₑᵣ ℓᵥₑ₁ ℓᵥₑ₂ ℓᵥₑ₃ ℓₛₑ ℓₙ₀ : Lvl.Level
private variable V Vₗ Vᵣ V₁ V₂ V₃ S : Type{ℓ}
private variable _+ᵥ_ _+ᵥₗ_ _+ᵥᵣ_ _+ᵥ₁_ _+ᵥ₂_ _+ᵥ₃_ : V → V → V
private variable _⋅ₛᵥ_ _⋅ₛᵥₗ_ _⋅ₛᵥᵣ_ _⋅ₛᵥ₁_ _⋅ₛᵥ₂_ _⋅ₛᵥ₃_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S
private variable f g : Vₗ → Vᵣ

open VectorSpace ⦃ … ⦄

module _ ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄ where
  private variable A B : VectorSpaceVObject {ℓᵥ}{_}{ℓᵥₑ}{ℓₛₑ} ⦃ equiv-S ⦄ (_+ₛ_)(_⋅ₛ_) {ℓₙ₀}

  [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv : Equiv(A →ˡⁱⁿᵉᵃʳᵐᵃᵖ B)
  Equiv._≡_ [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv ([∃]-intro f) ([∃]-intro g) = {!!}
  Equiv.equivalence [_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_]-equiv = {!!}
