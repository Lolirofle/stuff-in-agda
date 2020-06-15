module Structure.Operator.Vector.LinearMap where

open import Logic
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator.Vector
open import Structure.Operator.Field.VectorSpace
open import Structure.Setoid.WithLvl
open import Type
open import Syntax.Function

private variable ℓ ℓᵥ ℓᵥₗ ℓᵥᵣ ℓₛ ℓᵥₑ ℓᵥₑₗ ℓᵥₑᵣ ℓₛₑ : Lvl.Level
private variable V Vₗ Vᵣ S : Type{ℓ}
private variable _+ᵥ_ _+ᵥₗ_ _+ᵥᵣ_ : V → V → V
private variable _⋅ₛᵥ_ _⋅ₛᵥₗ_ _⋅ₛᵥᵣ_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S

module _
  ⦃ equiv-Vₗ : Equiv{ℓᵥₑₗ}(Vₗ) ⦄
  ⦃ equiv-Vᵣ : Equiv{ℓᵥₑᵣ}(Vᵣ) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpaceₗ : VectorSpace{V = Vₗ}{S = S}(_+ᵥₗ_)(_⋅ₛᵥₗ_)(_+ₛ_)(_⋅ₛ_))
  (vectorSpaceᵣ : VectorSpace{V = Vᵣ}{S = S}(_+ᵥᵣ_)(_⋅ₛᵥᵣ_)(_+ₛ_)(_⋅ₛ_))
  (f : Vₗ → Vᵣ)
  where

  record LinearMap : Type{Lvl.of(Vₗ) Lvl.⊔ ℓᵥₑₗ Lvl.⊔ ℓᵥₑᵣ Lvl.⊔ Lvl.of(S)} where
    constructor intro
    field
      ⦃ function-f ⦄ : Function(f)
      ⦃ preserves-[+ᵥ]  ⦄ : Preserving₂(f)(_+ᵥₗ_)(_+ᵥᵣ_)
      ⦃ preserves-[⋅ₛᵥ] ⦄ : ∀{s} → Preserving₁(f)(s ⋅ₛᵥₗ_)(s ⋅ₛᵥᵣ_)

_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_ : ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄ → VectorSpaceVObject{ℓᵥ = ℓᵥₗ}{ℓᵥₑ = ℓᵥₑₗ}{S = S}(_+ₛ_)(_⋅ₛ_) → VectorSpaceVObject{ℓᵥ = ℓᵥᵣ}{ℓᵥₑ = ℓᵥₑᵣ}{S = S}(_+ₛ_)(_⋅ₛ_) → Stmt
V₁ →ˡⁱⁿᵉᵃʳᵐᵃᵖ V₂ = ∃(LinearMap(VectorSpaceVObject.vectorSpace(V₁)) (VectorSpaceVObject.vectorSpace(V₂)))

_↔ˡⁱⁿᵉᵃʳᵐᵃᵖ_ : ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄ → VectorSpaceVObject{ℓᵥ = ℓᵥₗ}{ℓᵥₑ = ℓᵥₑₗ}{S = S}(_+ₛ_)(_⋅ₛ_) → VectorSpaceVObject{ℓᵥ = ℓᵥᵣ}{ℓᵥₑ = ℓᵥₑᵣ}{S = S}(_+ₛ_)(_⋅ₛ_) → Stmt
V₁ ↔ˡⁱⁿᵉᵃʳᵐᵃᵖ V₂ = ∃(f ↦ Invertible(f) ∧ LinearMap(VectorSpaceVObject.vectorSpace(V₁)) (VectorSpaceVObject.vectorSpace(V₂))(f))

module _
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpace : VectorSpace{V = V}{S = S}(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_))
  (f : V → V)
  where

  LinearOperator = LinearMap(vectorSpace)(vectorSpace) (f)

module _
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpace : VectorSpace{V = V}{S = S}(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_))
  (f : V → S)
  where

  LinearFunctional = LinearMap(vectorSpace)(fieldVectorSpace(VectorSpace.scalarField(vectorSpace))) (f)
