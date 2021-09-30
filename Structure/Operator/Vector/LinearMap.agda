module Structure.Operator.Vector.LinearMap where

open import Functional
open import Logic
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Operator.Field.VectorSpace
open import Structure.Operator.Properties using (Distributivityₗ ; Distributivityᵣ)
open import Structure.Operator.Vector
open import Structure.Setoid
open import Type
open import Syntax.Function
open import Syntax.Transitivity

private variable ℓ ℓᵥ ℓᵥₗ ℓᵥᵣ ℓₛ ℓᵥₑ ℓᵥₑₗ ℓᵥₑᵣ ℓᵥₑ₁ ℓᵥₑ₂ ℓᵥₑ₃ ℓₛₑ ℓₙ₀ ℓₙ₀ₗ ℓₙ₀ᵣ ℓₙ₀₁ ℓₙ₀₂ ℓₙ₀₃ : Lvl.Level
private variable V Vₗ Vᵣ V₁ V₂ V₃ S : Type{ℓ}
private variable _+ᵥ_ _+ᵥₗ_ _+ᵥᵣ_ _+ᵥ₁_ _+ᵥ₂_ _+ᵥ₃_ : V → V → V
private variable _⋅ₛᵥ_ _⋅ₛᵥₗ_ _⋅ₛᵥᵣ_ _⋅ₛᵥ₁_ _⋅ₛᵥ₂_ _⋅ₛᵥ₃_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S

module _
  ⦃ equiv-Vₗ : Equiv{ℓᵥₑₗ}(Vₗ) ⦄
  ⦃ equiv-Vᵣ : Equiv{ℓᵥₑᵣ}(Vᵣ) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpaceₗ : VectorSpace{V = Vₗ}{S = S}(_+ᵥₗ_)(_⋅ₛᵥₗ_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀ₗ})
  (vectorSpaceᵣ : VectorSpace{V = Vᵣ}{S = S}(_+ᵥᵣ_)(_⋅ₛᵥᵣ_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀ᵣ})
  (f : Vₗ → Vᵣ)
  where

  record LinearMap : Type{Lvl.of(Vₗ) Lvl.⊔ ℓᵥₑₗ Lvl.⊔ ℓᵥₑᵣ Lvl.⊔ Lvl.of(S)} where
    constructor intro
    field
      ⦃ function ⦄ : Function(f)
      ⦃ preserves-[+ᵥ]  ⦄ : Preserving₂(f)(_+ᵥₗ_)(_+ᵥᵣ_)
      ⦃ preserves-[⋅ₛᵥ] ⦄ : ∀{s} → Preserving₁(f)(s ⋅ₛᵥₗ_)(s ⋅ₛᵥᵣ_)

_→ˡⁱⁿᵉᵃʳᵐᵃᵖ_ : ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄ → VectorSpaceVObject{ℓᵥ = ℓᵥₗ}{ℓᵥₑ = ℓᵥₑₗ}{S = S}(_+ₛ_)(_⋅ₛ_) {ℓₙ₀ₗ} → VectorSpaceVObject{ℓᵥ = ℓᵥᵣ}{ℓᵥₑ = ℓᵥₑᵣ}{S = S}(_+ₛ_)(_⋅ₛ_) {ℓₙ₀ᵣ} → Stmt
V₁ →ˡⁱⁿᵉᵃʳᵐᵃᵖ V₂ = ∃(LinearMap(VectorSpaceVObject.vectorSpace(V₁)) (VectorSpaceVObject.vectorSpace(V₂)))

_↔ˡⁱⁿᵉᵃʳᵐᵃᵖ_ : ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄ → VectorSpaceVObject{ℓᵥ = ℓᵥₗ}{ℓᵥₑ = ℓᵥₑₗ}{S = S}(_+ₛ_)(_⋅ₛ_) {ℓₙ₀ₗ} → VectorSpaceVObject{ℓᵥ = ℓᵥᵣ}{ℓᵥₑ = ℓᵥₑᵣ}{S = S}(_+ₛ_)(_⋅ₛ_) {ℓₙ₀ᵣ} → Stmt
V₁ ↔ˡⁱⁿᵉᵃʳᵐᵃᵖ V₂ = ∃(f ↦ Invertible(f) ∧ LinearMap(VectorSpaceVObject.vectorSpace(V₁)) (VectorSpaceVObject.vectorSpace(V₂))(f))

module _
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpace : VectorSpace{V = V}{S = S}(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀})
  (f : V → V)
  where

  LinearOperator = LinearMap(vectorSpace)(vectorSpace) (f)

module _
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpace : VectorSpace{V = V}{S = S}(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀})
  (f : V → S)
  where

  LinearFunctional = LinearMap(vectorSpace)(fieldVectorSpace(VectorSpace.scalarField(vectorSpace))) (f)

module _
  ⦃ equiv-V₁ : Equiv{ℓᵥₑ₁}(V₁) ⦄
  ⦃ equiv-V₂ : Equiv{ℓᵥₑ₂}(V₂) ⦄
  ⦃ equiv-V₃ : Equiv{ℓᵥₑ₃}(V₃) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpace₁ : VectorSpace{V = V₁}{S = S}(_+ᵥ₁_)(_⋅ₛᵥ₁_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀₁})
  (vectorSpace₂ : VectorSpace{V = V₂}{S = S}(_+ᵥ₂_)(_⋅ₛᵥ₂_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀₂})
  (vectorSpace₃ : VectorSpace{V = V₃}{S = S}(_+ᵥ₃_)(_⋅ₛᵥ₃_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀₃})
  (f : V₁ → V₂ → V₃)
  where

  record BilinearMap : Type{Lvl.of(V₁) Lvl.⊔ Lvl.of(V₂) Lvl.⊔ ℓᵥₑ₁ Lvl.⊔ ℓᵥₑ₂ Lvl.⊔ ℓᵥₑ₃ Lvl.⊔ Lvl.of(S)} where
    constructor intro
    field
      ⦃ linearMap₁ ⦄ : ∀{y} → LinearMap vectorSpace₁ vectorSpace₃ (x ↦ f(x)(y))
      ⦃ linearMap₂ ⦄ : ∀{x} → LinearMap vectorSpace₂ vectorSpace₃ (y ↦ f(x)(y))

    open module LinearMapₗ{y} = LinearMap(linearMap₁{y}) renaming (function to functionₗ ; preserves-[+ᵥ] to preserves-[+ᵥ]ₗ ; preserves-[⋅ₛᵥ] to preserves-[⋅ₛᵥ]ₗ) public
    open module LinearMapᵣ{x} = LinearMap(linearMap₂{x}) renaming (function to functionᵣ ; preserves-[+ᵥ] to preserves-[+ᵥ]ᵣ ; preserves-[⋅ₛᵥ] to preserves-[⋅ₛᵥ]ᵣ) public

    binaryOperator : BinaryOperator(f)
    binaryOperator = functions-to-binaryOperator(f) ⦃ functionₗ ⦄ ⦃ functionᵣ ⦄
