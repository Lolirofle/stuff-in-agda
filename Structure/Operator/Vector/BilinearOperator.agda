module Structure.Operator.Vector.BilinearOperator where

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
open import Structure.Operator.Properties using (Distributivityₗ ; Distributivityᵣ ; Distributivity)
open import Structure.Operator.Vector
open import Structure.Operator.Vector.LinearMap
open import Structure.Setoid
open import Type
open import Syntax.Function
open import Syntax.Transitivity

private variable ℓ ℓᵥ ℓᵥₗ ℓᵥᵣ ℓₛ ℓᵥₑ ℓᵥₑₗ ℓᵥₑᵣ ℓᵥₑ₁ ℓᵥₑ₂ ℓᵥₑ₃ ℓₛₑ ℓₙ₀ : Lvl.Level
private variable V Vₗ Vᵣ V₁ V₂ V₃ S : Type{ℓ}
private variable _+ᵥ_ _+ᵥₗ_ _+ᵥᵣ_ _+ᵥ₁_ _+ᵥ₂_ _+ᵥ₃_ : V → V → V
private variable _⋅ₛᵥ_ _⋅ₛᵥₗ_ _⋅ₛᵥᵣ_ _⋅ₛᵥ₁_ _⋅ₛᵥ₂_ _⋅ₛᵥ₃_ : S → V → V
private variable _+ₛ_ _⋅ₛ_ : S → S → S

module _
  ⦃ equiv-V : Equiv{ℓᵥₑ}(V) ⦄
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  (vectorSpace : VectorSpace{V = V}{S = S}(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) {ℓₙ₀})
  (_▫_ : V → V → V)
  where

  BilinearOperator = BilinearMap(vectorSpace)(vectorSpace)(vectorSpace) (_▫_)
  module BilinearOperator(bilinearOper : BilinearOperator) where
    open BilinearMap(bilinearOper) public

    instance
      [+ᵥ]-distributivityₗ : Distributivityₗ(_▫_)(_+ᵥ_)
      Distributivityₗ.proof [+ᵥ]-distributivityₗ {x}{y}{z} =
        x ▫ (y +ᵥ z)       🝖[ _≡_ ]-[ preserving₂(x ▫_)(_+ᵥ_)(_+ᵥ_) ⦃ LinearMap.preserves-[+ᵥ] (BilinearMap.linearMap₂ bilinearOper) ⦄ ]
        (x ▫ y) +ᵥ (x ▫ z) 🝖-end

    instance
      [+ᵥ]-distributivityᵣ : Distributivityᵣ(_▫_)(_+ᵥ_)
      Distributivityᵣ.proof [+ᵥ]-distributivityᵣ {x}{y}{z} =
        (x +ᵥ y) ▫ z       🝖[ _≡_ ]-[ preserving₂(_▫ z)(_+ᵥ_)(_+ᵥ_) ⦃ LinearMap.preserves-[+ᵥ] (BilinearMap.linearMap₁ bilinearOper) ⦄ ]
        (x ▫ z) +ᵥ (y ▫ z) 🝖-end

    instance
      [+ᵥ]-distributivity : Distributivity(_▫_)(_+ᵥ_)
      [+ᵥ]-distributivity = record{}
