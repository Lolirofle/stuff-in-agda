module Structure.Operator.Algebra where

open import Logic.Predicate
import      Lvl
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.Operator.Vector
open import Structure.Operator.Vector.BilinearOperator
open import Structure.Operator.Vector.LinearMap
open import Structure.Setoid
open import Type

module _
  {ℓᵥ ℓₛ ℓᵥₑ ℓₛₑ}
  {V : Type{ℓᵥ}} ⦃ _ : Equiv{ℓᵥₑ}(V) ⦄
  {S : Type{ℓₛ}} ⦃ _ : Equiv{ℓₛₑ}(S) ⦄
  (_+ᵥ_ : V → V → V)
  (_⋅ᵥ_ : V → V → V)
  (_⋅ₛᵥ_ : S → V → V)
  (_+ₛ_ : S → S → S)
  (_⋅ₛ_ : S → S → S)
  {ℓᵥₙ₀ ℓₛₙ₀}
  where

  record Algebra : Type{ℓₛₑ Lvl.⊔ ℓₛ Lvl.⊔ ℓᵥₑ Lvl.⊔ ℓᵥ Lvl.⊔ Lvl.𝐒(ℓᵥₙ₀ Lvl.⊔ ℓₛₙ₀)} where
    constructor intro
    field
      ⦃ vectorSpace ⦄      : VectorSpace(_+ᵥ_)(_⋅ₛᵥ_)(_+ₛ_)(_⋅ₛ_) {ℓₛₙ₀}
      ⦃ [⋅ᵥ]-bilinearity ⦄ : BilinearOperator vectorSpace (_⋅ᵥ_)
      ⦃ non-zero-vector-relation ⦄ : NonIdentityRelation(VectorSpace.[+ᵥ]-monoid vectorSpace) {ℓᵥₙ₀}
    open VectorSpace(vectorSpace) public
    open BilinearOperator _ _ ([⋅ᵥ]-bilinearity) public

    vectorRing : ⦃ Associativity(_⋅ᵥ_) ⦄ → ⦃ ∃(Identity(_⋅ᵥ_)) ⦄ → Ring(_+ᵥ_)(_⋅ᵥ_) {ℓᵥₙ₀}
    Monoid.binaryOperator (Ring.[⋅]-monoid vectorRing) = BilinearMap.binaryOperator [⋅ᵥ]-bilinearity

  -- TODO: UnitalAssociativeAlgebra
