module Structure.Operator.Field.VectorSpace where

import      Lvl
open import Structure.Function.Multi
open import Structure.Operator.Field
open import Structure.Operator.Properties using (associativity ; identityₗ ; distributivityᵣ)
open import Structure.Operator.Vector
open import Structure.Operator
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₗ ℓₗₑ ℓₙ₀ : Lvl.Level
private variable T : Type{ℓ}
private variable _+_ _⋅_ : T → T → T

module _
  ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  (field-structure : Field{T = T}(_+_)(_⋅_) {ℓₙ₀})
  where
  open Field(field-structure)

  fieldScalarMultiplicationCore : ScalarMultiplicationCore(_+_)(_⋅_)(_+_)(_⋅_)
  ScalarMultiplicationCore.[⋅ₛᵥ][+ᵥ]-distributivityₗ fieldScalarMultiplicationCore = [⋅][+]-distributivityₗ
  ScalarMultiplicationCore.[⋅ₛᵥ]ₗ[⋅]ᵣ-preserving     fieldScalarMultiplicationCore = intro(associativity(_⋅_))
  ScalarMultiplicationCore.[⋅ₛᵥ]ₗ[+]-preserving      fieldScalarMultiplicationCore = intro(distributivityᵣ(_⋅_)(_+_))

  fieldVectorSpace : VectorSpace(_+_)(_⋅_)(_+_)(_⋅_) {ℓₙ₀}
  VectorSpace.scalarField fieldVectorSpace = field-structure
  ScalarMultiplicationCore.[⋅ₛᵥ][+ᵥ]-distributivityₗ (VectorSpace.[⋅ₛᵥ]-scalarMultiplication fieldVectorSpace) = [⋅][+]-distributivityₗ
  ScalarMultiplicationCore.[⋅ₛᵥ]ₗ[⋅]ᵣ-preserving     (VectorSpace.[⋅ₛᵥ]-scalarMultiplication fieldVectorSpace) = intro(associativity(_⋅_))
  ScalarMultiplicationCore.[⋅ₛᵥ]ₗ[+]-preserving      (VectorSpace.[⋅ₛᵥ]-scalarMultiplication fieldVectorSpace) = intro(distributivityᵣ(_⋅_)(_+_))
