module Structure.Operator.Field.VectorSpace where

import      Lvl
open import Structure.Function.Multi
open import Structure.Operator.Field
open import Structure.Operator.Properties using (associativity ; identityₗ ; distributivityᵣ)
open import Structure.Operator.Vector
open import Structure.Operator
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₗ ℓₗₑ : Lvl.Level
private variable T : Type{ℓ}
private variable _+_ _⋅_ : T → T → T

module _
  ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  ⦃ [+]-oper : BinaryOperator(_+_) ⦄
  ⦃ [⋅]-oper : BinaryOperator(_⋅_) ⦄
  (field-structure : Field{T = T}(_+_)(_⋅_))
  where
  open Field(field-structure)

  fieldVectorSpace : VectorSpace(_+_)(_⋅_)(_+_)(_⋅_)
  VectorSpace.scalarField               fieldVectorSpace = field-structure
  VectorSpace.[⋅ₛᵥ]-binaryOperator      fieldVectorSpace = [⋅]-oper
  VectorSpace.[⋅ₛᵥ][+ᵥ]-distributivityₗ fieldVectorSpace = [⋅][+]-distributivityₗ
  VectorSpace.[⋅ₛᵥ]ₗ[⋅]ᵣ-preserving     fieldVectorSpace = intro(associativity(_⋅_))
  VectorSpace.[⋅ₛᵥ]ₗ[+]-preserving      fieldVectorSpace = intro(distributivityᵣ(_⋅_)(_+_))
