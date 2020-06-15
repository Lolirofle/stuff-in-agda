module Structure.Operator.Field.VectorSpace where

import      Lvl
open import Structure.Setoid.WithLvl
open import Structure.Operator.Field
open import Structure.Operator.Properties using (associativity ; identityₗ ; distributivityᵣ)
open import Structure.Operator.Vector
open import Structure.Operator
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
  VectorSpace.scalarField                   fieldVectorSpace = field-structure
  VectorSpace.[⋅ₛᵥ]-binaryOperator          fieldVectorSpace = [⋅]-oper
  VectorSpace.[⋅ₛ][⋅ₛᵥ]-compatibility       fieldVectorSpace = associativity(_⋅_)
  VectorSpace.[⋅ₛᵥ][+ᵥ]-distributivityₗ     fieldVectorSpace = [⋅][+]-distributivityₗ
  VectorSpace.[⋅ₛᵥ][+ₛ][+ᵥ]-distributivityᵣ fieldVectorSpace = distributivityᵣ(_⋅_)(_+_)
