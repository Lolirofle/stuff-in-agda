module Structure.Operator.Field {ℓ₁} {ℓ₂} where

import      Level as Lvl
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Relator.Equals{ℓ₁}{ℓ₂}
open import Structure.Operator.Group{ℓ₁}{ℓ₂}
open import Structure.Operator.Properties{ℓ₁}{ℓ₂}
open import Type{ℓ₂}

record FieldSym {T : Type} : Type where
  field
    _+_  : T → T → T
    _⋅_  : T → T → T
    [+]-id  : T
    [+]-inv : T → T
    [⋅]-id  : T
    [⋅]-inv : T → T
open FieldSym {{...}}

record Field {T : Type} {{sym : FieldSym{T}}} : Stmt where
  field
    [+]-group : Group (FieldSym._+_ sym) ([+]-id {T}) ([+]-inv {T})
    [⋅]-group : Group (FieldSym._⋅_ sym) ([⋅]-id {T}) ([⋅]-inv {T})
    [⋅][+]-distributivityₗ : Distributivityₗ (_⋅_ {T}) (_+_ {T})
    [⋅][+]-distributivityᵣ : Distributivityᵣ (_⋅_ {T}) (_+_ {T})
