module Structure.Operator.Field lvl where

open import Logic(lvl)
open import Relator.Equals(lvl)
open import Structure.Operator.Group(lvl)
open import Structure.Operator.Properties(lvl)

record FieldSym {T : Set} : Set where
  field
    _+_  : T → T → T
    _⋅_  : T → T → T
    [+]-id  : T
    [+]-inv : T → T
    [⋅]-id  : T
    [⋅]-inv : T → T
open FieldSym {{...}}

record Field {T : Set} {{sym : FieldSym{T}}} : Stmt where
  field
    [+]-group : Group (FieldSym._+_ sym) ([+]-id {T}) ([+]-inv {T})
    [⋅]-group : Group (FieldSym._⋅_ sym) ([⋅]-id {T}) ([⋅]-inv {T})
    [⋅][+]-distributivityₗ : Distributivityₗ (_⋅_ {T}) (_+_ {T})
    [⋅][+]-distributivityᵣ : Distributivityᵣ (_⋅_ {T}) (_+_ {T})
