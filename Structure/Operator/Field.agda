module Structure.Operator.Field {l₁} {l₂} where

import      Level as Lvl
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Relator.Equals{l₁}{l₂}
open import Structure.Operator.Group{l₁}{l₂}
open import Structure.Operator.Properties{l₁}{l₂}
open import Type{l₂}

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
