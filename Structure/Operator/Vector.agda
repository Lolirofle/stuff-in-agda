module Structure.Operator.Vector {l₁} {l₂} where

import      Level as Lvl
open import Logic.Propositional{l₁ Lvl.⊔ l₂}
open import Relator.Equals{l₁}{l₂}
open import Structure.Operator.Field{l₁}{l₂}
open import Structure.Operator.Group{l₁}{l₂}
open import Structure.Operator.Properties{l₁}{l₂}
open import Type{l₂}

record VectorSpaceSym {V S : Type} : Type where
  field
    {{fieldₛ}} : FieldSym{S}
    _+ᵥ_  : V → V → V
    _⋅ₛᵥ_  : S → V → V
    [+]-idᵥ  : V
    [+]-invᵥ  : V → V
open VectorSpaceSym {{...}}
open FieldSym {{...}}

record VectorSpace {V S : Type} {{sym : VectorSpaceSym {V} {S}}} : Stmt where
  field
    scalarField                  : Field {{fieldₛ {V} {S}}}
    vectorAbelianGroup           : AbelianGroup (_+ᵥ_ {V} {S}) ([+]-idᵥ {V} {S}) ([+]-invᵥ {V} {S})
    [⋅ₛ][⋅ₛᵥ]-compatibility      : Compatibility (_⋅_ {{fieldₛ {V} {S}}}) (_⋅ₛᵥ_ {V} {S})
    [⋅ₛᵥ]-id                     : Identityₗ (_⋅ₛᵥ_ {V} {S}) ([⋅]-id {{fieldₛ {V} {S}}})
    [⋅ₛᵥ][+ᵥ]-distributivity     : Distributivityₗ (_⋅ₛᵥ_ {V} {S}) (_+ᵥ_ {V} {S})
    [⋅ₛᵥ][+ₛ][+ᵥ]-distributivity : DistributivityPatternᵣ (_⋅ₛᵥ_ {V} {S}) (_+_ {{fieldₛ {V} {S}}}) (_+ᵥ_ {V} {S})
