module Structure.Operator.Vector lvl where

open import Logic(lvl)
open import Relator.Equals(lvl)
open import Structure.Operator.Field(lvl)
open import Structure.Operator.Group(lvl)
open import Structure.Operator.Properties(lvl)

record VectorSpaceSym {V S : Set} : Set where
  field
    {{fieldₛ}} : FieldSym{S}
    _+ᵥ_  : V → V → V
    _⋅ₛᵥ_  : S → V → V
    [+]-idᵥ  : V
    [+]-invᵥ  : V → V
open VectorSpaceSym {{...}}
open FieldSym {{...}}

record VectorSpace {V S : Set} {{sym : VectorSpaceSym {V} {S}}} : Stmt where
  field
    scalarField                  : Field {{fieldₛ {V} {S}}}
    vectorAbelianGroup           : AbelianGroup (_+ᵥ_ {V} {S}) ([+]-idᵥ {V} {S}) ([+]-invᵥ {V} {S})
    [⋅ₛ][⋅ₛᵥ]-compatibility      : Compatibility (_⋅_ {{fieldₛ {V} {S}}}) (_⋅ₛᵥ_ {V} {S})
    [⋅ₛᵥ]-id                     : Identityₗ (_⋅ₛᵥ_ {V} {S}) ([⋅]-id {{fieldₛ {V} {S}}})
    [⋅ₛᵥ][+ᵥ]-distributivity     : Distributivityₗ (_⋅ₛᵥ_ {V} {S}) (_+ᵥ_ {V} {S})
    [⋅ₛᵥ][+ₛ][+ᵥ]-distributivity : DistributivityIntoᵣ (_⋅ₛᵥ_ {V} {S}) (_+_ {{fieldₛ {V} {S}}}) (_+ᵥ_ {V} {S})
