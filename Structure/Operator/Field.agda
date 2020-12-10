module Structure.Operator.Field where

import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Setoid.WithLvl
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Type

record Field {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  field
    ⦃ divisionRing ⦄      : DivisionRing(_+_)(_⋅_)
    ⦃ [⋅]-commutativity ⦄ : Commutativity(_⋅_)

  open DivisionRing(divisionRing) public

  field
     -- Note: This excludes the trivial ring and is unprovable from the other field axioms, and models where this is true are always "trivial/singleton rings".
    ⦃ distinct-identities ⦄ : DistinctIdentities

record FieldObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ structure ⦄ : Field(_+_)(_⋅_)
  open Field(structure) public
