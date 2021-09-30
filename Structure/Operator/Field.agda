module Structure.Operator.Field where

import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Operator.Group
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Type

record Field {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) {ℓₙ₀} : Stmt{ℓ Lvl.⊔ ℓₑ Lvl.⊔ Lvl.𝐒(ℓₙ₀)} where
  field
    ⦃ divisionRing ⦄      : DivisionRing(_+_)(_⋅_) {ℓₙ₀}
    ⦃ [+]-commutativity ⦄ : Commutativity(_+_) -- TODO: It is possible to derive this from the other axioms
    ⦃ [⋅]-commutativity ⦄ : Commutativity(_⋅_)

  open DivisionRing(divisionRing) public

  field
     -- Note: This excludes the trivial ring and is unprovable from the other field axioms, and models where this is true are always "trivial/singleton rings".
    ⦃ distinct-identities ⦄ : DistinctIdentities

  instance
    [+]-commutativeGroup : CommutativeGroup(_+_)
    [+]-commutativeGroup = intro

record FieldObject {ℓ ℓₑ ℓₙ₀} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ Lvl.⊔ ℓₙ₀)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ structure ⦄ : Field(_+_)(_⋅_) {ℓₙ₀}
  open Field(structure) public
