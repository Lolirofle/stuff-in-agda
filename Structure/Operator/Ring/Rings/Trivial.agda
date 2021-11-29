module Structure.Operator.Ring.Rings.Trivial where

import      Lvl
open import Structure.Function
open import Structure.Operator.Group.Groups.Trivial
open import Structure.Operator.Monoid
open import Structure.Operator.Monoid.Monoids.Trivial
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.Setoid
open import Type
open import Type.Properties.MereProposition
open import Type.Properties.Singleton
open import Type.Properties.Singleton.Proofs

private variable ℓ ℓₑ : Lvl.Level
private variable T U : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(U) ⦄ ⦃ singleton : IsUnit(U) ⦄ (_+_ _⋅_ : U → U → U) (−_ : U → U) where
  private instance _ = unit-is-prop ⦃ equiv ⦄ ⦃ singleton ⦄

  trivialRing : Ring(_+_)(_⋅_)
  Ring.[+]-group trivialRing = trivialGroup(_+_)(−_)
  Ring.[⋅]-monoid trivialRing = trivialMonoid(_⋅_)
  Distributivityₗ.proof (Distributivity.left (Ring.[⋅][+]-distributivity trivialRing)) = uniqueness(U)
  Distributivityᵣ.proof (Distributivity.right (Ring.[⋅][+]-distributivity trivialRing)) = uniqueness(U)
  Ring.non-zero-relation trivialRing = defaultNonIdentityRelation
