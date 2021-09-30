module Structure.Operator.Group.Groups.Trivial where

import      Lvl
open import Structure.Function
open import Structure.Operator.Group
open import Structure.Operator.Monoid
open import Structure.Operator.Monoid.Monoids.Trivial
open import Structure.Operator.Proofs.EquivalentStructure
open import Structure.Operator.Properties
open import Structure.Setoid
open import Type
open import Type.Properties.MereProposition
open import Type.Properties.Singleton
open import Type.Properties.Singleton.Proofs

private variable ℓ ℓₑ : Lvl.Level
private variable T U : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(U) ⦄ ⦃ singleton : IsUnit(U) ⦄ (_▫_ : U → U → U) (inv : U → U) where
  private instance _ = unit-is-prop ⦃ equiv ⦄ ⦃ singleton ⦄

  trivialGroup : Group(_▫_)
  trivialGroup =
    let open Monoid(trivialMonoid(_▫_))
    in monoid-to-group(_▫_)(inv)
      ⦃ trivialMonoid(_▫_) ⦄
      ⦃ intro \_ → uniqueness(U) ⦄
      ⦃ intro
        ⦃ identity = identity-existence ⦄
        ⦃ left     = intro(uniqueness(U)) ⦄
        ⦃ right    = intro(uniqueness(U)) ⦄
      ⦄
