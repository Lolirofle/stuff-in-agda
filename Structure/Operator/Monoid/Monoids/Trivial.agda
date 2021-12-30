module Structure.Operator.Monoid.Monoids.Trivial where

open import Logic.Predicate
import      Lvl
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Monoid
open import Structure.Operator.Properties
open import Structure.Setoid
open import Type
open import Type.Properties.MereProposition
open import Type.Properties.Singleton
open import Type.Properties.Proofs

private variable ℓ ℓₑ : Lvl.Level
private variable T U : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(U) ⦄ ⦃ singleton : IsUnit(U) ⦄ (_▫_ : U → U → U) where
  private instance _ = unit-is-prop ⦃ equiv ⦄ ⦃ singleton ⦄

  trivialMonoid : Monoid(_▫_)
  BinaryOperator.congruence                (Monoid.binaryOperator    trivialMonoid) _ _ = uniqueness(U)
  Associativity.proof                      (Monoid.associativity      trivialMonoid)     = uniqueness(U)
  ∃.witness                                (Monoid.identity-existence trivialMonoid)     = unit
  Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence trivialMonoid)))   = uniqueness(U)
  Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence trivialMonoid)))   = uniqueness(U)
