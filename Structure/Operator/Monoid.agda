module Structure.Operator.Monoid where

import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Operator.Properties hiding (associativity ; identityₗ ; identityᵣ)
open import Structure.Operator
open import Type

-- A type and a binary operator using this type is a monoid when:
-- • The operator is associative.
-- • The operator have an identity in both directions.
record Monoid {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ binary-operator ⦄    : BinaryOperator(_▫_)
    ⦃ associativity ⦄      : Associativity(_▫_)
    ⦃ identity-existence ⦄ : ∃(Identity(_▫_))

  id = [∃]-witness identity-existence

  identity : Identity (_▫_) id
  identity = [∃]-proof identity-existence

  identityₗ : Identityₗ (_▫_) id
  identityₗ = Identity.left(identity)

  identityᵣ : Identityᵣ (_▫_) id
  identityᵣ = Identity.right(identity)

  identity-existenceₗ : ∃(Identityₗ(_▫_))
  identity-existenceₗ = [∃]-intro id ⦃ identityₗ ⦄

  identity-existenceᵣ : ∃(Identityᵣ(_▫_))
  identity-existenceᵣ = [∃]-intro id ⦃ identityᵣ ⦄

record MonoidObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _▫_ : T → T → T
    ⦃ monoid ⦄ : Monoid(_▫_)
  open Monoid(monoid) public
