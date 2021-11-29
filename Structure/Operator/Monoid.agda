module Structure.Operator.Monoid {ℓ}{ℓₑ} where

import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Structure.Setoid
open import Structure.Operator
open import Structure.Operator.Properties hiding (associativity ; identityₗ ; identityᵣ)
open import Structure.Operator.Semi
open import Type

-- A type and a binary operator using this type is a monoid when:
-- • The operator is associative.
-- • The operator have an identity in both directions.
record Monoid  {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ binaryOperator ⦄    : BinaryOperator(_▫_)
    ⦃ associativity ⦄      : Associativity(_▫_)
    ⦃ identity-existence ⦄ : ∃(Identity(_▫_))

  instance
    semi : Semi(_▫_)
    semi = intro

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

record MonoidObject : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _▫_ : T → T → T
    ⦃ monoid ⦄ : Monoid(_▫_)
  open Monoid(monoid) public

module _ {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ {_▫_ : T → T → T} where
  record NonIdentityRelation (monoid : Monoid(_▫_)) {ℓₙᵢ} : Stmt{ℓ Lvl.⊔ ℓₑ Lvl.⊔ Lvl.𝐒(ℓₙᵢ)} where
    constructor intro
    open Monoid(monoid)
    field
      NonIdentity : T → Stmt{ℓₙᵢ}
      proof : ∀{x} → NonIdentity(x) ↔ (x ≢ id)

  defaultNonIdentityRelation : ∀{monoid : Monoid(_▫_)} → NonIdentityRelation(monoid)
  NonIdentityRelation.NonIdentity (defaultNonIdentityRelation {monoid}) = _≢ id where open Monoid(monoid)
  NonIdentityRelation.proof defaultNonIdentityRelation = [↔]-reflexivity
