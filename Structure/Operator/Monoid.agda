module Structure.Operator.Monoid where

import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Operator.Properties hiding (associativity ; identityₗ ; identityᵣ)
open import Structure.Operator
open import Type
open import Type.Size

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

record MonoidObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _▫_ : T → T → T
    ⦃ monoid ⦄ : Monoid(_▫_)
  open Monoid(monoid) public

record Homomorphism
  {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}
  {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_▫X_ : X → X → X} ( structureₗ : Monoid(_▫X_))
  {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_▫Y_ : Y → Y → Y} ( structureᵣ : Monoid(_▫Y_))
  (f : X → Y)
  : Stmt{ℓ₁ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₑ₂} where

  constructor intro

  idₗ = Monoid.id(structureₗ)
  idᵣ = Monoid.id(structureᵣ)

  field
    ⦃ function ⦄ : Function(f)
    ⦃ preserve-op ⦄ : Preserving₂(f)(_▫X_)(_▫Y_)
    ⦃ preserve-id ⦄ : Preserving₀(f)(idₗ)(idᵣ)

_→ᵐᵒⁿᵒⁱᵈ_ : ∀{ℓₗ ℓₗₑ ℓᵣ ℓᵣₑ} → MonoidObject{ℓₗ}{ℓₗₑ} → MonoidObject{ℓᵣ}{ℓᵣₑ} → Type
A →ᵐᵒⁿᵒⁱᵈ B = ∃(Homomorphism(MonoidObject.monoid A)(MonoidObject.monoid B))

-- TODO: Notation for morphisms
-- Monomorphism _↣_ inj
-- Epimorphism _↠_ surj
-- Isomorphism _⤖_ bij
