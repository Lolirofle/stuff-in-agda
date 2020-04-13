module Structure.Operator.Monoid where

import      Lvl
open import Logic
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Function
open import Structure.Operator.Properties hiding (associativity ; identityₗ ; identityᵣ)
open import Structure.Operator
open import Type
open import Type.Size

-- A type and a binary operator using this type is a monoid when:
-- • The operator is associative.
-- • The operator have an identity in both directions.
record Monoid {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) : Stmt{ℓ} where
  constructor intro
  field
    instance ⦃ binary-operator ⦄    : BinaryOperator(_▫_)
    instance ⦃ associativity ⦄      : Associativity(_▫_)
    ⦃ identity-existence ⦄          : ∃(Identity(_▫_))

  id = [∃]-witness identity-existence

  identity : Identity (_▫_) id
  identity = [∃]-proof identity-existence

  identityₗ : Identityₗ (_▫_) id
  identityₗ = Identity.left(identity)

  identityᵣ : Identityᵣ (_▫_) id
  identityᵣ = Identity.right(identity)

module Morphism where
  record Homomorphism {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} (f : X → Y) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      instance ⦃ structureₗ ⦄ : Monoid(_▫X_)
      instance ⦃ structureᵣ ⦄ : Monoid(_▫Y_)

    idₗ = Monoid.id(structureₗ)
    idᵣ = Monoid.id(structureᵣ)

    field
      preserve-op : ∀{x y : X} → (f(x ▫X y) ≡ f(x) ▫Y f(y))
      preserve-id : (f(idₗ) ≡ idᵣ)

  -- Monoid monomorphism (Injective homomorphism)
  record _↣_ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} (f : X → Y) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ homomorphism ⦄ : Homomorphism {_▫X_ = _▫X_} {_▫Y_ = _▫Y_} (f)
      ⦃ size ⦄         : (X ≼ Y)


  -- Monoid epimorphism (Surjective homomorphism)
  record _↠_ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} (f : X → Y) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ homomorphism ⦄ : Homomorphism {_▫X_ = _▫X_} {_▫Y_ = _▫Y_} (f)
      ⦃ size ⦄         : (X ≽ Y)

  -- Monoid isomorphism (Bijective homomorphism)
  record _⤖_ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} (f : X → Y) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ homomorphism ⦄ : Homomorphism {_▫X_ = _▫X_} {_▫Y_ = _▫Y_} (f)
      ⦃ size ⦄         : (X ≍ Y)

  -- TODO: When f is a function and a homomorphism and only _▫X_ is a monoid, is it enough to prove that RHS is a monoid?
  -- structureᵣ : ⦃ _ : Function(f) ⦄ → Monoid(_▫Y_)
  -- Identityₗ.proof(Monoid.identityₗ(structureᵣ)) = function(f) (Identityₗ.proof(Monoid.identityₗ(structureₗ)))
