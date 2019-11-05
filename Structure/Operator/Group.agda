module Structure.Operator.Group where

import      Lvl
open import Logic
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Operator.Monoid using (Monoid)
open import Structure.Operator.Properties hiding (commutativity)
open import Type
open import Type.Size

-- A type and a binary operator using this type is a group when:
-- • It is a monoid.
-- • The operator have an inverse in both directions.
record Group {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) : Stmt{ℓ} where
  constructor intro

  field
    instance ⦃ monoid ⦄ : Monoid(_▫_)
  open Monoid(monoid) public

  field
    ⦃ inverse-existence ⦄ : ∃(InverseFunction(_▫_) ⦃ identity-existence ⦄)

  inv = [∃]-witness inverse-existence

  field
    ⦃ inv-function ⦄ : Function(inv)

  instance
    inverse : InverseFunction (_▫_) inv
    inverse = [∃]-proof inverse-existence

  instance
    inverseₗ : InverseFunctionₗ (_▫_) inv
    inverseₗ = InverseFunction.left(inverse)

  instance
    inverseᵣ : InverseFunctionᵣ (_▫_) inv
    inverseᵣ = InverseFunction.right(inverse)

record CommutativeGroup {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_▫_ : T → T → T) : Stmt{ℓ} where
  constructor intro
  field
    instance ⦃ group ⦄         : Group (_▫_)
    instance ⦃ commutativity ⦄ : Commutativity (_▫_)
  open Group(group) public

module Morphism where
  -- Group homomorphism
  record Homomorphism {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} (f : X → Y) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      instance ⦃ structureₗ ⦄ : Group(_▫X_)
      instance ⦃ structureᵣ ⦄ : Group(_▫Y_)

    idₗ = Group.id(structureₗ)
    idᵣ = Group.id(structureᵣ)

    invₗ = Group.inv(structureₗ)
    invᵣ = Group.inv(structureᵣ)

    field
      preserve-op  : ∀{x y : X} → (f(x ▫X y) ≡ f(x) ▫Y f(y))
      preserve-inv : ∀{x : X} → (f(invₗ x) ≡ invᵣ(f(x)))
      preserve-id  : (f(idₗ) ≡ idᵣ)

  -- Group monomorphism (Injective homomorphism)
  record _↣_ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} (f : X → Y) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ homomorphism ⦄ : Homomorphism {_▫X_ = _▫X_} {_▫Y_ = _▫Y_} (f)
      ⦃ size ⦄         : (X ≼ Y)


  -- Group epimorphism (Surjective homomorphism)
  record _↠_ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} (f : X → Y) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ homomorphism ⦄ : Homomorphism {_▫X_ = _▫X_} {_▫Y_ = _▫Y_} (f)
      ⦃ size ⦄         : (X ≽ Y)

  -- Group isomorphism (Bijective homomorphism)
  record _⤖_ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} (f : X → Y) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field
      ⦃ homomorphism ⦄ : Homomorphism {_▫X_ = _▫X_} {_▫Y_ = _▫Y_} (f)
      ⦃ size ⦄         : (X ≍ Y)
