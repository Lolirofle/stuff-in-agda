open import Structure.Setoid
open import Type

module Structure.Operator.Group {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_▫_ : T → T → T) where

import      Lvl
open import Logic
open import Logic.IntroInstances
open import Logic.Predicate
open import Structure.Function
open import Structure.Operator
import      Structure.Operator.InverseOperatorFromFunction as InverseOperatorFromFunction
open import Structure.Operator.Monoid using (Monoid ; intro)
open import Structure.Operator.Properties hiding (associativity ; commutativity)
open import Type.Size

-- A type and a binary operator using this type is a group when:
-- • It is a monoid.
-- • The operator have an inverse in both directions.
record Group : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ binaryOperator ⦄    : BinaryOperator(_▫_)
    ⦃ associativity ⦄      : Associativity(_▫_)
    ⦃ identity-existence ⦄ : ∃(Identity(_▫_))

  instance
    monoid : Monoid(_▫_)
    monoid = intro ⦃ identity-existence = identity-existence ⦄
  open Monoid(monoid)
    hiding(
      binaryOperator ;
      associativity ;
      identity-existence
    ) public

  field
    ⦃ inverse-existence ⦄ : ∃(InverseFunction(_▫_) ⦃ identity-existence ⦄)

  inv = [∃]-witness inverse-existence

  field
    ⦃ inv-function ⦄ : Function(inv)

  instance
    inverse : InverseFunction(_▫_) inv
    inverse = [∃]-proof inverse-existence

  instance
    inverseₗ : InverseFunctionₗ(_▫_) inv
    inverseₗ = InverseFunction.left(inverse)

  instance
    inverseᵣ : InverseFunctionᵣ(_▫_) inv
    inverseᵣ = InverseFunction.right(inverse)

  inv-op : T → T → T
  inv-op = InverseOperatorFromFunction.invOpᵣ(_▫_)(inv)

Group-from-monoid : ⦃ monoid@(intro ⦃ identity-existence = identity-existence ⦄) : Monoid(_▫_) ⦄ → (inv : T → T) → ⦃ func : Function(inv) ⦄ → ⦃ inver : InverseFunction(_▫_) ⦃ identity-existence ⦄ inv ⦄ → Group
Group-from-monoid ⦃ intro ⦄ inv = intro

record CommutativeGroup : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ group ⦄         : Group
    ⦃ commutativity ⦄ : Commutativity(_▫_)
  open Group(group) public

{- TODO: See Monoid for how this should be rewritten to fit how it is done in Category
module Morphism where
  module _ {ℓ₁ ℓ₂} {X : Type{ℓ₁}} ⦃ _ : Equiv(X) ⦄ {_▫X_ : X → X → X} ⦃ structureₗ : Group(_▫X_) ⦄ {Y : Type{ℓ₂}} ⦃ _ : Equiv(Y) ⦄ {_▫Y_ : Y → Y → Y} ⦃ structureᵣ : Group(_▫Y_) ⦄ (f : X → Y) where
    -- Group homomorphism
    record Homomorphism : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro

      idₗ = Group.id(structureₗ)
      idᵣ = Group.id(structureᵣ)

      invₗ = Group.inv(structureₗ)
      invᵣ = Group.inv(structureᵣ)

      field
        preserve-op  : ∀{x y : X} → (f(x ▫X y) ≡ f(x) ▫Y f(y))
        -- TODO: These may be unneccessary because they follow from preserve-op when Function(f)
        preserve-inv : ∀{x : X} → (f(invₗ x) ≡ invᵣ(f(x)))
        preserve-id  : (f(idₗ) ≡ idᵣ)

    -- Group monomorphism (Injective homomorphism)
    record Monomorphism : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field
        ⦃ homomorphism ⦄ : Homomorphism
        ⦃ size ⦄         : (X ≼ Y)

    -- Group epimorphism (Surjective homomorphism)
    record Epimorphism : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field
        ⦃ homomorphism ⦄ : Homomorphism
        ⦃ size ⦄         : (X ≽ Y)

    -- Group isomorphism (Bijective homomorphism)
    record Isomorphism : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
      constructor intro
      field
        ⦃ homomorphism ⦄ : Homomorphism
        ⦃ size ⦄         : (X ≍ Y)

  _↣_ : ∀{ℓ₁ ℓ₂} → {X : Type{ℓ₁}} → ⦃ _ : Equiv(X) ⦄ → (_▫X_ : X → X → X) → ⦃ structureₗ : Group(_▫X_) ⦄ → {Y : Type{ℓ₂}} → ⦃ _ : Equiv(Y) ⦄ → (_▫Y_ : Y → Y → Y) → ⦃ structureᵣ : Group(_▫Y_) ⦄ → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  (_▫X_) ↣ (_▫Y_) = ∃(Monomorphism{_▫X_ = _▫X_}{_▫Y_ = _▫Y_})

  _↠_ : ∀{ℓ₁ ℓ₂} → {X : Type{ℓ₁}} → ⦃ _ : Equiv(X) ⦄ → (_▫X_ : X → X → X) → ⦃ structureₗ : Group(_▫X_) ⦄ → {Y : Type{ℓ₂}} → ⦃ _ : Equiv(Y) ⦄ → (_▫Y_ : Y → Y → Y) → ⦃ structureᵣ : Group(_▫Y_) ⦄ → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  (_▫X_) ↠ (_▫Y_) = ∃(Epimorphism{_▫X_ = _▫X_}{_▫Y_ = _▫Y_})

  _⤖_ : ∀{ℓ₁ ℓ₂} → {X : Type{ℓ₁}} → ⦃ _ : Equiv(X) ⦄ → (_▫X_ : X → X → X) → ⦃ structureₗ : Group(_▫X_) ⦄ → {Y : Type{ℓ₂}} → ⦃ _ : Equiv(Y) ⦄ → (_▫Y_ : Y → Y → Y) → ⦃ structureᵣ : Group(_▫Y_) ⦄ → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  (_▫X_) ⤖ (_▫Y_) = ∃(Isomorphism{_▫X_ = _▫X_}{_▫Y_ = _▫Y_})
-}
