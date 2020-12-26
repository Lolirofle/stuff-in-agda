module Structure.Operator.Ring where

import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Operator
open import Structure.Operator.Group using (Group ; CommutativeGroup)
open import Structure.Operator.Monoid using (Monoid)
open import Structure.Operator.Properties hiding (distributivityₗ ; distributivityᵣ ; commutativity)
open import Syntax.Function
open import Type

-- TODO: Rg, Rng, Rig

private
  module Impl {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (𝟎 : T) where
    record NonZero (x : T) : Stmt{ℓₑ} where
      constructor intro
      field proof : (x ≢ 𝟎)

-- An algebraic structure over two operators, in which the first one is a commutative group, and the second one is associative and distributes over the first one.
-- Also called: Rg.
record Rng {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ [+]-commutative-group ⦄  : CommutativeGroup (_+_)
    ⦃ [⋅]-binary-operator ⦄    : BinaryOperator(_⋅_)
    ⦃ [⋅]-associativity ⦄      : Associativity(_⋅_)
    ⦃ [⋅][+]-distributivityₗ ⦄ : Distributivityₗ(_⋅_)(_+_)
    ⦃ [⋅][+]-distributivityᵣ ⦄ : Distributivityᵣ(_⋅_)(_+_)

  open CommutativeGroup([+]-commutative-group)
    using ()
    renaming(
      group               to [+]-group ;
      commutativity       to [+]-commutativity ;
      monoid              to [+]-monoid ;
      binary-operator     to [+]-binary-operator ;
      associativity       to [+]-associativity ;
      identity-existence  to [+]-identity-existence ;
      identity-existenceₗ to [+]-identity-existenceₗ ;
      identity-existenceᵣ to [+]-identity-existenceᵣ ;
      id                  to 𝟎 ;
      identity            to [+]-identity ;
      identityₗ           to [+]-identityₗ ;
      identityᵣ           to [+]-identityᵣ ;
      inverse-existence   to [+]-inverse-existence ;
      inv                 to −_ ;
      inv-function        to [−]-function ;
      inverse             to [+]-inverse ;
      inverseₗ            to [+]-inverseₗ ;
      inverseᵣ            to [+]-inverseᵣ
    ) public
  open Impl(𝟎) public

  _−_ : T → T → T
  x − y = x + (− y)

  ZeroDivisorₗ : T → Stmt
  ZeroDivisorₗ(a) = ∃(x ↦ (x ≢ 𝟎) ∧ (a ⋅ x ≡ 𝟎))

  ZeroDivisorᵣ : T → Stmt
  ZeroDivisorᵣ(a) = ∃(x ↦ (x ≢ 𝟎) ∧ (x ⋅ a ≡ 𝟎))

  ZeroDivisor : T → Stmt
  ZeroDivisor(a) = ∃(x ↦ (x ≢ 𝟎) ∧ ((a ⋅ x ≡ 𝟎) ∧ (x ⋅ a ≡ 𝟎)))

record RngObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ rng ⦄ : Rng(_+_)(_⋅_)
  open Rng(rng) public



record Unity {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) ⦃ rng : Rng(_+_)(_⋅_) ⦄ : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  open Rng(rng)
  field
    ⦃ [⋅]-identity-existence ⦄ : ∃(Identity(_⋅_))

  [⋅]-monoid : Monoid(_⋅_)
  [⋅]-monoid = record{}

  open Monoid([⋅]-monoid)
    using ()
    renaming(
      id                 to 𝟏 ;
      identity           to [⋅]-identity ;
      identityₗ          to [⋅]-identityₗ ;
      identityᵣ          to [⋅]-identityᵣ
    ) public

  DistinctIdentities = NonZero(𝟏)

-- Rng with unity.
-- Also called: Rig.
record Ring {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ rng ⦄   : Rng(_+_)(_⋅_)
    ⦃ unity ⦄ : Unity(_+_)(_⋅_)
  open Rng(rng) public
  open Unity(unity) public

record RingObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ ring ⦄ : Ring(_+_)(_⋅_)
  open Ring(ring) public



record Division {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) ⦃ rng : Rng(_+_)(_⋅_) ⦄ ⦃ unity : Unity(_+_)(_⋅_) ⦄ : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  open Rng(rng)
  open Unity(unity)
  field
    ⅟ : (x : T) → ⦃ NonZero(x) ⦄ → T
    [⋅]-inverseₗ : ∀{x} → ⦃ non-zero : NonZero(x) ⦄ → (x ⋅ (⅟ x) ≡ 𝟏)
    [⋅]-inverseᵣ : ∀{x} → ⦃ non-zero : NonZero(x) ⦄ → ((⅟ x) ⋅ x ≡ 𝟏)

  _/_ : T → (y : T) → ⦃ NonZero(y) ⦄ → T
  x / y = x ⋅ (⅟ y)

-- Ring with division.
-- Also called: Ring.
record DivisionRing {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ ring ⦄     : Ring(_+_)(_⋅_)
    ⦃ division ⦄ : Division(_+_)(_⋅_)
  open Ring    (ring)     public
  open Division(division) public

record DivisionRingObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ divisionRing ⦄ : DivisionRing(_+_)(_⋅_)
  open DivisionRing(divisionRing) public
