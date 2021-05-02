module Structure.Operator.Ring where

import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Operator
open import Structure.Operator.Semi using (Semi)
open import Structure.Operator.Group using (Group ; CommutativeGroup ; intro)
open import Structure.Operator.Monoid using (Monoid ; intro)
open import Structure.Operator.Properties hiding (distributivityₗ ; distributivityᵣ ; commutativity)
open import Syntax.Function
open import Type

-- TODO: Not sure about the way the definitions handle the hiearchies

private
  module Impl {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (𝟎 : T) where
    record NonZero (x : T) : Stmt{ℓₑ} where
      constructor intro
      field proof : (x ≢ 𝟎)

record PreRg {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ [+]-commutativity ⦄      : Commutativity(_+_)
    ⦃ [⋅][+]-distributivityₗ ⦄ : Distributivityₗ(_⋅_)(_+_)
    ⦃ [⋅][+]-distributivityᵣ ⦄ : Distributivityᵣ(_⋅_)(_+_)

-- An algebraic structure over two operators, in which the first one is a commutative semigroup and the second one is a semigroup which distributes over the first one.
-- Also called: Semiring, hemiring, pre-semiring.
-- Note: It is called "semi-rg" because it is like a rg but the addition is a semigroup.
record SemiRg {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ [+]-semi ⦄ : Semi(_+_)
    ⦃ [⋅]-semi ⦄ : Semi(_⋅_)
    ⦃ preRg ⦄    : PreRg(_+_)(_⋅_)
  open Semi([+]-semi)
    using()
    renaming(
      binary-operator     to [+]-binary-operator ;
      associativity       to [+]-associativity
    ) public
  open Semi([⋅]-semi)
    using()
    renaming(
      binary-operator     to [⋅]-binary-operator ;
      associativity       to [⋅]-associativity
    ) public
  open PreRg(preRg) public

record Rg {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ [+]-monoid ⦄ : Monoid(_+_)
    ⦃ [⋅]-semi ⦄   : Semi(_⋅_)
    ⦃ preRg ⦄      : PreRg(_+_)(_⋅_)
  open Monoid([+]-monoid)
    using()
    renaming(
      semi                to [+]-semi ;
      identity-existence  to [+]-identity-existence ;
      identity-existenceₗ to [+]-identity-existenceₗ ;
      identity-existenceᵣ to [+]-identity-existenceᵣ ;
      id                  to 𝟎 ;
      identity            to [+]-identity ;
      identityₗ           to [+]-identityₗ ;
      identityᵣ           to [+]-identityᵣ
    ) public
  semiRg : SemiRg(_+_)(_⋅_)
  semiRg = intro
  open SemiRg(semiRg)
    hiding(
      [+]-semi ;
      [⋅]-semi ;
      preRg
    )public

  open Impl(𝟎) public

  ZeroDivisorₗ : T → Stmt
  ZeroDivisorₗ(a) = ∃(x ↦ (x ≢ 𝟎) ∧ (a ⋅ x ≡ 𝟎))

  ZeroDivisorᵣ : T → Stmt
  ZeroDivisorᵣ(a) = ∃(x ↦ (x ≢ 𝟎) ∧ (x ⋅ a ≡ 𝟎))

  ZeroDivisor : T → Stmt
  ZeroDivisor(a) = ∃(x ↦ (x ≢ 𝟎) ∧ ((a ⋅ x ≡ 𝟎) ∧ (x ⋅ a ≡ 𝟎)))

-- An algebraic structure over two operators, in which the first one is a commutative group, and the second one is associative and distributes over the first one.
-- Also called: Rg.
record Rng {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ [+]-group ⦄  : Group(_+_)
    ⦃ [⋅]-semi ⦄   : Semi(_⋅_)
    ⦃ preRg ⦄      : PreRg(_+_)(_⋅_)
  instance
    rg : Rg(_+_)(_⋅_)
    rg = let open Group([+]-group) ; open Semi([⋅]-semi) in intro
  open Rg(rg)
    hiding(
      [⋅]-semi ;
      preRg
    ) public
  open Group([+]-group)
    using ()
    renaming(
      inverse-existence   to [+]-inverse-existence ;
      inv                 to −_ ;
      inv-function        to [−]-function ;
      inverse             to [+]-inverse ;
      inverseₗ            to [+]-inverseₗ ;
      inverseᵣ            to [+]-inverseᵣ
    ) public

  instance
    [+]-commutativeGroup : CommutativeGroup(_+_)
    [+]-commutativeGroup = intro

  _−_ : T → T → T
  x − y = x + (− y)

record RngObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ rng ⦄ : Rng(_+_)(_⋅_)
  open Rng(rng) public

record Unity {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) ⦃ rg : Rg(_+_)(_⋅_) ⦄ : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  open Rg(rg)
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

-- An algebraic structure over two operators, in which the first one is a commutative monoid and the second one is a monoid which distributes over the first one.
-- Also called: Semiring.
-- Note: It is called "rig" because it is a ring without the "n" (the negative element, inverse of addition).
record Rig {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ [+]-monoid ⦄ : Monoid(_+_)
    ⦃ [⋅]-monoid ⦄ : Monoid(_⋅_)
    ⦃ preRg ⦄      : PreRg(_+_)(_⋅_)
  instance
    rg : Rg(_+_)(_⋅_)
    rg = let open Monoid([+]-monoid) ; open Monoid([⋅]-monoid) in intro
  open Rg(rg)
    hiding(
      [+]-monoid ;
      preRg
    ) public
  instance
    unity : Unity(_+_)(_⋅_)
    unity = intro
  open Unity(unity)
    hiding(
      [⋅]-monoid
    ) public

  field
    ⦃ [⋅]-absorberₗ ⦄ : Absorberₗ(_⋅_)(𝟎)
    ⦃ [⋅]-absorberᵣ ⦄ : Absorberᵣ(_⋅_)(𝟎)

-- Rng with unity.
record Ring {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  field
    ⦃ [+]-group ⦄  : Group(_+_)
    ⦃ [⋅]-monoid ⦄ : Monoid(_⋅_)
    ⦃ preRg ⦄      : PreRg(_+_)(_⋅_)
  instance
    rng : Rng(_+_)(_⋅_)
    rng = let open Monoid([⋅]-monoid) in intro
  open Rng(rng)
    hiding(
      [+]-group ;
      preRg
    ) public
  instance
    unity : Unity(_+_)(_⋅_)
    unity = intro
  open Unity(unity)
    hiding(
      [⋅]-monoid
    ) public

record RingObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ ring ⦄ : Ring(_+_)(_⋅_)
  open Ring(ring) public

record Division {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) ⦃ rg : Rg(_+_)(_⋅_) ⦄ ⦃ unity : Unity(_+_)(_⋅_) ⦄ : Stmt{ℓ Lvl.⊔ ℓₑ} where
  constructor intro
  open Rg(rg)
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
  field ⦃ ring ⦄ : Ring(_+_)(_⋅_)
  open Ring(ring) public
  field ⦃ division ⦄ : Division(_+_)(_⋅_)
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
