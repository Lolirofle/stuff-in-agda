module Structure.Operator.Ring where

import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Setoid.WithLvl
open import Structure.Operator.Group using (Group ; CommutativeGroup)
open import Structure.Operator.Monoid using (Monoid)
open import Structure.Operator.Properties hiding (distributivityₗ ; distributivityᵣ)
open import Type

record Ring {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  field
    instance ⦃ [+]-commutative-group ⦄  : CommutativeGroup (_+_)
    instance ⦃ [⋅]-monoid ⦄             : Monoid (_⋅_)
    instance ⦃ [⋅][+]-distributivityₗ ⦄ : Distributivityₗ (_⋅_) (_+_)
    instance ⦃ [⋅][+]-distributivityᵣ ⦄ : Distributivityᵣ (_⋅_) (_+_)

  open CommutativeGroup([+]-commutative-group)
    using ()
    renaming(
      group              to [+]-group ;
      commutativity      to [+]-commutativity ;
      monoid             to [+]-monoid ;
      binary-operator    to [+]-binary-operator ;
      associativity      to [+]-associativity ;
      identity-existence to [+]-identity-existence ;
      id                 to 𝟎 ;
      identity           to [+]-identity ;
      identityₗ          to [+]-identityₗ ;
      identityᵣ          to [+]-identityᵣ ;
      inverse-existence  to [+]-inverse-existence ;
      inv                to −_ ;
      inv-function        to [−]-function ;
      inverse            to [+]-inverse ;
      inverseₗ           to [+]-inverseₗ ;
      inverseᵣ           to [+]-inverseᵣ
    ) public

  open Monoid([⋅]-monoid)
    using ()
    renaming(
      binary-operator    to [⋅]-binary-operator ;
      associativity      to [⋅]-associativity ;
      identity-existence to [⋅]-identity-existence ;
      id                 to 𝟏 ;
      identity           to [⋅]-identity ;
      identityₗ          to [⋅]-identityₗ ;
      identityᵣ          to [⋅]-identityᵣ
    ) public

  _−_ : T → T → T
  x − y = x + (− y)

record RingObject {ℓ ℓₑ} : Stmt{Lvl.𝐒(ℓ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {T} : Type{ℓ}
    ⦃ equiv ⦄ : Equiv{ℓₑ}(T)
    _+_ : T → T → T
    _⋅_ : T → T → T
    ⦃ ring ⦄ : Ring(_+_)(_⋅_)
  open Ring(ring) public

record Homomorphism
  {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}
  {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_+X_ _⋅X_ : X → X → X} (structureₗ : Ring(_+X_)(_⋅X_))
  {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_+Y_ _⋅Y_ : Y → Y → Y} (structureᵣ : Ring(_+Y_)(_⋅Y_))
  (f : X → Y)
  : Stmt{ℓ₁ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₑ₂} where

  constructor intro

  𝟏ₗ = Ring.𝟏(structureₗ)
  𝟏ᵣ = Ring.𝟏(structureᵣ)

  field
    ⦃ function ⦄     : Function(f)
    ⦃ preserve-[+] ⦄ : Preserving₂(f)(_+X_)(_+Y_)
    ⦃ preserve-[⋅] ⦄ : Preserving₂(f)(_⋅X_)(_⋅Y_)
    ⦃ preserve-𝟏 ⦄   : Preserving₀(f)(𝟏ₗ)(𝟏ᵣ)

record Antihomomorphism
  {ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂}
  {X : Type{ℓ₁}} ⦃ _ : Equiv{ℓₑ₁}(X) ⦄ {_+X_ _⋅X_ : X → X → X} (structureₗ : Ring(_+X_)(_⋅X_))
  {Y : Type{ℓ₂}} ⦃ _ : Equiv{ℓₑ₂}(Y) ⦄ {_+Y_ _⋅Y_ : Y → Y → Y} (structureᵣ : Ring(_+Y_)(_⋅Y_))
  (f : X → Y)
  : Stmt{ℓ₁ Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓₑ₂} where

  constructor intro

  𝟏ₗ = Ring.𝟏(structureₗ)
  𝟏ᵣ = Ring.𝟏(structureᵣ)

  field
    ⦃ function ⦄         : Function(f)
    ⦃ preserve-[+] ⦄     : Preserving₂(f)(_+X_)(_+Y_)
    ⦃ antipreserve-[⋅] ⦄ : ∀{x y} → (f(x ⋅X y) ≡ f(y) ⋅Y f(x))
    ⦃ preserve-𝟏 ⦄       : Preserving₀(f)(𝟏ₗ)(𝟏ᵣ)

_→ʳⁱⁿᵍ_ : ∀{ℓₗ ℓₗₑ ℓᵣ ℓᵣₑ} → RingObject{ℓₗ}{ℓₗₑ} → RingObject{ℓᵣ}{ℓᵣₑ} → Type
A →ʳⁱⁿᵍ B = ∃(Homomorphism(RingObject.ring A)(RingObject.ring B))



private
  module Impl {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (𝟎 : T) where
    record NonZero (x : T) : Stmt{ℓₑ} where
      constructor intro
      field proof : (x ≢ 𝟎)

record DivisionRing {ℓ ℓₑ} {T : Type{ℓ}} ⦃ _ : Equiv{ℓₑ}(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ Lvl.⊔ ℓₑ} where
  field
    ⦃ ring ⦄ : Ring(_+_)(_⋅_)

  open Ring(ring) public
  open Impl(𝟎) public

  field
    ⅟ : (x : T) → ⦃ NonZero(x) ⦄ → T
    [⋅]-inverseₗ : ∀{x} → ⦃ non-zero : NonZero(x) ⦄ → (x ⋅ (⅟ x) ≡ 𝟏)
    [⋅]-inverseᵣ : ∀{x} → ⦃ non-zero : NonZero(x) ⦄ → ((⅟ x) ⋅ x ≡ 𝟏)

  _/_ : T → (y : T) → ⦃ NonZero(y) ⦄ → T
  x / y = x ⋅ (⅟ y)
