module Structure.Operator.Field where

import      Lvl
open import Logic
open import Logic.Propositional
open import Sets.Setoid
open import Structure.Operator.Group using (Group ; CommutativeGroup)
open import Structure.Operator.Monoid using (Monoid)
open import Structure.Operator.Properties hiding (distributivityₗ ; distributivityᵣ)
open import Type


private
  module Impl {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (𝟎 : T) where
    record NonZero (x : T) : Stmt{ℓ} where
      constructor intro
      field proof : (x ≢ 𝟎)

record Field {ℓ} {T : Type{ℓ}} ⦃ _ : Equiv(T) ⦄ (_+_  : T → T → T) (_⋅_  : T → T → T) : Stmt{ℓ} where
  field
    instance ⦃ [+]-commutative-group ⦄  : CommutativeGroup (_+_)
    instance ⦃ [⋅]-monoid ⦄             : Monoid (_⋅_)
    instance ⦃ [⋅][+]-distributivityₗ ⦄ : Distributivityₗ (_⋅_) (_+_)
    instance ⦃ [⋅][+]-distributivityᵣ ⦄ : Distributivityᵣ (_⋅_) (_+_)
    instance ⦃ [⋅]-commutativity ⦄      : Commutativity(_⋅_) -- TODO: Consider removing this to get a more general structure: The division ring
    -- distinct-identities : 𝟎 ≢ 𝟏 -- TODO: Consider adding this somewhere or at least aknowledge it because this is unprovable, and models where this is true are always a "trivial/singleton ring"

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

  open Impl(𝟎) public

  field
    ⅟ : (x : T) → ⦃ NonZero(x) ⦄ → T
    [⋅]-inverseₗ : ∀{x} → ⦃ non-zero : NonZero(x) ⦄ → (x ⋅ (⅟ x) ≡ 𝟏)
    [⋅]-inverseᵣ : ∀{x} → ⦃ non-zero : NonZero(x) ⦄ → ((⅟ x) ⋅ x ≡ 𝟏)

  _−_ : T → T → T
  x − y = x + (− y)

  _/_ : T → (y : T) → ⦃ NonZero(y) ⦄ → T
  x / y = x ⋅ (⅟ y)
