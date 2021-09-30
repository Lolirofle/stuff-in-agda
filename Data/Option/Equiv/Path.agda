{-# OPTIONS --cubical #-}

module Data.Option.Equiv.Path where

import      Lvl
open import Data
open import Data.Boolean.Equiv.Path
open import Data.Option
open import Data.Option.Functions
open import Data.Option.Equiv
open import Functional
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Properties
open import Type.Cubical.Path.Equality
open import Type.Cubical.Path.Properties
open import Type
open import Type.Identity using (Id ; intro)
open import Type.Identity.Proofs

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

instance
  Some-injectivity : Injective {B = Option(T)} (Some)
  Injective.proof Some-injectivity {x}{y} = congruence₂ₗ(_or_)(x)

instance
  Path-Option-extensionality : Extensionality{A = T} (Path-equiv)
  Extensionality.cases-inequality (Path-Option-extensionality {T = T}) {x} p with () ← substitute₁(elim{A = T}{B = λ _ → Type}(Option(T)) (const Empty)) p (Some x)

instance
  Option-identityPath : ⦃ IdentityPathType(T) ⦄ → IdentityPathType(Option(T))
  _⊆₂_.proof Option-identityPath {None}   {None}     = const intro
  _⊆₂_.proof Option-identityPath {None}   {Some x} p with () ← Bool-different-values(congruence₁(isSome) p)
  _⊆₂_.proof Option-identityPath {Some x} {None}   p with () ← Bool-different-values(congruence₁(isNone) p)
  _⊆₂_.proof Option-identityPath {Some x} {Some y}   = congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (Some) ⦃ Id-to-function ⦃ Id-equiv ⦄ ⦄ ∘ sub₂(_≡_)(Id) ∘ injective(Some)
