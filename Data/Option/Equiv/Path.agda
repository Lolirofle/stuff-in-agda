{-# OPTIONS --cubical #-}

module Data.Option.Equiv.Path where

import      Lvl
open import Data
open import Data.Option
open import Data.Option.Functions
open import Data.Option.Equiv
open import Functional
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Relator
open import Type.Cubical.Path.Equality
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

instance
  Some-injectivity : Injective {B = Option(T)} (Some)
  Injective.proof Some-injectivity {x}{y} = congruence₂ₗ(_or_)(x)

instance
  Path-Option-extensionality : Extensionality{A = T} (Path-equiv)
  Extensionality.cases-inequality (Path-Option-extensionality {T = T}) {x} p with () ← substitute₁(elim{A = T}{B = λ _ → Type}(Option(T)) (const Empty)) p (Some x)
