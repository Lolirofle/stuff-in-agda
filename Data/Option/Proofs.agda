module Data.Option.Proofs where

import      Lvl
open import Data
open import Data.Option
open import Data.Either
open import Data.Either.Proofs
open import Functional
open import Relator.Equals
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Type

module _ {ℓ} {T : Type{ℓ}} where
  Some-injectivity : Injective {B = Option(T)} (Some)
  Some-injectivity = Right-injectivity

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : Type{ℓ₃}} {f : B → C}{g : A → B} where
  map-preserves-[∘] : ∀{o} → (map(f ∘ g)(o) ≡ ((map f) ∘ (map g))(o))
  map-preserves-[∘] {None}   = [≡]-intro
  map-preserves-[∘] {Some x} = [≡]-intro

module _ {ℓ} {T : Type{ℓ}} where
  map-preserves-id : ∀{o : Option(T)} → (map id(o) ≡ o)
  map-preserves-id {None}   = [≡]-intro
  map-preserves-id {Some x} = [≡]-intro
