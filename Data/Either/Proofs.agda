module Data.Either.Proofs where

import      Lvl
open import Data.Either as Either
open import Functional
open import Relator.Equals
open import Relator.Equals.Proofs.Equivalence
open import Structure.Function.Domain
open import Type

module _ {ℓ₁}{ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} where
  Left-injectivity : ∀{x y : T₁} → (Left {T₁ = T₁} {T₂ = T₂} (x) ≡ Left(y)) → (x ≡ y)
  Left-injectivity [≡]-intro = [≡]-intro

  Right-injectivity : ∀{x y : T₂} → (Right {T₁ = T₁} {T₂ = T₂} (x) ≡ Right(y)) → (x ≡ y)
  Right-injectivity [≡]-intro = [≡]-intro

  mapLeft-preserves-id : ∀{e : (T₁ ‖ T₂)} → (mapLeft id(e) ≡ e)
  mapLeft-preserves-id {Left  x} = [≡]-intro
  mapLeft-preserves-id {Right x} = [≡]-intro

  mapRight-preserves-id : ∀{e : (T₁ ‖ T₂)} → (mapRight id(e) ≡ e)
  mapRight-preserves-id {Left  x} = [≡]-intro
  mapRight-preserves-id {Right x} = [≡]-intro

  swap-involution : ∀{x} → (Either.swap ∘ Either.swap {T₁ = T₁}{T₂ = T₂})(x) ≡ x
  swap-involution {Left  x} = [≡]-intro
  swap-involution {Right x} = [≡]-intro

module _ {ℓ₁}{ℓ₂}{ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : Type{ℓ₃}} {f : B → C}{g : A → B} where
  mapLeft-preserves-[∘] : ∀{e : A ‖ B} → (mapLeft(f ∘ g)(e) ≡ ((mapLeft f) ∘ (mapLeft g))(e))
  mapLeft-preserves-[∘] {Left  x} = [≡]-intro
  mapLeft-preserves-[∘] {Right x} = [≡]-intro

module _ {ℓ₁}{ℓ₂}{ℓ₃} {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : Type{ℓ₃}} {f : B → A}{g : C → B} where
  mapRight-preserves-[∘] : ∀{e : B ‖ C} → (mapRight(f ∘ g)(e) ≡ ((mapRight f) ∘ (mapRight g))(e))
  mapRight-preserves-[∘] {Left  x} = [≡]-intro
  mapRight-preserves-[∘] {Right x} = [≡]-intro

