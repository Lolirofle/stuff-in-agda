module Data.Either.Proofs where

import      Lvl
open import Data
open import Data.Either as Either
open import Functional
open import Logic.Predicate
open import Structure.Function.Domain hiding (Function)
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable A B C : Type{ℓ}

module _ where
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equivalence

  instance
    Left-injectivity : Injective(Left {A = A}{B = B})
    Injective.proof Left-injectivity [≡]-intro = [≡]-intro

  instance
    Right-injectivity : Injective(Right {A = A}{B = B})
    Injective.proof Right-injectivity [≡]-intro = [≡]-intro

  mapLeft-preserves-id : ∀{e : (A ‖ B)} → (mapLeft id(e) ≡ e)
  mapLeft-preserves-id {e = Left  x} = [≡]-intro
  mapLeft-preserves-id {e = Right x} = [≡]-intro

  mapRight-preserves-id : ∀{e : (A ‖ B)} → (mapRight id(e) ≡ e)
  mapRight-preserves-id {e = Left  x} = [≡]-intro
  mapRight-preserves-id {e = Right x} = [≡]-intro

  swap-involution : ∀{x} → (Either.swap ∘ Either.swap {A = A}{B = B})(x) ≡ x
  swap-involution {x = Left  _} = [≡]-intro
  swap-involution {x = Right _} = [≡]-intro
  {-# REWRITE swap-involution #-}

  module _ {f : B → C}{g : A → B} where
    mapLeft-preserves-[∘] : ∀{e : A ‖ B} → (mapLeft(f ∘ g)(e) ≡ ((mapLeft f) ∘ (mapLeft g))(e))
    mapLeft-preserves-[∘] {Left  x} = [≡]-intro
    mapLeft-preserves-[∘] {Right x} = [≡]-intro

  module _ {f : B → A}{g : C → B} where
    mapRight-preserves-[∘] : ∀{e : B ‖ C} → (mapRight(f ∘ g)(e) ≡ ((mapRight f) ∘ (mapRight g))(e))
    mapRight-preserves-[∘] {Left  x} = [≡]-intro
    mapRight-preserves-[∘] {Right x} = [≡]-intro
