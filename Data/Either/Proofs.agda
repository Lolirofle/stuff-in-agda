module Data.Either.Proofs where

import      Lvl
open import Data
open import Data.Either as Either
open import Function.Equals
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid hiding ([≡]-with)
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Relator.Equals using ([≡]-intro)
open import Relator.Equals.Proofs.Equivalence
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable A B C : Type{ℓ}

module _ ⦃ _ : Equiv(A) ⦄ ⦃ _ : Equiv(B) ⦄ where
  instance
    Left-injectivity : Injective(Left {A = A}{B = B})
    Injective.proof Left-injectivity [≡]-intro = [≡]-intro

  instance
    Right-injectivity : Injective(Right {A = A}{B = B})
    Injective.proof Right-injectivity [≡]-intro = [≡]-intro

  mapLeft-preserves-id : ∀{e : (A ‖ B)} → (mapLeft id(e) ≡ e)
  mapLeft-preserves-id {e = Left  _} = reflexivity(_≡_)
  mapLeft-preserves-id {e = Right _} = reflexivity(_≡_)

  mapRight-preserves-id : ∀{e : (A ‖ B)} → (mapRight id(e) ≡ e)
  mapRight-preserves-id {e = Left  _} = reflexivity(_≡_)
  mapRight-preserves-id {e = Right _} = reflexivity(_≡_)

  swap-involution : ∀{x} → (Either.swap ∘ Either.swap {A = A}{B = B})(x) ≡ x
  swap-involution {x = Left  _} = reflexivity(_≡_)
  swap-involution {x = Right _} = reflexivity(_≡_)

module _ ⦃ _ : Equiv(B) ⦄ ⦃ _ : Equiv(C) ⦄ {f : B → C}{g : A → B} where
  mapLeft-preserves-[∘] : ∀{e : A ‖ B} → (mapLeft(f ∘ g)(e) ≡ ((mapLeft f) ∘ (mapLeft g))(e))
  mapLeft-preserves-[∘] {Left  x} = reflexivity(_≡_)
  mapLeft-preserves-[∘] {Right x} = reflexivity(_≡_)

module _  ⦃ _ : Equiv(A) ⦄ ⦃ _ : Equiv(B) ⦄ {f : B → A}{g : C → B} where
  mapRight-preserves-[∘] : ∀{e : B ‖ C} → (mapRight(f ∘ g)(e) ≡ ((mapRight f) ∘ (mapRight g))(e))
  mapRight-preserves-[∘] {Left  x} = reflexivity(_≡_)
  mapRight-preserves-[∘] {Right x} = reflexivity(_≡_)

module _  ⦃ _ : Equiv(A) ⦄ ⦃ _ : Equiv(B) ⦄ where
  map2-preserves-id : ∀{e : (A ‖ B)} → (map2 id id e ≡ e)
  map2-preserves-id {e = Left  x} = reflexivity(_≡_)
  map2-preserves-id {e = Right x} = reflexivity(_≡_)
