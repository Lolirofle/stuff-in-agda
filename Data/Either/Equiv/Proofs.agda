module Data.Either.Equiv.Proofs where

import      Lvl
open import Data
open import Data.Either as Either
open import Data.Either.Equiv
open import Function.Equals
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable A B C : Type{ℓ}

module _ ⦃ _ : Equiv(A) ⦄ ⦃ _ : Equiv(B) ⦄ where
  instance
    Left-injectivity : Injective(Left {A = A}{B = B})
    Injective.proof Left-injectivity (Left p) = p

  instance
    Right-injectivity : Injective(Right {A = A}{B = B})
    Injective.proof Right-injectivity (Right p) = p

  mapLeft-preserves-id : ∀{e : (A ‖ B)} → (mapLeft id(e) ≡ e)
  mapLeft-preserves-id {e = Left  _} = Left (reflexivity(_≡_))
  mapLeft-preserves-id {e = Right _} = Right(reflexivity(_≡_))

  mapRight-preserves-id : ∀{e : (A ‖ B)} → (mapRight id(e) ≡ e)
  mapRight-preserves-id {e = Left  _} = Left (reflexivity(_≡_))
  mapRight-preserves-id {e = Right _} = Right(reflexivity(_≡_))

  swap-involution : ∀{x} → (Either.swap ∘ Either.swap {A = A}{B = B})(x) ≡ x
  swap-involution {x = Left  _} = Left (reflexivity(_≡_))
  swap-involution {x = Right _} = Right(reflexivity(_≡_))

module _ ⦃ _ : Equiv(B) ⦄ ⦃ _ : Equiv(C) ⦄ {f : B → C}{g : A → B} where
  mapLeft-preserves-[∘] : ∀{e : A ‖ B} → (mapLeft(f ∘ g)(e) ≡ ((mapLeft f) ∘ (mapLeft g))(e))
  mapLeft-preserves-[∘] {Left  x} = Left (reflexivity(_≡_))
  mapLeft-preserves-[∘] {Right x} = Right(reflexivity(_≡_))

module _  ⦃ _ : Equiv(A) ⦄ ⦃ _ : Equiv(B) ⦄ {f : B → A}{g : C → B} where
  mapRight-preserves-[∘] : ∀{e : B ‖ C} → (mapRight(f ∘ g)(e) ≡ ((mapRight f) ∘ (mapRight g))(e))
  mapRight-preserves-[∘] {Left  x} = Left (reflexivity(_≡_))
  mapRight-preserves-[∘] {Right x} = Right(reflexivity(_≡_))

module _  ⦃ _ : Equiv(A) ⦄ ⦃ _ : Equiv(B) ⦄ where
  map2-preserves-id : ∀{e : (A ‖ B)} → (map2 id id e ≡ e)
  map2-preserves-id {e = Left  x} = Left (reflexivity(_≡_))
  map2-preserves-id {e = Right x} = Right(reflexivity(_≡_))

module _  ⦃ _ : Equiv(A) ⦄ ⦃ _ : Equiv(B) ⦄ {f : B → A}{g : C → B} where
  map2-mapLeft-mapRight : (map2 f g ≡ mapLeft f ∘ mapRight g)
  _⊜_.proof (map2-mapLeft-mapRight) {[∨]-introₗ _} = Left (reflexivity(_≡_))
  _⊜_.proof (map2-mapLeft-mapRight) {[∨]-introᵣ _} = Right(reflexivity(_≡_))

module _  ⦃ _ : Equiv(A) ⦄ ⦃ _ : Equiv(B) ⦄ {f₁ f₂ : B → A} {g₁ g₂ : C → B} where
  map2-eq : (f₁ ≡ f₂) → (g₁ ≡ g₂) → (map2 f₁ g₁ ≡ map2 f₂ g₂)
  _⊜_.proof (map2-eq (intro f₁f₂) (intro g₁g₂)) {[∨]-introₗ _} = Left  f₁f₂
  _⊜_.proof (map2-eq (intro f₁f₂) (intro g₁g₂)) {[∨]-introᵣ _} = Right g₁g₂

module _  ⦃ _ : Equiv(C) ⦄ {f₁ f₂ : A → C} {g₁ g₂ : B → C} where
  map1-fn-eq : (f₁ ≡ f₂) → (g₁ ≡ g₂) → (map1 f₁ g₁ ≡ map1 f₂ g₂)
  _⊜_.proof (map1-fn-eq (intro f₁f₂) (intro g₁g₂)) {[∨]-introₗ _} = f₁f₂
  _⊜_.proof (map1-fn-eq (intro f₁f₂) (intro g₁g₂)) {[∨]-introᵣ _} = g₁g₂

module _  ⦃ _ : Equiv(A) ⦄ ⦃ _ : Equiv(B) ⦄ ⦃ _ : Equiv(C) ⦄ {f₁ f₂ : A → C} ⦃ _ : Function(f₁) ⦄ {g₁ g₂ : B → C} ⦃ _ : Function(g₁) ⦄  {x₁ x₂ : (A ‖ B)} where
  map1-eq : (f₁ ≡ f₂) → (g₁ ≡ g₂) → (x₁ ≡ x₂) → (map1 f₁ g₁ x₁ ≡ map1 f₂ g₂ x₂)
  map1-eq (intro f₁f₂) (intro g₁g₂) (Left  xy) = congruence₁(f₁) xy 🝖 f₁f₂
  map1-eq (intro f₁f₂) (intro g₁g₂) (Right xy) = congruence₁(g₁) xy 🝖 g₁g₂
