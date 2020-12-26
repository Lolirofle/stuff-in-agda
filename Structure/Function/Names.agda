module Structure.Function.Names where

open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
import      Lvl
open import Structure.Setoid.Uniqueness
open import Structure.Setoid
open import Type

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₒ₄ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ ℓₗ₄ : Lvl.Level

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄ where
  Injective : (A → B) → Stmt
  Injective(f) = (∀{x y : A} → (f(x) ≡ f(y)) → (x ≡ y))

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄ where
  Surjective : (A → B) → Stmt
  Surjective(f) = (∀{y : B} → ∃(x ↦ f(x) ≡ y))

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄ where
  Bijective : (A → B) → Stmt
  Bijective(f) = (∀{y : B} → ∃!(x ↦ f(x) ≡ y))

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄ where
  InversesOn : (A → B) → (B → A) → B → Stmt
  InversesOn f g x = ((f ∘ g)(x) ≡ x)

  Inverses : (A → B) → (B → A) → Stmt
  Inverses f g = ∀¹(InversesOn f g)

  Constant : (A → B) → Stmt
  Constant(f) = (∀{x y : A} → (f(x) ≡ f(y)))

module _ {A : Type{ℓₒ}} ⦃ equiv : Equiv{ℓₗ}(A) ⦄ where
  Fixpoint : (A → A) → A → Stmt
  Fixpoint f(x) = (f(x) ≡ x)

  InvolutionOn : (A → A) → A → Stmt
  InvolutionOn f(x) = InversesOn f f x
  -- (f ∘ f)(x) ≡ x
  -- f(f(x)) ≡ x

  Involution : (A → A) → Stmt
  Involution(f) = Inverses f f

  IdempotentOn : (A → A) → A → Stmt
  IdempotentOn f(x) = Fixpoint f(f(x))
  -- (f ∘ f)(x) ≡ f(x)
  -- f(f(x)) ≡ f(x)

  Idempotent : (A → A) → Stmt
  Idempotent(f) = ∀ₗ(IdempotentOn f)

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄ where
  Congruence₁ : (A → B) → Stmt
  Congruence₁(f) = (∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y)))

  module _ {C : Type{ℓₒ₃}} ⦃ _ : Equiv{ℓₗ₃}(C) ⦄ where
    Congruence₂ : (A → B → C) → Stmt
    Congruence₂(f) = (∀{x₁ y₁ : A}{x₂ y₂ : B} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (f x₁ x₂ ≡ f y₁ y₂))

    module _ {D : Type{ℓₒ₄}} ⦃ _ : Equiv{ℓₗ₄}(D) ⦄ where
      Congruence₃ : (A → B → C → D) → Stmt
      Congruence₃(f) = (∀{x₁ y₁ : A}{x₂ y₂ : B}{x₃ y₃ : C} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₃ ≡ y₃) → (f x₁ x₂ x₃ ≡ f y₁ y₂ y₃))
