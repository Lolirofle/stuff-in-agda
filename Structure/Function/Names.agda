module Structure.Function.Names where

open import Function.Names
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

module _ {A : Type{ℓₒ₁}} (_▫₁_ : A → A → Type{ℓₗ₁}) {B : Type{ℓₒ₂}} (_▫₂_ : B → B → Type{ℓₗ₂}) where
  Compatible₁ : (A → B) → Stmt
  Compatible₁(f) = (∀{x y : A} → (x ▫₁ y) → (f(x) ▫₂ f(y)))

  module _ {C : Type{ℓₒ₃}} (_▫₃_ : C → C → Type{ℓₗ₃}) where
    Compatible₂ : (A → B → C) → Stmt
    Compatible₂(f) = (∀{x₁ y₁ : A}{x₂ y₂ : B} → (x₁ ▫₁ y₁) → (x₂ ▫₂ y₂) → (f x₁ x₂ ▫₃ f y₁ y₂))

    module _ {D : Type{ℓₒ₄}} (_▫₄_ : D → D → Type{ℓₗ₄}) where
      Compatible₃ : (A → B → C → D) → Stmt
      Compatible₃(f) = (∀{x₁ y₁ : A}{x₂ y₂ : B}{x₃ y₃ : C} → (x₁ ▫₁ y₁) → (x₂ ▫₂ y₂) → (x₃ ▫₃ y₃) → (f x₁ x₂ x₃ ▫₄ f y₁ y₂ y₃))

module _ {A : Type{ℓₒ₁}} ⦃ equiv-A : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ equiv-B : Equiv{ℓₗ₂}(B) ⦄ where
  Congruence₁ : (A → B) → Stmt
  Congruence₁ = Compatible₁(_≡_)(_≡_)

  module _ {C : Type{ℓₒ₃}} ⦃ equiv-C : Equiv{ℓₗ₃}(C) ⦄ where
    Congruence₂ : (A → B → C) → Stmt
    Congruence₂ = Compatible₂(_≡_)(_≡_)(_≡_)

    module _ {D : Type{ℓₒ₄}} ⦃ equiv-D : Equiv{ℓₗ₄}(D) ⦄ where
      Congruence₃ : (A → B → C → D) → Stmt
      Congruence₃ = Compatible₃(_≡_)(_≡_)(_≡_)(_≡_)

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ ⦃ _ : Equiv{ℓₗ₃}(A → B) ⦄ where
  FunctionExtensionalityOn : (A → B) → (A → B) → Stmt
  FunctionExtensionalityOn(f)(g) = ((f ⊜ g) → (f ≡ g))

  FunctionApplicationOn : (A → B) → (A → B) → Stmt
  FunctionApplicationOn(f)(g) = ((f ≡ g) → (f ⊜ g))

module _ (A : Type{ℓₒ₁}) (B : Type{ℓₒ₂}) ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ ⦃ _ : Equiv{ℓₗ₃}(A → B) ⦄ where
  FunctionExtensionality : Stmt
  FunctionExtensionality = ∀²(FunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})

  FunctionApplication : Stmt
  FunctionApplication = ∀²(FunctionApplicationOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄ ⦃ _ : Equiv{ℓₗ₃}((a : A) → B(a)) ⦄ where
  DependentFunctionExtensionalityOn : ((a : A) → B(a)) → ((a : A) → B(a)) → Stmt
  DependentFunctionExtensionalityOn(f)(g) = ((f ⊜ g) → (f ≡ g))

module _ (A : Type{ℓₒ₁}) (B : A → Type{ℓₒ₂}) ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄ ⦃ _ : Equiv{ℓₗ₃}((a : A) → B(a)) ⦄ where
  DependentFunctionExtensionality : Stmt
  DependentFunctionExtensionality = ∀²(DependentFunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄ ⦃ _ : Equiv{ℓₗ₃}({a : A} → B(a)) ⦄ where
  DependentImplicitFunctionExtensionalityOn : ({a : A} → B(a)) → ({a : A} → B(a)) → Stmt
  DependentImplicitFunctionExtensionalityOn(f)(g) = (((\{a} → f{a}) ⊜ᵢ (\{a} → g{a})) → ((\{a} → f{a}) ≡ (\{a} → g{a})))

module _ (A : Type{ℓₒ₁}) (B : A → Type{ℓₒ₂}) ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄ ⦃ _ : Equiv{ℓₗ₃}({a : A} → B(a)) ⦄ where
  DependentImplicitFunctionExtensionality : Stmt
  DependentImplicitFunctionExtensionality = ∀²(DependentImplicitFunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄ ⦃ _ : Equiv{ℓₗ₃}(⦃ a : A ⦄ → B(a)) ⦄ where
  DependentInstanceFunctionExtensionalityOn : (⦃ a : A ⦄ → B(a)) → (⦃ a : A ⦄ → B(a)) → Stmt
  DependentInstanceFunctionExtensionalityOn(f)(g) = (((\ ⦃ a ⦄ → f ⦃ a ⦄) ⦃⊜⦄ (\ ⦃ a ⦄ → g ⦃ a ⦄)) → ((\ ⦃ a ⦄ → f ⦃ a ⦄) ≡ (\ ⦃ a ⦄ → g ⦃ a ⦄)))

module _ (A : Type{ℓₒ₁}) (B : A → Type{ℓₒ₂}) ⦃ _ : ∀{a} → Equiv{ℓₗ₂}(B(a)) ⦄ ⦃ _ : Equiv{ℓₗ₃}(⦃ a : A ⦄ → B(a)) ⦄ where
  DependentInstanceFunctionExtensionality : Stmt
  DependentInstanceFunctionExtensionality = ∀²(DependentInstanceFunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})
