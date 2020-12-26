import      Lvl

module Function.Names where

open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.Uniqueness
open import Structure.Setoid
open import Type

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₃}(B(a)) ⦄ where
  _⊜_ : ((a : A) → B(a)) → ((a : A) → B(a)) → Stmt
  _⊜_ f g = (∀{x} → (f(x) ≡ g(x)))

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₃}(B(a)) ⦄ where
  _⊜ᵢ_ : ({a : A} → B(a)) → ({a : A} → B(a)) → Stmt
  _⊜ᵢ_ f g = (∀{x} → (f{x} ≡ g{x}))

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₃}(B(a)) ⦄ where
  _⦃⊜⦄_ : (⦃ a : A ⦄ → B(a)) → (⦃ a : A ⦄ → B(a)) → Stmt
  _⦃⊜⦄_ f g = (∀{x} → (f ⦃ x ⦄ ≡ g ⦃ x ⦄))

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
