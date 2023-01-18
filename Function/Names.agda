import      Lvl

module Function.Names where

open import DependentFunctional
open import Logic.Predicate
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₒ₄ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ equiv-B : ∀{a} → Equiv{ℓₗ₃}(B(a)) ⦄ where
  -- Extensional equality on functions.
  -- Alternative definition: f ⊜ g = (∀{x} → (f(x) ≡ g(x)))
  _⊜_ : ((a : A) → B(a)) → ((a : A) → B(a)) → Type
  _⊜_ = ∀¹ ∘₂ pointwise₂,₁(_≡_)
  _⊜₁_ = _⊜_

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ equiv-B : ∀{a} → Equiv{ℓₗ₃}(B(a)) ⦄ where
  _⊜ᵢ_ : ({a : A} → B(a)) → ({a : A} → B(a)) → Type
  _⊜ᵢ_ f g = (∀{x} → (f{x} ≡ g{x}))

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₃}(B(a)) ⦄ where
  _⦃⊜⦄_ : (⦃ a : A ⦄ → B(a)) → (⦃ a : A ⦄ → B(a)) → Type
  _⦃⊜⦄_ f g = (∀{x} → (f ⦃ x ⦄ ≡ g ⦃ x ⦄))

module _ {A₁ : Type{ℓₒ₁}} {A₂ : A₁ → Type{ℓₒ₂}} {B : (a₁ : A₁) → A₂(a₁) → Type{ℓₒ₃}} ⦃ equiv-B : ∀{a₁}{a₂} → Equiv{ℓₗ₃}(B(a₁)(a₂)) ⦄ where
  -- Alternative definition: f ⊜ g = (∀{x}{y} → (f(x)(y) ≡ g(x)(y)))
  _⊜₂_ : (f g : ∀(a₁)(a₂) → B(a₁)(a₂)) → Type
  _⊜₂_ = ∀¹ ∘₂ (∀¹ ∘₃ pointwise₂,₂(_≡_))

module _ {A₁ : Type{ℓₒ₁}} {A₂ : A₁ → Type{ℓₒ₂}} {A₃ : (a₁ : A₁) → A₂(a₁) → Type{ℓₒ₃}} {B : (a₁ : A₁) → (a₂ : A₂(a₁)) → A₃(a₁)(a₂) → Type{ℓₒ₄}} ⦃ equiv-B : ∀{a₁}{a₂}{a₃} → Equiv{ℓₗ₃}(B(a₁)(a₂)(a₃)) ⦄ where
  -- Alternative definition: f ⊜ g = (∀{x}{y}{z} → (f(x)(y)(z) ≡ g(x)(y)(z)))
  _⊜₃_ : (f g : ∀(a₁)(a₂)(a₃) → B(a₁)(a₂)(a₃)) → Type
  _⊜₃_ = ∀¹ ∘₂ (∀¹ ∘₃ (∀¹ ∘₄ pointwise₂,₃(_≡_)))
