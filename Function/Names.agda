import      Lvl

module Function.Names where

open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid.Uniqueness
open import Sets.Setoid.WithLvl
open import Type

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level

module _ {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv{ℓₗ₃}(B(a)) ⦄ where
  _⊜_ : ((a : A) → B(a)) → ((a : A) → B(a)) → Stmt
  _⊜_ f g = (∀{x} → (f(x) ≡ g(x)))

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ ⦃ _ : Equiv{ℓₗ₃}(A → B) ⦄ where
  FunctionExtensionalityOn : (A → B) → (A → B) → Stmt
  FunctionExtensionalityOn(f)(g) = ((f ⊜ g) → (f ≡ g))

module _ (A : Type{ℓₒ₁}) (B : Type{ℓₒ₂}) ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ ⦃ _ : Equiv{ℓₗ₃}(A → B) ⦄ where
  FunctionExtensionality : Stmt
  FunctionExtensionality = ∀²(FunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{ℓₗ₂}{ℓₗ₃}{A}{B})

-- TODO: Move below to Structure.Function.Names

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ where
  Function : (A → B) → Stmt
  Function(f) = (∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y)))

  Injective : (A → B) → Stmt
  Injective(f) = (∀{x y : A} → (f(x) ≡ f(y)) → (x ≡ y))

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ where
  Surjective : (A → B) → Stmt
  Surjective(f) = (∀{y : B} → ∃(x ↦ f(x) ≡ y))

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ where
  Bijective : (A → B) → Stmt
  Bijective(f) = (∀{y : B} → ∃!(x ↦ f(x) ≡ y))

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ where
  InversesOn : (A → B) → (B → A) → B → Stmt
  InversesOn f g x = ((f ∘ g)(x) ≡ x)

  Inverses : (A → B) → (B → A) → Stmt
  Inverses f g = ∀¹(InversesOn f g)

  Constant : (A → B) → Stmt
  Constant(f) = (∀{x y : A} → (f(x) ≡ f(y)))

module _ {A : Type{ℓₒ}} ⦃ _ : Equiv{ℓₗ}(A) ⦄ where
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
