import      Lvl

module Function.Names where

open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid.Uniqueness
open import Sets.Setoid hiding (Function)
open import Type

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} {B : A → Type{ℓₒ₂}} ⦃ _ : ∀{a} → Equiv(B(a)) ⦄ where
  _⊜_ : ((a : A) → B(a)) → ((a : A) → B(a)) → Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  _⊜_ f g = (∀{x} → (f(x) ≡ g(x)))

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ ⦃ _ : Equiv(A → B) ⦄ where
  FunctionExtensionalityOn : (A → B) → (A → B) → Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  FunctionExtensionalityOn(f)(g) = ((f ⊜ g) → (f ≡ g))

module _ {ℓₒ₁}{ℓₒ₂} where
  open import Relator.Equals.Proofs.Equivalence

  FunctionExtensionality : Stmt{Lvl.𝐒(ℓₒ₁ Lvl.⊔ ℓₒ₂)}
  FunctionExtensionality = ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} → ∀²(FunctionExtensionalityOn{ℓₒ₁}{ℓₒ₂}{A}{B} ⦃ [≡]-equiv ⦄ ⦃ [≡]-equiv ⦄)

-- TODO: Move below to Structure.Function.Names

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ where
  Function : (A → B) → Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  Function(f) = (∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y)))

  Injective : (A → B) → Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  Injective(f) = (∀{x y : A} → (f(x) ≡ f(y)) → (x ≡ y))

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ where
  Surjective : (A → B) → Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  Surjective(f) = (∀{y : B} → ∃(x ↦ f(x) ≡ y))

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ where
  Bijective : (A → B) → Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  Bijective(f) = (∀{y : B} → ∃!(x ↦ f(x) ≡ y))

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ where
  InversesOn : (A → B) → (B → A) → B → Stmt{ℓₒ₂}
  InversesOn f g x = ((f ∘ g)(x) ≡ x)

  Inverses : (A → B) → (B → A) → Stmt{ℓₒ₂}
  Inverses f g = ∀¹(InversesOn f g)

  Constant : (A → B) → Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  Constant(f) = (∀{x y : A} → (f(x) ≡ f(y)))

module _ {ℓₒ} {A : Type{ℓₒ}} ⦃ _ : Equiv(A) ⦄ where
  Fixpoint : (A → A) → A → Stmt{ℓₒ}
  Fixpoint f(x) = (f(x) ≡ x)

  InvolutionOn : (A → A) → A → Stmt{ℓₒ}
  InvolutionOn f(x) = InversesOn f f x
  -- (f ∘ f)(x) ≡ x
  -- f(f(x)) ≡ x

  Involution : (A → A) → Stmt{ℓₒ}
  Involution(f) = Inverses f f

  IdempotentOn : (A → A) → A → Stmt{ℓₒ}
  IdempotentOn f(x) = Fixpoint f(f(x))
  -- (f ∘ f)(x) ≡ f(x)
  -- f(f(x)) ≡ f(x)

  Idempotent : (A → A) → Stmt{ℓₒ}
  Idempotent(f) = ∀ₗ(IdempotentOn f)
