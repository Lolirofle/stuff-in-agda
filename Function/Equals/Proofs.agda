module Function.Equals.Proofs where

import      Lvl
open import Data
import      Functional
import      Function.Equals
open import Logic.Predicate
open import Logic.Propositional
open import Structure.Setoid
open import Structure.Function
import      Structure.Operator.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Syntax.Type
open import Type

-- TODO: Remove some of these functions and use Function.Equiv.Proofs instead

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓₑ ℓᵤ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level

module Dependent where
  open        Functional using (id)
  open import DependentFunctional
  open        Function.Equals.Dependent

  module _ {A : Type{ℓ₁}} {B : A → Type{ℓ₂}} ⦃ equiv-B : ∀{a} → Equiv{ℓₑ₂}(B(a)) ⦄ where
    [⊜]-identityₗ : Identityₗ {T₂ = (a : A) → B(a)} (_∘_)(id)
    _⊜_.proof (Identityₗ.proof [⊜]-identityₗ) {x} = reflexivity(_≡_) ⦃ Equiv.reflexivity equiv-B ⦄

  module _ {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : B → Type{ℓ₂}} ⦃ equiv-C : ∀{b} → Equiv{ℓₑ₃}(C(b)) ⦄ where
    [⊜][∘]ₗ-function-raw : ∀{f₁ f₂ : (b : B) → C(b)}{g : A → B} → (f₁ ⊜ f₂) → ((f₁ ∘ g) ⊜ (f₂ ∘ g))
    [⊜][∘]ₗ-function-raw {g = g} (intro feq) = intro(\{x} → feq{g(x)})

  module _ {A : Type{ℓ₁}} {B : A → Type{ℓ₂}} {C : (a : A) → B(a) → Type{ℓ₃}} ⦃ equiv-C : ∀{a}{b} → Equiv{ℓₑ₃}(C(a)(b)) ⦄ where
    [⊜][∘ₛ]ₗ-function-raw : ∀{f₁ f₂ : (a : A) → (b : B(a)) → C(a)(b)}{g : (a : A) → B(a)} → (f₁ ⊜ f₂) → ((f₁ ∘ₛ g) ⊜ (f₂ ∘ₛ g))
    [⊜][∘ₛ]ₗ-function-raw {g = g} (intro feq) = intro(\{x} → _⊜_.proof (feq{x}) {g(x)})

  -- module _ {A : Type{ℓ₁}} {B : Type{ℓ₂}} {C : B → Type{ℓ₃}} ⦃ _ : Equiv(B) ⦄ ⦃ equiv-C : ∀{b} → Equiv(C(b)) ⦄ {f₁ f₂ : (b : B) → C(b)} ⦃ _ : Function(f₂) ⦄ where (TODO: Requires Function to be able to take a dependent function)
    -- [⊜][∘]-binaryOperator-raw : (f₁ ⊜ f₂) → ∀{g₁ g₂ : A → B} → (g₁ ⊜ g₂) → (f₁ ∘ g₁ ⊜ f₂ ∘ g₂)
    -- [⊜][∘]-binaryOperator-raw feq (intro geq) = [⊜][∘]ₗ-function-raw feq 🝖 (intro(congruence₁(f₂) (geq)))

open Functional
open Function.Equals

private variable A B C D A₁ A₂ B₁ B₂ : Type{ℓ}

-- TODO: Rename all these so that they mention (_∘_)
module _ ⦃ _ : let _ = A in Equiv{ℓₑ₂}(B) ⦄ where
  [⊜]-identityₗ : Identityₗ {T₂ = A → B} (_∘_)(id)
  _⊜_.proof(Identityₗ.proof([⊜]-identityₗ)) = reflexivity(_≡_)

  [⊜]-identityᵣ : Identityᵣ {T₁ = A → B} (_∘_)(id)
  _⊜_.proof(Identityᵣ.proof([⊜]-identityᵣ)) = reflexivity(_≡_)

module _ ⦃ _ : Equiv{ℓₑ}(A) ⦄ where
  [⊜]-identity : Identity {T = A → A} (_∘_)(id)
  [⊜]-identity = intro ⦃ left = [⊜]-identityₗ ⦄ ⦃ right = [⊜]-identityᵣ ⦄

module _ ⦃ _ : let _ = A ; _ = B ; _ = C ; _ = D in Equiv{ℓₑ₄}(D) ⦄ where
  [⊜]-associativity : Names.AssociativityPattern {T₁ = C → D} {T₂ = B → C} {T₃ = A → B} (_∘_)(_∘_)(_∘_)(_∘_)
  _⊜_.proof ([⊜]-associativity {f} {g} {h}) {x} = reflexivity(_≡_)

module _ ⦃ _ : Equiv{ℓₑ₁}(Empty{ℓₑ}) ⦄ where
  [⊜]-emptyₗ : ∀{f g : A → Empty{ℓₑ}} → (f ⊜ g)
  [⊜]-emptyₗ {f = f} = intro(\{x} → empty(f(x)))

module _ ⦃ _ : Equiv{ℓₑ}(A) ⦄ where
  [⊜]-emptyᵣ : ∀{f g : Empty{ℓₑ} → A} → (f ⊜ g)
  [⊜]-emptyᵣ = intro(\{})

module _ ⦃ _ : Equiv{ℓₑ}(Unit{ℓᵤ}) ⦄ where
  [⊜]-unitₗ : ∀{f g : A → Unit{ℓᵤ}} → (f ⊜ g)
  [⊜]-unitₗ = intro(reflexivity(_≡_))

module _ ⦃ _ : let _ = A ; _ = B ; _ = C in Equiv{ℓₑ₃}(C) ⦄ where
  [⊜][∘]ₗ-function-raw : ∀{f₁ f₂ : B → C}{g : A → B} → (f₁ ⊜ f₂) → ((f₁ ∘ g) ⊜ (f₂ ∘ g))
  [⊜][∘]ₗ-function-raw {g = g} (intro feq) = intro(\{x} → feq{g(x)})

module _ ⦃ _ : let _ = A in Equiv{ℓₑ₂}(B) ⦄ ⦃ _ : Equiv{ℓₑ₃}(C) ⦄ {f₁ f₂ : B → C} ⦃ func₂ : Function(f₂) ⦄ {g₁ g₂ : A → B} where
  [⊜][∘]-binaryOperator-raw : (f₁ ⊜ f₂) → (g₁ ⊜ g₂) → (f₁ ∘ g₁ ⊜ f₂ ∘ g₂)
  [⊜][∘]-binaryOperator-raw feq (intro geq) = [⊜][∘]ₗ-function-raw feq 🝖 (intro(congruence₁(f₂) (geq)))

module _ ⦃ _ : let _ = A in Equiv{ℓₑ₂}(B) ⦄ ⦃ _ : Equiv{ℓₑ₃}(C) ⦄ ⦃ function : ∀{f : B → C} → Function(f) ⦄ where
  instance
    [⊜][∘]-binaryOperator : BinaryOperator(_∘_ {X = A}{Y = B}{Z = C})
    BinaryOperator.congruence [⊜][∘]-binaryOperator = [⊜][∘]-binaryOperator-raw

module _ ⦃ _ : let _ = A in Equiv{ℓₑ₂}(B) ⦄ where
  [⊜]-abstract : ∀{a b : B} → (a ≡ b) → ((x ↦ a) ⊜ ((x ↦ b) :of: (A → B)))
  [⊜]-abstract {a} {b} x = intro x

  [⊜]-apply : ∀{f g : A → B} → (f ⊜ g) → (∀{x} → (f(x) ≡ g(x)))
  [⊜]-apply (intro proof) = proof

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B₁ : Equiv{ℓₑ₂}(B₁) ⦄
  ⦃ equiv-B₂ : Equiv{ℓₑ₃}(B₂) ⦄
  {F : A → (B₁ → B₂)}
  ⦃ func : BinaryOperator(F) ⦄
  where

  instance
    [⊜]-functionᵣ : Function {A = A} {B = B₁ → B₂} ⦃ equiv-A ⦄ ⦃ [⊜]-equiv ⦄ (F)
    Function.congruence([⊜]-functionᵣ) eq = intro(\{x} → congruence₂-₁(F)(x) eq)
