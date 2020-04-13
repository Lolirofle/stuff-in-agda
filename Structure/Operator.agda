module Structure.Operator where

import Lvl
open import Lang.Instance
open import Logic.Predicate
open import Logic
open import Sets.Setoid
open import Structure.Function
open import Structure.Relator.Properties
open import Syntax.Function
open import Type

private variable ℓ ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ : Lvl.Level
private variable A₁ A₂ B : Type{ℓ}

module _
  ⦃ _ : Equiv{ℓₗ₁}(A₁) ⦄
  ⦃ _ : Equiv{ℓₗ₂}(A₂) ⦄
  ⦃ _ : Equiv{ℓₗ₃}(B) ⦄
  (_▫_ : A₁ → A₂ → B)
  where

  -- The operator `_▫_` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
  -- `congruence` is the defining property of a binary operation.
  record BinaryOperator : Type{Lvl.of(A₁) Lvl.⊔ Lvl.of(A₂) Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃} where
    constructor intro
    field congruence : ∀{x₁ y₁ : A₁} → (x₁ ≡ y₁) → ∀{x₂ y₂ : A₂} → (x₂ ≡ y₂) → (x₁ ▫ x₂ ≡ y₁ ▫ y₂)

    instance
      left : ∀{x} → Function(_▫ x)
      left = intro(proof ↦ congruence proof (reflexivity(_≡_)))

    instance
      right : ∀{x} → Function(x ▫_)
      right = intro(proof ↦ congruence (reflexivity(_≡_)) proof)

    congruenceₗ : ∀{x₁ x₂}{y} → (x₁ ≡ x₂) → (x₁ ▫ y ≡ x₂ ▫ y)
    congruenceₗ = Function.congruence(left)

    congruenceᵣ : ∀{x}{y₁ y₂} → (y₁ ≡ y₂) → (x ▫ y₁ ≡ x ▫ y₂)
    congruenceᵣ = Function.congruence(right)

  [≡]-congruence2-left : ⦃ inst : BinaryOperator ⦄ → (x : _) → Function(_▫ x)
  [≡]-congruence2-left = x ↦ inst-fn(BinaryOperator.left) {x}

  [≡]-congruence2-right : ⦃ inst : BinaryOperator ⦄ → (x : _) → Function(x ▫_)
  [≡]-congruence2-right = x ↦ inst-fn(BinaryOperator.right) {x}

  [≡]-with2 = inst-fn BinaryOperator.congruence

  [≡]-with2ₗ : ⦃ inst : BinaryOperator ⦄ → (a : A₂) → ∀{x y : A₁} → (x ≡ y) → (x ▫ a ≡ y ▫ a)
  [≡]-with2ₗ _ = inst-fn BinaryOperator.congruenceₗ -- ([≡]-with(_▫ a) ⦃ [≡]-congruence2-left ⦃ inst ⦄ a ⦄)

  [≡]-with2ᵣ : ⦃ inst : BinaryOperator ⦄ → (a : A₁) → ∀{x y : A₂} → (x ≡ y) → (a ▫ x ≡ a ▫ y)
  [≡]-with2ᵣ _ = inst-fn BinaryOperator.congruenceᵣ
