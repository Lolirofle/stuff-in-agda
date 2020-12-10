module Structure.Operator where

import Lvl
open import Functional using (_$_)
open import Lang.Instance
open import Logic.Predicate
open import Logic
open import Structure.Setoid.WithLvl
open import Structure.Function.Names
open import Structure.Function
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ ℓₒ₄ ℓₗ ℓₗ₁ ℓₗ₂ ℓₗ₃ ℓₗ₄ : Lvl.Level
private variable A₁ A₂ A₃ B : Type{ℓ}

module _
  ⦃ equiv-A₁ : Equiv{ℓₗ₁}(A₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₗ₂}(A₂) ⦄
  ⦃ equiv-B : Equiv{ℓₗ₃}(B) ⦄
  (_▫_ : A₁ → A₂ → B)
  where

  -- The operator `_▫_` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
  -- `congruence` is the defining property of a binary operation.
  record BinaryOperator : Type{Lvl.of(A₁) Lvl.⊔ Lvl.of(A₂) Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃} where
    constructor intro
    field congruence : Congruence₂(_▫_)

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

  congruence₂ = inst-fn BinaryOperator.congruence

  congruence₂ₗ : ⦃ inst : BinaryOperator ⦄ → (a : A₂) → ∀{x y : A₁} → (x ≡ y) → (x ▫ a ≡ y ▫ a)
  congruence₂ₗ _ = inst-fn BinaryOperator.congruenceₗ -- (congruence₁(_▫ a) ⦃ [≡]-congruence2-left ⦃ inst ⦄ a ⦄)

  congruence₂ᵣ : ⦃ inst : BinaryOperator ⦄ → (a : A₁) → ∀{x y : A₂} → (x ≡ y) → (a ▫ x ≡ a ▫ y)
  congruence₂ᵣ _ = inst-fn BinaryOperator.congruenceᵣ

  functions-to-binaryOperator : ⦃ l : ∀{y} → Function(_▫ y) ⦄ ⦃ r : ∀{x} → Function(x ▫_) ⦄ → BinaryOperator
  BinaryOperator.congruence functions-to-binaryOperator {x₁} {y₁} {x₂} {y₂} leq req =
    (x₁ ▫ x₂) 🝖[ _≡_ ]-[ congruence₁(_▫ x₂) leq ]
    (y₁ ▫ x₂) 🝖[ _≡_ ]-[ congruence₁(y₁ ▫_) req ]
    (y₁ ▫ y₂) 🝖-end

module _
  ⦃ equiv-A₁ : Equiv{ℓₗ₁}(A₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₗ₂}(A₂) ⦄
  ⦃ equiv-A₃ : Equiv{ℓₗ₃}(A₃) ⦄
  ⦃ equiv-B : Equiv{ℓₗ₄}(B) ⦄
  (_▫_▫_ : A₁ → A₂ → A₃ → B)
  where

  record TrinaryOperator : Type{Lvl.of(A₁) Lvl.⊔ Lvl.of(A₂) Lvl.⊔ Lvl.of(A₃) Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂ Lvl.⊔ ℓₗ₃ Lvl.⊔ ℓₗ₄} where
    constructor intro
    field congruence : Congruence₃(_▫_▫_)

  congruence₃ = inst-fn TrinaryOperator.congruence
