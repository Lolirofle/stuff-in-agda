module Structure.Function.Proofs where

import      Lvl
open import Functional
open import Structure.Function
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level
private variable T A B C D : Type{ℓ}

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄
  ⦃ equiv-D : Equiv{ℓₑ₄}(D) ⦄
  {f : C → D} ⦃ func : Function(f) ⦄
  {_▫_ : A → B → C} ⦃ oper : BinaryOperator(_▫_) ⦄
  where

  [∘₂]-function : BinaryOperator(f ∘₂ (_▫_))
  BinaryOperator.congruence [∘₂]-function = congruence₁(f) ∘₂ congruence₂(_▫_)

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-C : Equiv{ℓₑ₃}(C) ⦄
  {_▫_ : A → B → C}
  ⦃ funcₗ : ∀{x} → Function(x ▫_) ⦄
  ⦃ funcᵣ : ∀{y} → Function(_▫ y) ⦄
  where

  binaryOperator-from-function : BinaryOperator(_▫_)
  BinaryOperator.congruence binaryOperator-from-function xy1 xy2 = congruence₁(_▫ _) xy1 🝖 congruence₁(_ ▫_) xy2

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {_▫_ : A → A → B}
  ⦃ funcᵣ : ∀{y} → Function(_▫ y) ⦄
  ⦃ comm : Commutativity(_▫_) ⦄
  where

  functionₗ-from-commutative-functionᵣ : ∀{x} → Function(x ▫_)
  Function.congruence (functionₗ-from-commutative-functionᵣ{a}) {x}{y} xy = commutativity(_▫_) {a}{x} 🝖 congruence₁(_▫ a) xy 🝖 commutativity(_▫_) {y}{a}

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {_▫_ : A → A → B}
  ⦃ funcᵣ : ∀{x} → Function(x ▫_) ⦄
  ⦃ comm : Commutativity(_▫_) ⦄
  where

  functionᵣ-from-commutative-functionₗ : ∀{y} → Function(_▫ y)
  Function.congruence (functionᵣ-from-commutative-functionₗ{a}) {x}{y} xy = commutativity(_▫_) {x}{a} 🝖 congruence₁(a ▫_) xy 🝖 commutativity(_▫_) {a}{y}
