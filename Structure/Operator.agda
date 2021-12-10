module Structure.Operator where

import      Lvl
open import Functional.Instance
open import Structure.Setoid
open import Structure.Function.Names
open import Structure.Function using (Function ; intro)
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ : Lvl.Level
private variable A₁ A₂ A₃ B : Type{ℓ}

module _
  ⦃ equiv-A₁ : Equiv{ℓₑ₁}(A₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₑ₂}(A₂) ⦄
  ⦃ equiv-B  : Equiv{ℓₑ₃}(B) ⦄
  (_▫_ : A₁ → A₂ → B)
  where

  -- The operator `_▫_` is a function/operator with respect to the setoids of the Equiv instances.
  -- `congruence` is the defining property of a binary operation.
  record BinaryOperator : Type{Lvl.of(A₁) Lvl.⊔ Lvl.of(A₂) Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₑ₃} where
    constructor intro
    field congruence : Congruence₂(_▫_)

    unary₁ : ∀{b} → Function(_▫ b)
    unary₁ = intro(p₁ ↦ congruence p₁ (reflexivity(_≡_)))

    unary₂ : ∀{a} → Function(a ▫_)
    unary₂ = intro(p₂ ↦ congruence (reflexivity(_≡_)) p₂)

    congruence₁ = \b {a₁}{a₂} → Function.congruence(unary₁{b}) {a₁}{a₂}
    congruence₂ = \a {b₁}{b₂} → Function.congruence(unary₂{a}) {b₁}{b₂}

  BinaryOperator-unary₁ = inferArg BinaryOperator.unary₁
  BinaryOperator-unary₂ = inferArg BinaryOperator.unary₂

  congruence₂-₁ = inferArg BinaryOperator.congruence₁
  congruence₂-₂ = inferArg BinaryOperator.congruence₂

  BinaryOperator-unary-intro : (∀{y} → Function(_▫ y)) → (∀{x} → Function(x ▫_)) → BinaryOperator
  BinaryOperator.congruence (BinaryOperator-unary-intro l r) {x₁} {y₁} {x₂} {y₂} leq req = Function.congruence l leq 🝖 Function.congruence r req

module _
  ⦃ equiv-A₁ : Equiv{ℓₑ₁}(A₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₑ₂}(A₂) ⦄
  ⦃ equiv-A₃ : Equiv{ℓₑ₃}(A₃) ⦄
  ⦃ equiv-B  : Equiv{ℓₑ₄}(B) ⦄
  (_▫_▫_ : A₁ → A₂ → A₃ → B)
  where

  record TrinaryOperator : Type{Lvl.of(A₁) Lvl.⊔ Lvl.of(A₂) Lvl.⊔ Lvl.of(A₃) Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₑ₃ Lvl.⊔ ℓₑ₄} where
    constructor intro
    field congruence : Congruence₃(_▫_▫_)

    unary₁ : ∀{b}{c} → Function(_▫ b ▫ c)
    unary₁ = intro(p₁ ↦ congruence p₁ (reflexivity(_≡_)) (reflexivity(_≡_)))

    unary₂ : ∀{a}{c} → Function(a ▫_▫ c)
    unary₂ = intro(p₂ ↦ congruence(reflexivity(_≡_)) p₂ (reflexivity(_≡_)))

    unary₃ : ∀{a}{b} → Function(a ▫ b ▫_)
    unary₃ = intro(p₃ ↦ congruence(reflexivity(_≡_)) (reflexivity(_≡_)) p₃)

    binary₁,₂ : ∀{c} → BinaryOperator(_▫_▫ c)
    binary₁,₂ = intro(p₁ ↦ p₂ ↦ congruence p₁ p₂ (reflexivity(_≡_)))

    binary₁,₃ : ∀{b} → BinaryOperator(_▫ b ▫_)
    binary₁,₃ = intro(p₁ ↦ p₃ ↦ congruence p₁ (reflexivity(_≡_)) p₃)

    binary₂,₃ : ∀{a} → BinaryOperator(a ▫_▫_)
    binary₂,₃ = intro(p₂ ↦ p₃ ↦ congruence (reflexivity(_≡_)) p₂ p₃)

    congruence₁ = \b c {a₁}{a₂} → Function.congruence(unary₁{b}{c}) {a₁}{a₂}
    congruence₂ = \a c {b₁}{b₂} → Function.congruence(unary₂{a}{c}) {b₁}{b₂}
    congruence₃ = \a b {c₁}{c₂} → Function.congruence(unary₃{a}{b}) {c₁}{c₂}

    congruence₁,₂ = \c {a₁}{a₂}{b₁}{b₂} → BinaryOperator.congruence(binary₁,₂{c}) {a₁}{a₂}{b₁}{b₂}
    congruence₁,₃ = \b {a₁}{a₂}{c₁}{c₂} → BinaryOperator.congruence(binary₁,₃{b}) {a₁}{a₂}{c₁}{c₂}
    congruence₂,₃ = \a {b₁}{b₂}{c₁}{c₂} → BinaryOperator.congruence(binary₂,₃{a}) {b₁}{b₂}{c₁}{c₂}

  TrinaryOperator-unary₁    = inferArg TrinaryOperator.unary₁
  TrinaryOperator-unary₂    = inferArg TrinaryOperator.unary₂
  TrinaryOperator-unary₃    = inferArg TrinaryOperator.unary₃
  TrinaryOperator-binary₁,₂ = inferArg TrinaryOperator.binary₁,₂
  TrinaryOperator-binary₁,₃ = inferArg TrinaryOperator.binary₁,₃
  TrinaryOperator-binary₂,₃ = inferArg TrinaryOperator.binary₂,₃

  congruence₃-₁   = inferArg TrinaryOperator.congruence₁
  congruence₃-₂   = inferArg TrinaryOperator.congruence₂
  congruence₃-₃   = inferArg TrinaryOperator.congruence₃
  congruence₃-₁,₂ = inferArg TrinaryOperator.congruence₁,₂
  congruence₃-₁,₃ = inferArg TrinaryOperator.congruence₁,₃
  congruence₃-₂,₃ = inferArg TrinaryOperator.congruence₂,₃

  TrinaryOperator-unary-intro : (∀{y}{z} → Function(_▫ y ▫ z)) → (∀{x}{z} → Function(x ▫_▫ z)) → (∀{x}{y} → Function(x ▫ y ▫_)) → TrinaryOperator
  TrinaryOperator.congruence (TrinaryOperator-unary-intro fn₁ fn₂ fn₃) eq₁ eq₂ eq₃ = Function.congruence fn₁ eq₁ 🝖 Function.congruence fn₂ eq₂ 🝖 Function.congruence fn₃ eq₃

module _
  ⦃ equiv-A₁ : Equiv{ℓₑ₁}(A₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₑ₂}(A₂) ⦄
  ⦃ equiv-B  : Equiv{ℓₑ₃}(B) ⦄
  (_▫_ : A₁ → A₂ → B)
  where

  congruence₂ = inferArg(BinaryOperator.congruence{_▫_ = _▫_})

module _
  ⦃ equiv-A₁ : Equiv{ℓₑ₁}(A₁) ⦄
  ⦃ equiv-A₂ : Equiv{ℓₑ₂}(A₂) ⦄
  ⦃ equiv-A₃ : Equiv{ℓₑ₃}(A₃) ⦄
  ⦃ equiv-B  : Equiv{ℓₑ₄}(B) ⦄
  (_▫_▫_ : A₁ → A₂ → A₃ → B)
  where

  congruence₃ = inferArg(TrinaryOperator.congruence{_▫_▫_ = _▫_▫_})
