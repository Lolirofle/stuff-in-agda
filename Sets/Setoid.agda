module Sets.Setoid where -- TODO: Move to Structure.Setoid

import Lvl
open import Functional.Dependent
open import Lang.Instance
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties using (Reflexivity ; Symmetry ; Transitivity)
open import Syntax.Function
import      Type

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₒ₃ : Lvl.Level

module _ where
  open Type

  -- An instance of `Equiv(T)` is that the type `T` has an equivalence relation which may be treated as a default one.
  -- Helps finding an instance of an equivalence relation for a type.
  record Equiv (T : Type{ℓₒ}) : Type{Lvl.𝐒(ℓₒ)} where
    constructor intro

    infixl 15 _≡_ _≢_
    field
      _≡_ : T → T → Type{ℓₒ}

    field
      instance ⦃ [≡]-equivalence ⦄ : Equivalence(_≡_)

    _≢_ : T → T → Type{ℓₒ}
    a ≢ b = ¬(a ≡ b)

    open Equivalence([≡]-equivalence) public

  open Equiv ⦃ ... ⦄ using (_≡_ ; _≢_ ; [≡]-equivalence) public
  {-# INLINE _≡_ #-}
  {-# DISPLAY Equiv._≡_ a b = a ≡ b #-}

  -- A set and an equivalence relation on it
  Setoid : Type{Lvl.𝐒(ℓₒ)}
  Setoid{ℓₒ} = ∃(Equiv{ℓₒ})

module Setoid(setoid : Setoid{ℓₒ}) where
  Type : Type.Type{ℓₒ}
  Type = [∃]-witness setoid

  open Equiv([∃]-proof setoid) public

open Type

-- TODO: Maybe these should be moved and renamed to function like all other properties in Structure.Operator and Structure.Function

-- The function `f` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (f : A → B) where
  record Function : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro

    field
      congruence : ∀{x y : A} → (x ≡ y) → (f(x) ≡ f(y))
  [≡]-with = inst-fn Function.congruence

_→ᶠⁿ_ : (A : Type{ℓₒ₁}) → (B : Type{ℓₒ₂}) → ⦃ _ : Equiv(A) ⦄ → ⦃ _ : Equiv(B) ⦄ → Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}
A →ᶠⁿ B = ∃(Function{A = A}{B = B})

module _ where
  open Structure.Relator.Properties

  module _ {A₁ : Type{ℓₒ₁}} ⦃ _ : Equiv(A₁) ⦄ {A₂ : Type{ℓₒ₂}} ⦃ _ : Equiv(A₂) ⦄ {B : Type{ℓₒ₃}} ⦃ _ : Equiv(B) ⦄ (_▫_ : A₁ → A₂ → B) where
    -- The operator `_▫_` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
    record BinaryOperator : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃} where
      constructor intro

      field
        congruence : ∀{x₁ y₁ : A₁} → (x₁ ≡ y₁) → ∀{x₂ y₂ : A₂} → (x₂ ≡ y₂) → (x₁ ▫ x₂ ≡ y₁ ▫ y₂)

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

-- The unary relator `P` "(behaves like)/is a relator" in the context of `_≡_` from the Equiv instance.
module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ (P : A → Type{ℓₒ₂}) where
  record UnaryRelator : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field
      substitution : ∀{x y : A} → (x ≡ y) → P(x) → P(y)
  substitute₁ = inst-fn UnaryRelator.substitution

-- The binary relator `_▫_` "(behaves like)/is a relator" in the context of `_≡_` from the Equiv instance.
module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (_▫_ : A → B → Type{ℓₒ₃}) where
  record BinaryRelator : Type{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃} where
    constructor intro

    field
      substitution : ∀{x₁ y₁ : A}{x₂ y₂ : B} → (x₁ ≡ y₁) → (x₂ ≡ y₂) → (x₁ ▫ x₂) → (y₁ ▫ y₂)
  substitute₂ = inst-fn BinaryRelator.substitution
