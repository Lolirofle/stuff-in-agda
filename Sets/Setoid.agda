module Sets.Setoid where

import Lvl
open import Functional
open import Logic.Propositional
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties

module _ {ℓₒ} where
  -- Helps finding an instance of an equivalence relation from a type
  record Equiv (T : Set(ℓₒ)) : Set(Lvl.𝐒(ℓₒ)) where
    constructor intro

    infixl 15 _≡_ _≢_
    field
      _≡_ : T → T → Set(ℓₒ)

    field
      instance ⦃ [≡]-equivalence ⦄ : Equivalence(_≡_)

    _≢_ : T → T → Set(ℓₒ)
    a ≢ b = ¬(a ≡ b)
  open Equiv ⦃ ... ⦄ public

  -- A set and an equivalence relation on it
  record Setoid : Set(Lvl.𝐒(ℓₒ)) where
    constructor intro
    field
      Type : Set(ℓₒ)
      instance ⦃ Eq ⦄ : Equiv(Type)

-- The function `f` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
module _ {ℓₒ₁}{ℓₒ₂} {T₁ : Set(ℓₒ₁)} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Set(ℓₒ₂)} ⦃ _ : Equiv(T₂) ⦄ where
  record Function (f : T₁ → T₂) : Set(ℓₒ₁ Lvl.⊔ ℓₒ₂) where
    constructor intro

    field
      congruence : ∀{x y : T₁} → (x ≡ y) → (f(x) ≡ f(y))

  [≡]-with : (f : T₁ → T₂) → ⦃ _ : Function(f) ⦄ → ∀{x y} → (x ≡ y) → (f(x) ≡ f(y))
  [≡]-with f ⦃ inst ⦄ = Function.congruence{f} (inst)

module _ {ℓₒ₁}{ℓₒ₂}{ℓₒ₃} where
  -- The operator `_▫_` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
  record BinaryOperator {T₁ : Set(ℓₒ₁)} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Set(ℓₒ₂)} ⦃ _ : Equiv(T₂) ⦄ {T₃ : Set(ℓₒ₃)} ⦃ _ : Equiv(T₃) ⦄ (_▫_ : T₁ → T₂ → T₃) : Set(ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃) where
    constructor intro

    field
      congruence : ∀{x₁ y₁ : T₁} → (x₁ ≡ y₁) → ∀{x₂ y₂ : T₂} → (x₂ ≡ y₂) → (x₁ ▫ x₂ ≡ y₁ ▫ y₂)

    instance
      left : ∀{x} → Function(_▫ x)
      left = intro(proof ↦ congruence proof (reflexivity(_≡_)))

    instance
      right : ∀{x} → Function(x ▫_)
      right = intro(proof ↦ congruence (reflexivity(_≡_)) proof)

  [≡]-congruence2-left : ∀{T₁} → ⦃ _ : Equiv(T₁) ⦄ → ∀{T₂} → ⦃ _ : Equiv(T₂) ⦄ → ∀{T₃} → ⦃ _ : Equiv(T₃) ⦄ → (_▫_ : T₁ → T₂ → T₃) → ⦃ _ : BinaryOperator(_▫_) ⦄ → ∀{x} → Function(_▫ x)
  [≡]-congruence2-left (_▫_) ⦃ inst ⦄ = BinaryOperator.left {_}{_}{_} {_▫_} (inst)

  [≡]-congruence2-right : ∀{T₁} → ⦃ _ : Equiv(T₁) ⦄ → ∀{T₂} → ⦃ _ : Equiv(T₂) ⦄ → ∀{T₃} → ⦃ _ : Equiv(T₃) ⦄ → (_▫_ : T₁ → T₂ → T₃) → ⦃ _ : BinaryOperator(_▫_) ⦄ → ∀{x} → Function(x ▫_)
  [≡]-congruence2-right (_▫_) ⦃ inst ⦄ = BinaryOperator.right {_}{_}{_} {_▫_} (inst)
