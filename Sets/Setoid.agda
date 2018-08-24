module Sets.Setoid{ℓₗ} where

import Lvl
open import Functional
import      Logic.Propositional
import      Structure.Relator.Equivalence
import      Structure.Relator.Properties

module _ {ℓₒ} where
  open Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
  open Structure.Relator.Equivalence{ℓₗ}{ℓₒ}
  open Structure.Relator.Properties{ℓₗ}{ℓₒ}

  -- Helps finding an instance of an equivalence relation from a type
  record Equiv (T : Set(ℓₒ)) : Set(Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)) where
    constructor intro

    infixl 15 _≡_ _≢_
    field
      _≡_ : T → T → Set(ℓₗ Lvl.⊔ ℓₒ)

    field
      instance ⦃ [≡]-equivalence ⦄ : Equivalence(_≡_)

    _≢_ : T → T → Set(ℓₗ Lvl.⊔ ℓₒ)
    a ≢ b = ¬(a ≡ b)
  open Equiv ⦃ ... ⦄ public

  -- A set and an equivalence relation on it
  record Setoid : Set(Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)) where
    constructor intro
    field
      Type : Set(ℓₒ)
      instance ⦃ Eq ⦄ : Equiv(Type)

-- The function `f` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
module _ {ℓₒ₁}{ℓₒ₂} where
  open Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂}
  open Structure.Relator.Equivalence{ℓₗ}{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  open Structure.Relator.Properties{ℓₗ}{ℓₒ₁ Lvl.⊔ ℓₒ₂}

  record Function {T₁ : Set(ℓₒ₁)} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Set(ℓₒ₂)} ⦃ _ : Equiv(T₂) ⦄ (f : T₁ → T₂) : Set(ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂) where
    constructor intro

    field
      congruence : ∀{x y : T₁} → (x ≡ y) → (f(x) ≡ f(y))

  [≡]-with : ∀{T₁} → ⦃ _ : Equiv(T₁) ⦄ → ∀{T₂} → ⦃ _ : Equiv(T₂) ⦄ → (f : T₁ → T₂) → ⦃ _ : Function(f) ⦄ → ∀{x y} → (x ≡ y) → (f(x) ≡ f(y))
  [≡]-with f ⦃ inst ⦄ = Function.congruence {_}{_} {f} (inst)

module _ {ℓₒ₁}{ℓₒ₂}{ℓₒ₃} where
  open Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃}
  open Structure.Relator.Equivalence{ℓₗ}{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃}
  open Structure.Relator.Properties{ℓₗ}

  -- The operator `_▫_` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
  record BinaryOperator {T₁ : Set(ℓₒ₁)} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Set(ℓₒ₂)} ⦃ _ : Equiv(T₂) ⦄ {T₃ : Set(ℓₒ₃)} ⦃ _ : Equiv(T₃) ⦄ (_▫_ : T₁ → T₂ → T₃) : Set(ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₒ₃) where
    constructor intro

    field
      congruence : ∀{x₁ y₁ : T₁} → (x₁ ≡ y₁) → ∀{x₂ y₂ : T₂} → (x₂ ≡ y₂) → (x₁ ▫ x₂ ≡ y₁ ▫ y₂)

    instance
      left : ∀{x} → Function(_▫ x)
      left = intro(proof ↦ congruence proof reflexivity)

    instance
      right : ∀{x} → Function(x ▫_)
      right = intro(proof ↦ congruence reflexivity proof)

  instance
    [≡]-congruence2-left : ∀{T₁} → ⦃ _ : Equiv(T₁) ⦄ → ∀{T₂} → ⦃ _ : Equiv(T₂) ⦄ → ∀{T₃} → ⦃ _ : Equiv(T₃) ⦄ → (_▫_ : T₁ → T₂ → T₃) → ⦃ _ : BinaryOperator(_▫_) ⦄ → ∀{x} → Function(_▫ x)
    [≡]-congruence2-left (_▫_) ⦃ inst ⦄ = BinaryOperator.left {_}{_}{_} {_▫_} (inst)

  instance
    [≡]-congruence2-right : ∀{T₁} → ⦃ _ : Equiv(T₁) ⦄ → ∀{T₂} → ⦃ _ : Equiv(T₂) ⦄ → ∀{T₃} → ⦃ _ : Equiv(T₃) ⦄ → (_▫_ : T₁ → T₂ → T₃) → ⦃ _ : BinaryOperator(_▫_) ⦄ → ∀{x} → Function(x ▫_)
    [≡]-congruence2-right (_▫_) ⦃ inst ⦄ = BinaryOperator.right {_}{_}{_} {_▫_} (inst)
