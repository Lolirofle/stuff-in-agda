module Sets.Setoid{ℓₗ}{ℓₒ} where

import Lvl
open import Functional
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Structure.Relator.Equivalence{ℓₗ}{ℓₒ}
open import Structure.Relator.Properties{ℓₗ}{ℓₒ}

-- Helps finding an instance of an equivalence relation from a type
record Equiv (T : Set(ℓₒ)) : Set(Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)) where
  constructor equiv-inst

  infixl 15 _≡_ _≢_
  field
    _≡_ : T → T → Set(ℓₗ Lvl.⊔ ℓₒ)

  field
    instance ⦃ [≡]-equivalence ⦄ : Equivalence(_≡_)

  _≢_ : T → T → Set(ℓₗ Lvl.⊔ ℓₒ)
  a ≢ b = ¬(a ≡ b)
open Equiv ⦃ ... ⦄ public

-- The function `f` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
record Congruence {T₁ : Set(ℓₒ)} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Set(ℓₒ)} ⦃ _ : Equiv(T₂) ⦄ (f : T₁ → T₂) : Set(ℓₗ Lvl.⊔ ℓₒ) where
  constructor congruence-inst

  field
    congruence : ∀{x y : T₁} → (x ≡ y) → (f(x) ≡ f(y))

[≡]-with : ∀{T₁} → ⦃ _ : Equiv(T₁) ⦄ → ∀{T₂} → ⦃ _ : Equiv(T₂) ⦄ → (f : T₁ → T₂) → ⦃ _ : Congruence(f) ⦄ → ∀{x y} → (x ≡ y) → (f(x) ≡ f(y))
[≡]-with f ⦃ inst ⦄ = Congruence.congruence {_}{_} {f} (inst)

-- The operator `_▫_` "(behaves like)/is a function" in the context of `_≡_` from the Equiv instance.
record Congruence2 {T₁ : Set(ℓₒ)} ⦃ _ : Equiv(T₁) ⦄ {T₂ : Set(ℓₒ)} ⦃ _ : Equiv(T₂) ⦄ {T₃ : Set(ℓₒ)} ⦃ _ : Equiv(T₃) ⦄ (_▫_ : T₁ → T₂ → T₃) : Set(ℓₗ Lvl.⊔ ℓₒ) where
  constructor congruence2-inst

  field
    congruence : ∀{x₁ y₁ : T₁} → (x₁ ≡ y₁) → ∀{x₂ y₂ : T₂} → (x₂ ≡ y₂) → (x₁ ▫ x₂ ≡ y₁ ▫ y₂)

  instance
    left : ∀{x} → Congruence(_▫ x)
    left = congruence-inst(proof ↦ congruence proof reflexivity)

  instance
    right : ∀{x} → Congruence(x ▫_)
    right = congruence-inst(proof ↦ congruence reflexivity proof)

instance
  [≡]-congruence2-left : ∀{T₁} → ⦃ _ : Equiv(T₁) ⦄ → ∀{T₂} → ⦃ _ : Equiv(T₂) ⦄ → ∀{T₃} → ⦃ _ : Equiv(T₃) ⦄ → (_▫_ : T₁ → T₂ → T₃) → ⦃ _ : Congruence2(_▫_) ⦄ → ∀{x} → Congruence(_▫ x)
  [≡]-congruence2-left (_▫_) ⦃ inst ⦄ = Congruence2.left {_}{_}{_} {_▫_} (inst)

instance
  [≡]-congruence2-right : ∀{T₁} → ⦃ _ : Equiv(T₁) ⦄ → ∀{T₂} → ⦃ _ : Equiv(T₂) ⦄ → ∀{T₃} → ⦃ _ : Equiv(T₃) ⦄ → (_▫_ : T₁ → T₂ → T₃) → ⦃ _ : Congruence2(_▫_) ⦄ → ∀{x} → Congruence(x ▫_)
  [≡]-congruence2-right (_▫_) ⦃ inst ⦄ = Congruence2.right {_}{_}{_} {_▫_} (inst)

-- A set and an equivalence relation on it
record Setoid : Set(Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)) where
  constructor setoid
  field
    Type : Set(ℓₒ)
    instance ⦃ Eq ⦄ : Equiv(Type)
