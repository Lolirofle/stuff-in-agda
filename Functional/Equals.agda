import      Level as Lvl
open import Logic.Propositional
open import Type
module Functional.Equals {ℓl} (_≡ᵥ_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Stmt{ℓl Lvl.⊔ ℓ}) where

infixl 15 _≡_
data _≡_ {ℓ₁}{ℓ₂}{A : Type{ℓ₁}} {B : Type{ℓ₂}} : (A → B) → (A → B) → Stmt{ℓl Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
  instance [≡]-intro : ∀{f₁ f₂} → (∀{x} → (f₁(x) ≡ᵥ f₂(x))) → (f₁ ≡ f₂)

-- TODO: Almost certainly wrong
-- [≡]-inherit-property : ∀{ℓ₁}{ℓ₂} → (∀{X : Type{ℓ₂}}{Y : Type{ℓ₂}} {a₁ b₁ : X}{a₂ b₂ : Y} → (a₁ ≡ᵥ b₁) → (a₂ ≡ᵥ b₂)) → (∀{X₁ X₂ : Type{ℓ₁}}{Y₁ Y₂ : Type{ℓ₂}}{f₁ g₁ : X₁ → Y₁}{f₂ g₂ : X₂ → Y₂} → (f₁ ≡ g₁) → (f₂ ≡ g₂))
-- [≡]-inherit-property(prop) {X₁}{X₂} {Y₁}{Y₂} {f₁}{g₁} {f₂}{g₂} =
--   [≡]-intro{_}{_} {_}{_} (\{x} → prop{_}{_} {f₁(x)}{g₁(x)} {f₂(x)}{g₂(x)})
-- P : ∀{X Y} → (X , X) → (Y , Y)
