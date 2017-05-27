import      Level as Lvl
open import Logic.Propositional
open import Type
module Functional.Equals {lvll} (_≡ᵥ_ : ∀{lvl}{T : Type{lvl}} → T → T → Stmt{lvll Lvl.⊔ lvl}) where

infixl 15 _≡_
data _≡_ {lvl₁}{lvl₂}{A : Type{lvl₁}} {B : Type{lvl₂}} : (A → B) → (A → B) → Stmt{lvll Lvl.⊔ lvl₁ Lvl.⊔ lvl₂} where
  instance [≡]-intro : ∀{f₁ f₂} → (∀{x} → (f₁(x) ≡ᵥ f₂(x))) → (f₁ ≡ f₂)

-- TODO: Almost certainly wrong
-- [≡]-inherit-property : ∀{lvl₁}{lvl₂} → (∀{X : Type{lvl₂}}{Y : Type{lvl₂}} {a₁ b₁ : X}{a₂ b₂ : Y} → (a₁ ≡ᵥ b₁) → (a₂ ≡ᵥ b₂)) → (∀{X₁ X₂ : Type{lvl₁}}{Y₁ Y₂ : Type{lvl₂}}{f₁ g₁ : X₁ → Y₁}{f₂ g₂ : X₂ → Y₂} → (f₁ ≡ g₁) → (f₂ ≡ g₂))
-- [≡]-inherit-property(prop) {X₁}{X₂} {Y₁}{Y₂} {f₁}{g₁} {f₂}{g₂} =
--   [≡]-intro{_}{_} {_}{_} (\{x} → prop{_}{_} {f₁(x)}{g₁(x)} {f₂(x)}{g₂(x)})
-- P : ∀{X Y} → (X , X) → (Y , Y)
