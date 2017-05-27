module Structure.Function.Domain {l₁} where

import      Level as Lvl
open import Functional
open import Logic.Propositional
open import Logic.Predicate{l₁}
open import Relator.Equals{l₁}
open import Type

-- Definition of injectivity for a function
Injective : ∀{l₂ l₃}{X : Type{l₂}}{Y : Type{l₃}} → (X → Y) → Stmt{l₁ Lvl.⊔ l₂ Lvl.⊔ l₃}
Injective {_}{_} {X} f = ∀{x₁ x₂ : X} → (f(x₁) ≡ f(x₂)) → (x₁ ≡ x₂)

-- Definition of surjectivity for a function
Surjective : ∀{l₂}{X : Type{l₂}}{Y : Type{l₂}} → (X → Y) → Stmt{l₁ Lvl.⊔ l₂}
Surjective {_} {X}{Y} f = ∀{y : Y} → ∃{_}{X}(x ↦ (f(x) ≡ y))

-- Definition of bijectivity for a function
Bijective : ∀{l₂}{X Y : Type{l₂}} → (X → Y) → Stmt{l₁ Lvl.⊔ l₂}
Bijective f = (Injective f) ∧ (Surjective f)

-- Definition of a fixed point for a function
FixPoint : ∀{l₂}{T : Type{l₂}} → (T → T) → T → Stmt{l₁ Lvl.⊔ l₂}
FixPoint f(x) = (f(x) ≡ x)

-- Definition of an inverse function for a function
Inverse : ∀{l₂ l₃}{X : Type{l₂}}{Y : Type{l₃}} → (X → Y) → (Y → X) → Stmt{l₁ Lvl.⊔ l₂ Lvl.⊔ l₃}
Inverse f f⁻¹ = (∀{x}{y} → (f(x) ≡ y) → (f⁻¹(y) ≡ x))

-- Definition of an inverse function for a function
InverseId : ∀{l₂}{X : Type{l₂}}{Y : Type{l₂}} → (X → Y) → (Y → X) → Stmt{l₁ Lvl.⊔ l₂}
InverseId f f⁻¹ = ((f ∘ f⁻¹) ≡ id) -- TODO: Prove equivalence of this and above

-- Definition of an constant function
Constant : ∀{l₂}{X : Type{l₂}}{Y : Type{l₂}} → (X → Y) → Stmt{l₁ Lvl.⊔ l₂}
Constant f = (∃(y ↦ ∀{x} → f(x) ≡ y))
