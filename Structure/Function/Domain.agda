module Structure.Function.Domain {ℓ₁} where

import      Level as Lvl
open import Functional
open import Logic.Propositional
open import Logic.Predicate{ℓ₁}
open import Relator.Equals{ℓ₁}
open import Type

-- Definition of injectivity for a function
Injective : ∀{ℓ₂ ℓ₃}{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
Injective {_}{_} {X} f = ∀{x₁ x₂ : X} → (f(x₁) ≡ f(x₂)) → (x₁ ≡ x₂)

-- Definition of surjectivity for a function
Surjective : ∀{ℓ₂}{X : Type{ℓ₂}}{Y : Type{ℓ₂}} → (X → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
Surjective {_} {X}{Y} f = ∀{y : Y} → ∃{_}{X}(x ↦ (f(x) ≡ y))

-- Definition of bijectivity for a function
Bijective : ∀{ℓ₂}{X Y : Type{ℓ₂}} → (X → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
Bijective f = (Injective f) ∧ (Surjective f)

-- Definition of a fixed point for a function
FixPoint : ∀{ℓ₂}{T : Type{ℓ₂}} → (T → T) → T → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
FixPoint f(x) = (f(x) ≡ x)

-- Definition of an inverse function for a function
Inverse : ∀{ℓ₂ ℓ₃}{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → (Y → X) → Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
Inverse f f⁻¹ = (∀{x}{y} → (f(x) ≡ y) → (f⁻¹(y) ≡ x))

-- Definition of an inverse function for a function
InverseId : ∀{ℓ₂}{X : Type{ℓ₂}}{Y : Type{ℓ₂}} → (X → Y) → (Y → X) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
InverseId f f⁻¹ = ((f ∘ f⁻¹) ≡ id) -- TODO: Prove equivalence of this and above

-- Definition of a constant function
Constant : ∀{ℓ₂}{X : Type{ℓ₂}}{Y : Type{ℓ₂}} → (X → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
Constant f = (∃(y ↦ ∀{x} → f(x) ≡ y))

-- Definition of the relation between a function and an operation that says:
-- The function preserves the operation
-- Special cases:
--   Additive function (Operator is a conventional _+_)
--   Multiplicative function (Operator is a conventional _*_)
_preserves_ : ∀{ℓ₂}{T : Type{ℓ₂}} → (T → T) → (T → T → T) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
_preserves_ (f)(_▫_) = (∀{x y} → (f(x ▫ y) ≡ f(x) ▫ f(y)))
