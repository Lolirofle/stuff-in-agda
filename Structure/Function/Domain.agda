module Structure.Function.Domain {ℓ₁} where -- TODO: Parameterize (_≡_ : ₎and comment out import of Relator.Equals

import      Lvl
open import Functional
open import Logic.Propositional
open import Logic.Predicate{ℓ₁}
import      Relator.Equals
open import Type

module _ {ℓ₂ ℓ₃} where
  open Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}

  -- Definition of injectivity for a function
  Injective : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
  Injective {X} f = ∀{x₁ x₂ : X} → (f(x₁) ≡ f(x₂)) → (x₁ ≡ x₂)

module _ {ℓ₂} where
  open Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}

  -- Definition of surjectivity for a function (TODO: Different levels would be okay if the existential allowed it)
  Surjective : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₂}} → (X → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  Surjective {X}{Y} f = ∀{y : Y} → ∃{_}{X}(x ↦ (f(x) ≡ y))

  -- Definition of bijectivity for a function
  Bijective : ∀{X Y : Type{ℓ₂}} → (X → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  Bijective f = (Injective f) ∧ (Surjective f)

  -- Definition of a fixed point for a function
  FixPoint : ∀{T : Type{ℓ₂}} → (T → T) → T → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  FixPoint f(x) = (f(x) ≡ x)

module _ {ℓ₂ ℓ₃} where
  open Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}

  -- Definition of an inverse function for a function
  Inverse : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → (Y → X) → Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
  Inverse f f⁻¹ = (∀{x}{y} → (f(x) ≡ y) → (f⁻¹(y) ≡ x))

  Invertible : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
  Invertible f = ∃(Inverse f)

  -- Definition of the relation between a function and an operation that says:
  -- The function preserves the operation.
  -- Also called: Homomorphism
  Preserving : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → (X → X) → (Y → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂ Lvl.⊔ ℓ₃}
  Preserving {X}{Y} (f)(x)(y) = (∀{a : X} → (f(x(a)) ≡ y(f(a)))) -- TODO: Is it possible to make this more general? So that multiple function applications are allowed?
  -- ∀{a : X} → ((f ∘ x)(a) ≡ (y ∘ f)(a))

module _ {ℓ₂} where
  open Relator.Equals{ℓ₁ Lvl.⊔ ℓ₂}{ℓ₂}

  -- Definition of an inverse function for a function
  InverseId : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₂}} → (X → Y) → (Y → X) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  InverseId f f⁻¹ = ((f ∘ f⁻¹) ≡ id) -- TODO: Prove equivalence of this and above

  -- Definition of a constant function
  Constant : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₂}} → (X → Y) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  Constant f = (∃(y ↦ ∀{x} → f(x) ≡ y))

  -- Definition of the relation between a function and an operation that says:
  -- The function preserves the operation.
  -- This is a special case of the (_preserves_)-relation that has the same operator inside and outside.
  -- Special cases:
  --   Additive function (Operator is a conventional _+_)
  --   Multiplicative function (Operator is a conventional _*_)
  _preserves_ : ∀{T : Type{ℓ₂}} → (T → T) → (T → T → T) → Stmt{ℓ₁ Lvl.⊔ ℓ₂}
  _preserves_ (f)(_▫_) = (∀{x y} → (f(x ▫ y) ≡ f(x) ▫ f(y)))
