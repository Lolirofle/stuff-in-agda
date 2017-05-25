import Level as Lvl
module Structure.Function.Domain {l₁ : Lvl.Level} where

open import Functional
open import Type

module _ {l₂}{T : Type{l₂}} where
  open import Logic.Propositional{l₁ Lvl.⊔ l₂}
  open import Logic.Predicate{l₁}{l₂}
  open import Relator.Equals{l₁}{l₂}

  -- Definition of a fixed point for a function
  FixPoint : ∀{T : Type{l₂}} → (T → T) → T → Stmt
  FixPoint f(x) = (f(x) ≡ x)

module _ {l₂}{l₃}{X : Type{l₂}}{Y : Type{l₂ Lvl.⊔ l₃}} where
  open import Logic.Propositional{l₁ Lvl.⊔ l₂ Lvl.⊔ l₃}
  open import Logic.Predicate{l₁}{l₂ Lvl.⊔ l₃}
  open import Relator.Equals{l₁}

  private _≡₂_ = _≡_{l₂}
  private _≡₃_ = _≡_{l₂ Lvl.⊔ l₃}

  -- Definition of injectivity for a function
  Injective : (X → Y) → Stmt
  Injective f = ∀{x₁ x₂ : X} → (f(x₁) ≡₃ f(x₂)) → (x₁ ≡₂ x₂)

  -- Definition of surjectivity for a function
  Surjective : (X → Y) → Stmt
  Surjective f = ∀{y : Y} → ∃(\(x : X) → (f(x) ≡₃ y))

  -- Definition of bijectivity for a function
  Bijective : (X → Y) → Stmt
  Bijective f = (Injective f) ∧ (Surjective f)

  -- Definition of an inverse function for a function
  Inverse : (X → Y) → (Y → X) → Stmt
  Inverse f f⁻¹ = (∀{x}{y} → (f(x) ≡ y) → (f⁻¹(y) ≡ x))

  -- Definition of an inverse function for a function
  InverseId : (X → Y) → (Y → X) → Stmt
  InverseId f f⁻¹ = ((f ∘ f⁻¹) ≡ id) -- TODO: Prove equivalence of this and above

  -- Definition of an constant function
  Constant : (X → Y) → Stmt{l₂ Lvl.⊔ l₃}
  Constant f = (∃{Y}(y ↦ ∀{x : X} → f(x) ≡ y))
