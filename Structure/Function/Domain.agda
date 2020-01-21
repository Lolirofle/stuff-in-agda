module Structure.Function.Domain where

import      Lvl
open import Functional
import      Functional.Names as Names
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid hiding (Function)
open import Type

-- TODO: Merge with the one in Sets.Setoid
module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (f : A → B) where
  record Function : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field proof : Names.Function(f)
  function = inst-fn Function.proof

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (f : A → B) where
  record Injective : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field proof : Names.Injective(f)
  injective = inst-fn Injective.proof

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (f : A → B) where
  record Surjective : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field proof : Names.Surjective(f)
  surjective = inst-fn Surjective.proof

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (f : A → B) where
  record Bijective : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field proof : Names.Bijective(f)
  bijective = inst-fn Bijective.proof

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} ⦃ _ : Equiv(A) ⦄ {B : Type{ℓₒ₂}} (f : A → B) where
  module _ (f⁻¹ : B → A) where
    record Inverseₗ : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
      constructor intro
      field proof : Names.Inverses(f⁻¹)(f)
    inverseₗ = inst-fn Inverseₗ.proof

  Invertibleₗ = ∃(Inverseₗ)

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (f : A → B) where
  module _ (f⁻¹ : B → A) where
    record Inverseᵣ : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
      constructor intro
      field proof : Names.Inverses(f)(f⁻¹)
    inverseᵣ = inst-fn Inverseᵣ.proof

  Invertibleᵣ = ∃(Inverseᵣ)

module _ {ℓₒ₁}{ℓₒ₂} {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv(B) ⦄ (f : A → B) where
  record Constant : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    constructor intro
    field proof : Names.Constant(f)
  constant = inst-fn Constant.proof

module _ {ℓₒ} {A : Type{ℓₒ}} ⦃ _ : Equiv(A) ⦄ (f : A → A) where
  module _ (x : A) where
    record Fixpoint : Stmt{ℓₒ} where
      constructor intro
      field proof : Names.Fixpoint f(x)
    fixpoint = inst-fn Fixpoint.proof

  record Involution : Stmt{ℓₒ} where
    constructor intro
    field proof : Names.Involution(f)
  involution = inst-fn Involution.proof

  record Idempotent : Stmt{ℓₒ} where
    constructor intro
    field proof : Names.Idempotent(f)
  idempotent = inst-fn Idempotent.proof

{-
module _ {ℓ₂ ℓ₃} where
  -- Definition of injectivity for a function
  Injective : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → Stmt{ℓ₂ Lvl.⊔ ℓ₃}
  Injective {X} f = ∀{x₁ x₂ : X} → (f(x₁) ≡ f(x₂)) → (x₁ ≡ x₂)

module _ {ℓ₂ ℓ₃} where
  -- Definition of surjectivity for a function (TODO: Different levels would be okay if the existential allowed it)
  Surjective : ∀{X : Type{ℓ₂ Lvl.⊔ ℓ₃}}{Y : Type{ℓ₂}} → (X → Y) → Stmt{ℓ₂ Lvl.⊔ ℓ₃}
  Surjective {X}{Y} f = ∀{y : Y} → ∃{Obj = X}(x ↦ (f(x) ≡ y))

  -- Definition of bijectivity for a function
  Bijective : ∀{X : Type{ℓ₂ Lvl.⊔ ℓ₃}}{Y : Type{ℓ₂}} → (X → Y) → Stmt{ℓ₂ Lvl.⊔ ℓ₃}
  Bijective f = (Injective f) ∧ (Surjective f)

module _ {ℓ₂ ℓ₃} where
  -- Definition of a left inverse function for a function
  Inverseₗ : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → (Y → X) → Stmt{ℓ₂ Lvl.⊔ ℓ₃}
  Inverseₗ f f⁻¹ = (∀{x}{y} → (f(x) ≡ y) ← (x ≡ f⁻¹(y)))

  -- Definition of a right inverse function for a function
  Inverseᵣ : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → (Y → X) → Stmt{ℓ₂ Lvl.⊔ ℓ₃}
  Inverseᵣ f f⁻¹ = (∀{x}{y} → (f(x) ≡ y) → (x ≡ f⁻¹(y)))

  -- Definition of an inverse function for a function
  Inverse : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → (Y → X) → Stmt{ℓ₂ Lvl.⊔ ℓ₃}
  Inverse f f⁻¹ = (∀{x}{y} → (f(x) ≡ y) ↔ (x ≡ f⁻¹(y)))

  Invertible : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → Stmt{ℓ₂ Lvl.⊔ ℓ₃}
  Invertible f = ∃(Inverse f)

  -- Definition of an left inverse for a function
  InverseIdₗ : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → (Y → X) → Stmt{ℓ₂}
  InverseIdₗ f f⁻¹ = (∀{x} → (f⁻¹ ∘ f)(x) ≡ x) -- TODO: Prove equivalence of this and above

  -- Definition of a right inverse for a function
  InverseIdᵣ : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₃}} → (X → Y) → (Y → X) → Stmt{ℓ₃}
  InverseIdᵣ f f⁻¹ = (∀{x} → (f ∘ f⁻¹)(x) ≡ x)

module _ {ℓ₂} where
  -- Definition of a fixed point for a function
  FixPoint : ∀{T : Type{ℓ₂}} → (T → T) → T → Stmt{ℓ₂}
  FixPoint f(x) = (f(x) ≡ x)

  -- Definition of a function with itself as its inverse (inverse function of function composition (∘))
  Involution : ∀{X : Type{ℓ₂}} → (X → X) → Stmt{ℓ₂}
  Involution f = (∀{x} → (f ∘ f)(x) ≡ x)

  -- Definition of a constant function
  Constant : ∀{X : Type{ℓ₂}}{Y : Type{ℓ₂}} → (X → Y) → Stmt{ℓ₂}
  Constant f = (∃(y ↦ ∀{x} → f(x) ≡ y))

  -- Definition of the relation between a function and an operation that says:
  -- The function preserves the operation.
  -- This is a special case of the (_preserves_)-relation that has the same operator inside and outside.
  -- Special cases:
  --   Additive function (Operator is a conventional _+_)
  --   Multiplicative function (Operator is a conventional _*_)
  _preserves_ : ∀{T : Type{ℓ₂}} → (T → T) → (T → T → T) → Stmt{ℓ₂}
  _preserves_ (f)(_▫_) = (∀{x y} → (f(x ▫ y) ≡ f(x) ▫ f(y)))
-}
