module Structure.Function.Domain where

import      Lvl
open import Functional
import      Structure.Function.Names as Names
open import Structure.Function
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid
open import Type

private variable ℓₒ ℓₒ₁ ℓₒ₂ ℓₗ ℓₗ₁ ℓₗ₂ : Lvl.Level

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (f : A → B) where
  record Injective : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field proof : Names.Injective(f)
  injective = inst-fn Injective.proof

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (f : A → B) where
  record Surjective : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field proof : Names.Surjective(f)
  surjective = inst-fn Surjective.proof

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (f : A → B) where
  record Bijective : Stmt{ℓₒ₁ Lvl.⊔ ℓₒ₂ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field proof : Names.Bijective(f)
  bijective = inst-fn Bijective.proof

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (f : A → B) where
  module _ (f⁻¹ : B → A) where
    record Inverseᵣ : Stmt{ℓₒ₂ Lvl.⊔ ℓₗ₂} where
      constructor intro
      field proof : Names.Inverses(f)(f⁻¹)
    inverseᵣ = inst-fn Inverseᵣ.proof

  module _ ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ where
    Invertibleᵣ = ∃(f⁻¹ ↦ Function(f⁻¹) ∧ Inverseᵣ(f⁻¹))

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} (f : A → B) where
  module _ (f⁻¹ : B → A) where
    Inverseₗ : Stmt
    Inverseₗ = Inverseᵣ(f⁻¹)(f)
    module Inverseₗ(inverseₗ) = Inverseᵣ{f = f⁻¹}{f⁻¹ = f}(inverseₗ)
    inverseₗ : ⦃ inverseₗ : Inverseₗ ⦄ → Names.Inverses(f⁻¹)(f)
    inverseₗ = inst-fn Inverseₗ.proof

  module _ ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ where
    Invertibleₗ = ∃(f⁻¹ ↦ Function(f⁻¹) ∧ Inverseₗ(f⁻¹))

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (f : A → B) where
  module _ (f⁻¹ : B → A) where
    Inverse = Inverseₗ(f)(f⁻¹) ∧ Inverseᵣ(f)(f⁻¹)
    inverse-left : ⦃ inverse : Inverse ⦄ → Names.Inverses(f⁻¹)(f)
    inverse-left = inst-fn(Inverseₗ.proof ∘ [∧]-elimₗ)
    inverse-right : ⦃ inverse : Inverse ⦄ → Names.Inverses(f)(f⁻¹)
    inverse-right = inst-fn(Inverseᵣ.proof ∘ [∧]-elimᵣ)

  Invertible = ∃(f⁻¹ ↦ Function(f⁻¹) ∧ Inverse(f⁻¹))

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (([↔]-intro ba ab) : A ↔ B) where
  record InversePair : Type{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    l = ba
    r = ab
    field
      ⦃ left ⦄ : Inverseₗ(l)(r)
      ⦃ right ⦄ : Inverseᵣ(l)(r)

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (f : A → B) where
  record Constant : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field proof : Names.Constant(f)
  constant = inst-fn Constant.proof

module _ {A : Type{ℓₒ}} ⦃ _ : Equiv{ℓₗ}(A) ⦄ (f : A → A) where
  module _ (x : A) where
    record Fixpoint : Stmt{ℓₗ} where
      constructor intro
      field proof : Names.Fixpoint f(x)
    fixpoint = inst-fn Fixpoint.proof

  record Involution : Stmt{ℓₒ Lvl.⊔ ℓₗ} where
    constructor intro
    field proof : Names.Involution(f)
  involution = inst-fn Involution.proof

  record Idempotent : Stmt{ℓₒ Lvl.⊔ ℓₗ} where
    constructor intro
    field proof : Names.Idempotent(f)
  idempotent = inst-fn Idempotent.proof
