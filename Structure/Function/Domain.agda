module Structure.Function.Domain where

import      Lvl
open import Functional
import      Function.Names as Names
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid.WithLvl hiding (Function)
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

module _ {A : Type{ℓₒ₁}} ⦃ _ : Equiv{ℓₗ₁}(A) ⦄ {B : Type{ℓₒ₂}} (f : A → B) where
  module _ (f⁻¹ : B → A) where
    record Inverseₗ : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₁} where
      constructor intro
      field proof : Names.Inverses(f⁻¹)(f)
    inverseₗ = inst-fn Inverseₗ.proof

  Invertibleₗ = ∃(Inverseₗ)

module _ {A : Type{ℓₒ₁}} {B : Type{ℓₒ₂}} ⦃ _ : Equiv{ℓₗ₂}(B) ⦄ (f : A → B) where
  module _ (f⁻¹ : B → A) where
    record Inverseᵣ : Stmt{ℓₒ₂ Lvl.⊔ ℓₗ₂} where
      constructor intro
      field proof : Names.Inverses(f)(f⁻¹)
    inverseᵣ = inst-fn Inverseᵣ.proof

  Invertibleᵣ = ∃(Inverseᵣ)

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
