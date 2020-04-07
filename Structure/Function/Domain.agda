module Structure.Function.Domain where

import      Lvl
open import Functional
import      Function.Names as Names
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid hiding (Function)
open import Type

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
