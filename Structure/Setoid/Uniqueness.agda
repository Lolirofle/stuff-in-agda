module Structure.Setoid.Uniqueness where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.WithLvl
open import Type

private variable ℓₗ ℓₗ₁ ℓₗ₂ : Lvl.Level

module _ {ℓ₁}{ℓ₂} where
  -- Definition of uniqueness of a property.
  -- This means that there is at most one element that satisfies this property.
  -- This is similiar to "Injective" for functions.
  Unique : ∀{Obj : Type{ℓ₁}}{ℓₗ} → ⦃ equiv : Equiv{ℓₗ}(Obj) ⦄ → (Pred : Obj → Stmt{ℓ₂}) → Stmt
  Unique {Obj = Obj} Pred = ∀{x y : Obj} → Pred(x) → Pred(y) → (x ≡ y)

  -- Definition of existence of an unique element satisfying a property.
  -- This means that there is one and only one element that satisfies this property.
  ∃! : ∀{Obj : Type{ℓ₁}}{ℓₗ} → ⦃ equiv : Equiv{ℓₗ}(Obj) ⦄ → (Pred : Obj → Stmt{ℓ₂}) → Stmt
  ∃! {Obj} Pred = ∃(Pred) ∧ Unique(Pred)

  [∃!]-intro : ∀{T} → ⦃ _ : Equiv{ℓₗ}(T) ⦄ → ∀{property} → ∃(property) → Unique{T}(property) → ∃!(property)
  [∃!]-intro = [∧]-intro

  [∃!]-existence : ∀{Obj} → ⦃ _ : Equiv{ℓₗ}(Obj) ⦄ → ∀{Pred} → ∃!{Obj}(Pred) → ∃(Pred)
  [∃!]-existence  = [∧]-elimₗ

  [∃!]-uniqueness : ∀{Obj} → ⦃ _ : Equiv{ℓₗ}(Obj) ⦄ → ∀{Pred} → ∃!{Obj}(Pred) → Unique(Pred)
  [∃!]-uniqueness = [∧]-elimᵣ

  [∃!]-witness : ∀{Obj} → ⦃ _ : Equiv{ℓₗ}(Obj) ⦄ → ∀{Pred} → ∃!{Obj}(Pred) → Obj
  [∃!]-witness e = [∃]-witness ([∃!]-existence e)

  [∃!]-proof : ∀{Obj} → ⦃ _ : Equiv{ℓₗ}(Obj) ⦄ → ∀{Pred} → (e : ∃!{Obj}(Pred)) → Pred([∃!]-witness(e))
  [∃!]-proof e = [∃]-proof ([∃!]-existence e)

  [∃!]-existence-eq : ∀{T} → ⦃ _ : Equiv{ℓₗ}(T) ⦄ → ∀{P} → (e : ∃!(P)) → ∀{x} → P(x) → (x ≡ [∃!]-witness e)
  [∃!]-existence-eq e {x} px = [∃!]-uniqueness e {x} {[∃!]-witness e} px ([∃!]-proof e)

  [∃!]-existence-eq-any : ∀{T} → ⦃ _ : Equiv{ℓₗ}(T) ⦄ → ∀{P} → (e : ∃!(P)) → ∀{x} → P(x) → ([∃!]-witness e ≡ x)
  [∃!]-existence-eq-any e {x} px = [∃!]-uniqueness e {[∃!]-witness e} {x} ([∃!]-proof e) px

  -- TODO: [∃!]-equivalence {T} property = ∃(a ↦ ∃{property(a)}(pa ↦ pa ∧ Uniqueness{T}(property){a}(pa)))
