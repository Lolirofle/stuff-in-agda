module Structure.Function.Ordering where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Type

module _ {ℓₒ₁ ℓₒ₂ ℓₗ₁ ℓₗ₂} {T₁ : Type{ℓₒ₁}} {T₂ : Type{ℓₒ₂}} (_≤₁_ : T₁ → T₁ → Type{ℓₗ₁}) (_≤₂_ : T₂ → T₂ → Type{ℓₗ₂}) where
  record Increasing (f : T₁ → T₂) : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field proof : ∀{a b : T₁} → (a ≤₁ b) → (f(a) ≤₂ f(b))

  record Decreasing (f : T₁ → T₂) : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field proof : ∀{a b : T₁} → (a ≤₁ b) → (f(b) ≤₂ f(a))

  Monotone : (T₁ → T₂) → Stmt
  Monotone(f) = (Increasing(f) ∨ Decreasing(f))

  record UpperBoundPointOf (f : T₁ → T₂) (p : T₁) : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field proof : ∀{x} → (f(x) ≤₂ f(p))

  UpperBounded : (T₁ → T₂) → Stmt
  UpperBounded(f) = ∃(UpperBoundPointOf(f))

  record LowerBoundPointOf (f : T₁ → T₂) (p : T₁) : Stmt{ℓₒ₁ Lvl.⊔ ℓₗ₂} where
    constructor intro
    field proof : ∀{x} → (f(p) ≤₂ f(x))

  LowerBounded : (T₁ → T₂) → Stmt
  LowerBounded(f) = ∃(LowerBoundPointOf(f))
