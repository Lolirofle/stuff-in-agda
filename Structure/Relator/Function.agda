module Structure.Relator.Function {ℓₗ} where

import      Lvl
open import Logic.Propositional
open import Logic.Predicate{ℓₗ}
open import Functional
open import Relator.Equals.Uniqueness{ℓₗ}
open import Relator.Equals.Proofs{ℓₗ}
open import Type

module _ {ℓₒ₁ ℓₒ₂} where
  -- A binary operation is total when every LHS have at least one RHS in which the relation holds.
  FunctionTotal : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} → (A → B → Stmt) → Stmt
  FunctionTotal{A}{B} (φ) = (∀{x} → ∃(y ↦ φ(x)(y)))

  -- A binary operation is a function when every LHS have at least one RHS in which the relation holds.
  Function : ∀{A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} → (A → B → Stmt{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂}) → Stmt
  Function{A}{B} (φ) = (∀{x} → Unique{ℓₒ₂}{ℓₒ₁} (φ(x)))
  -- (∀{x}{y₁ y₂} → φ(x)(y₁) → φ(x)(y₂) → (y₁ ≡ y₂))
