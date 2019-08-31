module Structure.Relator.Function where

import      Lvl
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Functional
open import Relator.Equals.Uniqueness
open import Relator.Equals.Proofs
open import Type

module _ {ℓₒ₁ ℓₒ₂ ℓ} {A : Type{ℓₒ₁}}{B : Type{ℓₒ₂}} where
  -- A binary operation is total when every LHS have at least one RHS in which the relation holds.
  FunctionTotal : (A → B → Stmt{ℓ}) → Stmt
  FunctionTotal(φ) = (∀{x} → ∃(y ↦ φ(x)(y)))

  -- A binary operation is a function when every LHS have at least one RHS in which the relation holds.
  Function : (A → B → Stmt{ℓ}) → Stmt
  Function(φ) = (∀{x} → Unique(φ(x)))
  -- (∀{x}{y₁ y₂} → φ(x)(y₁) → φ(x)(y₂) → (y₁ ≡ y₂))
