open import Logic
open import Type

module Structure.Sets.Quantifiers {ℓₑ ℓₛ ℓₗ}{E : Type{ℓₑ}}{S : Type{ℓₛ}} (_∈_ : E → S → Stmt{ℓₗ}) where

import      Lvl
open import Logic.Propositional
open import Logic.Predicate
open import Syntax.Function

private variable ℓ : Lvl.Level

-- Set restricted existential quantifier.
∃ₛ : S → (E → Stmt{ℓ}) → Stmt
∃ₛ(A) P = ∃(x ↦ (x ∈ A) ∧ P(x))

-- Set restricted universal quantifier.
∀ₛ : S → (E → Stmt{ℓ}) → Stmt
∀ₛ(A) P = ∀ₗ(x ↦ ((x ∈ A) → P(x)))
