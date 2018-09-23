open import Logic.Classical.NaturalDeduction

module Logic.Classical.SetTheory.BoundedQuantification {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} {Proof} ⦃ predicateEqTheory : PredicateEq.Theory{ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) ⦄ (_∈_ : Domain → Domain → Stmt) where

open import Functional hiding (Domain)
open import Lang.Instance
import      Lvl
open        Logic.Classical.NaturalDeduction.PredicateEq {ℓₗ}{ℓₒ}{ℓₘₗ}{ℓₘₒ} {Stmt} {Domain} (Proof) renaming (Theory to PredicateEqTheory)

open        PredicateEqTheory (predicateEqTheory)

-- Bounded universal quantifier
∀ₛ : Domain → (Domain → Stmt) → Stmt
∀ₛ(S)(φ) = ∀ₗ(x ↦ (x ∈ S) ⟶ φ(x))

-- Bounded existential quantifier
∃ₛ : Domain → (Domain → Stmt) → Stmt
∃ₛ(S)(φ) = ∃ₗ(x ↦ (x ∈ S) ∧ φ(x))
