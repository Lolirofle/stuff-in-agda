module Formalization.ClassicalPropositionalLogic.Semantics where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Stmt
open import Formalization.ClassicalPropositionalLogic.Syntax
open import Functional
open import Logic
import      Logic.Propositional as Logic
import      Logic.Predicate     as Logic
import      Sets.PredicateSet
open        Sets.PredicateSet.BoundedQuantifiers
open import Type

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level

module _ where
  private variable P : Type{ℓₚ}

  -- Model.
  -- A model decides which propositional constants that are true or false.
  Model : Type{ℓₚ} → Type{ℓₚ}
  Model(P) = (P → Bool)

  -- Satisfication relation.
  -- (𝔐 ⊧ φ) means that the formula φ is satisfied in the model 𝔐.
  -- Or in other words: A formula is true in the model 𝔐.
  _⊧_ : Model(P) → Formula(P) → Stmt
  𝔐 ⊧ (• p)   = IsTrue(𝔐(p))   -- A model decides whether a propositional constant is satisifed.
  𝔐 ⊧ ⊤       = Logic.⊤        -- Any model satisfies top.
  𝔐 ⊧ ⊥       = Logic.⊥        -- No model satisfies bottom.
  𝔐 ⊧ (¬ φ)   = Logic.¬(𝔐 ⊧ φ) -- A model satisfies a negated proposition when it does not satisfy the proposition.
  𝔐 ⊧ (φ ∧ ψ) = (𝔐 ⊧ φ) Logic.∧ (𝔐 ⊧ ψ) -- A model satisfies a conjunction when it satisfies both of the propositions.
  𝔐 ⊧ (φ ∨ ψ) = (𝔐 ⊧ φ) Logic.∨ (𝔐 ⊧ ψ) -- A model satisfies a disjunction when it satisfies any one of the propositions.
  𝔐 ⊧ (φ ⟶ ψ) = Logic.¬(𝔐 ⊧ φ) Logic.∨ (𝔐 ⊧ ψ)
  𝔐 ⊧ (φ ⟷ ψ) = ((𝔐 ⊧ φ) Logic.∧ (𝔐 ⊧ ψ)) Logic.∨ (Logic.¬(𝔐 ⊧ φ) Logic.∧ Logic.¬(𝔐 ⊧ ψ))

  -- Satisfication of a set of formulas.
  -- This means that a model satisfies all formulas at the same time.
  _⊧₊_ : Model(P) → Formulas(P){ℓ} → Stmt
  𝔐 ⊧₊ Γ = ∀ₛ(Γ) (𝔐 ⊧_)

  -- Validity of a formula.
  -- A formula is valid when it is true independent of any model.
  Valid : Formula(P) → Stmt
  Valid(φ) = Logic.∀ₗ(_⊧ φ)

  -- Satisfiability of sets of formulas.
  -- A set of formulas is valid when there is a model that satisfies all of them at the same time.
  Satisfiable : Formulas(P){ℓ} → Stmt
  Satisfiable(Γ) = Logic.∃(_⊧₊ Γ)

  -- Unsatisfiability of sets of formulas.
  Unsatisfiable : Formulas(P){ℓ} → Stmt
  Unsatisfiable{ℓ} = Logic.¬_ ∘ Satisfiable{ℓ}

  -- Semantic entailment of a formula.
  -- A hypothetical statement. If a model would satisfy all formulas in Γ, then this same model satisifes the formula φ.
  _⊨_ : Formulas(P){ℓ} → Formula(P) → Stmt
  Γ ⊨ φ = ∀{𝔐} → (𝔐 ⊧₊ Γ) → (𝔐 ⊧ φ)

  _⊭_ : Formulas(P){ℓ} → Formula(P) → Stmt
  _⊭_ = Logic.¬_ ∘₂ _⊨_

  -- Axiomatization of a theory by a set of axioms.
  -- A set of axioms is a set of formulas.
  -- A theory is the closure of a set of axioms.
  -- An axiomatization is a subset of formulas of the theory which entails all formulas in the axiomatized theory.
  _axiomatizes_ : Formulas(P){ℓ₁} → Formulas(P){ℓ₂} → Stmt
  Γ₁ axiomatizes Γ₂ = ∀{φ} → (Γ₁ ⊨ φ) → Γ₂(φ)

  -- A set of formulas is closed when it includes all formulas that it entails.
  Closed : Formulas(P){ℓ} → Stmt
  Closed(Γ) = Γ axiomatizes Γ
