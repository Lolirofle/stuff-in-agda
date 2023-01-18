open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Classical.Semantics.Satisfaction (𝔏 : Signature) {ℓₘ} where
open Signature(𝔏)

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.ListSized
import      Data.ListSized.Functions as List
open import Formalization.PredicateLogic.Classical.Semantics(𝔏){ℓₘ}
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Functional using (_∘_ ; _∘₂_)
import      Logic.Propositional as Logic
import      Logic.Predicate     as Logic
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Natural
open import Relator.Equals
open import Sets.PredicateSet using (PredSet)
open        Sets.PredicateSet.BoundedQuantifiers
open import Syntax.Function
open import Type.Dependent.Sigma renaming (intro to _,_)
open import Type.Properties.Decidable
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable P : Type{ℓₚ}
private variable args n vars : ℕ
private variable 𝔐 : Model

-- A `VarMapping(vars)(𝔐)` maps `vars` number of variables to objects in the domain of the model `𝔐`.
-- Also called: Variable assignment.
VarMapping : ℕ → Model → Type
VarMapping(vars)(𝔐) = 𝕟(vars) → Model.Domain(𝔐)
module VarMapping where
  -- Adds a mapping to an object in the domain of the model `𝔐`.
  add0 : VarMapping(vars)(𝔐) → Model.Domain(𝔐) → VarMapping(𝐒(vars))(𝔐)
  add0 𝔰 t 𝟎      = t
  add0 𝔰 t (𝐒(v)) = 𝔰(v)

private variable 𝔰 : VarMapping(vars)(𝔐)

module _ ((𝔐 , 𝔰) : Σ Model (VarMapping(vars))) where
  -- Maps terms to objects in the domain given a model and a variable mapping.
  val : Term(vars) → Model.Domain(𝔐)
  val₊ : List(Term(vars))(n) → List(Model.Domain(𝔐))(n)

  val(var v)    = 𝔰(v)
  val(func f x) = Model.function 𝔐 f (val₊ x)
  val₊ {0}       ∅       = ∅
  val₊ {𝐒(n)} (t ⊰ ts) = (val t ⊰ val₊ {n} ts)
  --val₊ = List.map val

-- Satisfication relation.
-- ((𝔐 , 𝔰) ⊧ φ) means that the formula φ is satisfied in the model 𝔐 with the variable mapping.
-- Or in other words: A formula is true in the model 𝔐.
_⊧_ : (Σ Model (VarMapping(vars))) → Formula(vars) → Type{ℓₘ}
(𝔐 , 𝔰) ⊧ (f $ x)  = Lvl.Up(IsTrue(Model.relation 𝔐 f (val₊(𝔐 , 𝔰) x)))  -- A model decides whether a relation is satisfied.
(𝔐 , 𝔰) ⊧ ⊤        = Unit                                                 -- All models satisfy top.
(𝔐 , 𝔰) ⊧ ⊥        = Empty                                                -- No model satisfies bottom.
(𝔐 , 𝔰) ⊧ (φ ∧ ψ)  = ((𝔐 , 𝔰) ⊧ φ) Logic.∧ ((𝔐 , 𝔰) ⊧ ψ)                  -- A model satisfies a conjunction when it satisfies both of the propositions.
(𝔐 , 𝔰) ⊧ (φ ∨ ψ)  = ((𝔐 , 𝔰) ⊧ φ) Logic.∨ ((𝔐 , 𝔰) ⊧ ψ)                  -- A model satisfies a disjunction when it satisfies any one of the propositions.
(𝔐 , 𝔰) ⊧ (φ ⟶ ψ)  = Logic.¬((𝔐 , 𝔰) ⊧ φ) Logic.∨ ((𝔐 , 𝔰) ⊧ ψ)
(𝔐 , 𝔰) ⊧ (Ɐ φ)    = Logic.∀ₗ(t ↦ (𝔐 , VarMapping.add0{𝔐 = 𝔐} 𝔰 t) ⊧ φ)
(𝔐 , 𝔰) ⊧ (∃ φ)    = Logic.∃(t ↦ (𝔐 , VarMapping.add0{𝔐 = 𝔐} 𝔰 t) ⊧ φ)

-- Satisfication of a set of formulas.
-- This means that a model satisfies all formulas at the same time.
_⊧₊_ : (Σ Model (VarMapping(vars))) → PredSet{ℓ}(Formula(vars)) → Type
𝔐 ⊧₊ Γ = ∀ₛ(Γ) (𝔐 ⊧_)

-- Validity of a formula.
-- A formula is valid when it is true independent of any model (is satisfied by all models).
-- Examples:
--   Valid(⊤)
--   Valid(⊥ ⟶ ⊥)
--   ¬ Valid(⊥)
--   ¬ Valid(P) where P : Prop(0)
Valid : Formula(vars) → Type
Valid(φ) = Logic.∀ₗ(_⊧ φ)

-- Satisfiability of sets of formulas.
-- A set of formulas is satisfiable when there is a model that satisfies all of them at the same time.
Satisfiable : PredSet{ℓ}(Formula(vars)) → Type
Satisfiable(Γ) = Logic.∃(_⊧₊ Γ)

-- Unsatisfiability of sets of formulas.
Unsatisfiable : PredSet{ℓ}(Formula(vars)) → Type
Unsatisfiable{ℓ} = Logic.¬_ ∘ Satisfiable{ℓ}

-- Semantic entailment of a formula.
-- A hypothetical statement. If a model would satisfy all formulas in Γ, then this same model satisifes the formula φ.
_⊨_ : PredSet{ℓ}(Formula(vars)) → Formula(vars) → Type
Γ ⊨ φ = ∀{𝔐} → (𝔐 ⊧₊ Γ) → (𝔐 ⊧ φ)

_⊭_ : PredSet{ℓ}(Formula(vars)) → Formula(vars) → Type
_⊭_ = (Logic.¬_) ∘₂ (_⊨_)

-- Axiomatization of a theory by a set of axioms.
-- A set of axioms is a set of formulas.
-- A theory is the closure of a set of axioms.
-- An axiomatization is a subset of formulas of the theory which entails all formulas in the axiomatized theory.
_axiomatizes_ : PredSet{ℓ₁}(Formula(vars)) → PredSet{ℓ₂}(Formula(vars)) → Type
Γ₁ axiomatizes Γ₂ = ∀{φ} → (Γ₁ ⊨ φ) → Γ₂(φ)

-- A set of formulas is closed when it includes all formulas that it entails.
Closed : PredSet{ℓ}(Formula(vars)) → Type
Closed(Γ) = Γ axiomatizes Γ

_⊨₊_ : PredSet{ℓ₁}(Formula(vars)) → PredSet{ℓ₂}(Formula(vars)) → Type
Γ₁ ⊨₊ Γ₂ = ∀{𝔐} → (𝔐 ⊧₊ Γ₁) → (𝔐 ⊧₊ Γ₂)

_⊭₊_ : PredSet{ℓ₁}(Formula(vars)) → PredSet{ℓ₂}(Formula(vars)) → Type
_⊭₊_ = (Logic.¬_) ∘₂ (_⊨₊_)
