open import Numeral.Natural
open import Relator.Equals
open import Type.Properties.Decidable
open import Type

module Formalization.ClassicalPredicateLogic.Semantics
  {ℓₘ ℓₚ ℓᵥ ℓₒ}
  (Prop : ℕ → Type{ℓₚ})
  (Var : Type{ℓᵥ}) ⦃ var-eq-dec : Decidable(2)(_≡_ {T = Var}) ⦄
  (Obj : ℕ → Type{ℓₒ})
  where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.ListSized
import      Data.ListSized.Functions as List
open import Formalization.ClassicalPredicateLogic.Syntax(Prop)(Var)(Obj)
open import Functional using (_∘_ ; _∘₂_)
import      Logic.Propositional as Logic
import      Logic.Predicate     as Logic
open import Sets.PredicateSet using (PredSet)
open        Sets.PredicateSet.BoundedQuantifiers
open import Syntax.Function
open import Type.Dependent renaming (intro to _,_)
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level

module _ where
  private variable P : Type{ℓₚ}
  private variable n : ℕ

  -- Model.
  -- A model decides which propositional constants that are true or false.
  record Model : Type{ℓₚ Lvl.⊔ ℓₒ Lvl.⊔ ℓᵥ Lvl.⊔ Lvl.𝐒(ℓₘ)} where
    field
      Domain : Type{ℓₘ}
      function : Obj(n) → List(Domain)(n) → Domain
      predicate : Prop(n) → List(Domain)(n) → Bool

  private variable 𝔐 : Model

  -- Also called: Variable assignment.
  VarMapping : Model → Type
  VarMapping(𝔐) =  Var → Model.Domain(𝔐)

  mapSingle : VarMapping(𝔐) → Var → Model.Domain(𝔐) → VarMapping(𝔐)
  mapSingle 𝔰 x t y =
    if decide(2)(_≡_) ⦃ var-eq-dec ⦄ x y
    then t
    else 𝔰(y)

  private variable 𝔰 : VarMapping(𝔐)

  module _ ((𝔐 , 𝔰) : Σ Model VarMapping) where
    val : Term → Model.Domain(𝔐)
    val₊ : List(Term)(n) → List(Model.Domain(𝔐))(n)

    val(var v)    = 𝔰(v)
    val(func f x) = Model.function 𝔐 f (val₊ x)
    val₊ {0}       ∅       = ∅
    val₊ {𝐒(n)} (t ⊰ ts) = (val t ⊰ val₊ {n} ts)
    --val₊ = List.map val

  -- Satisfication relation.
  -- ((𝔐 , 𝔰) ⊧ φ) means that the formula φ is satisfied in the model 𝔐 with the variable mapping.
  -- Or in other words: A formula is true in the model 𝔐.
  _⊧_ : (Σ Model VarMapping) → Formula → Type{ℓₘ}
  (𝔐 , 𝔰) ⊧ (f $ x)  = Lvl.Up(IsTrue(Model.predicate 𝔐 f (val₊(𝔐 , 𝔰) x)))  -- A model decides whether a relation is satisfied.
  (𝔐 , 𝔰) ⊧ ⊤        = Unit                                                 -- All models satisfy top.
  (𝔐 , 𝔰) ⊧ ⊥        = Empty                                                -- No model satisfies bottom.
  (𝔐 , 𝔰) ⊧ (φ ∧ ψ)  = ((𝔐 , 𝔰) ⊧ φ) Logic.∧ ((𝔐 , 𝔰) ⊧ ψ)                  -- A model satisfies a conjunction when it satisfies both of the propositions.
  (𝔐 , 𝔰) ⊧ (φ ∨ ψ)  = ((𝔐 , 𝔰) ⊧ φ) Logic.∨ ((𝔐 , 𝔰) ⊧ ψ)                  -- A model satisfies a disjunction when it satisfies any one of the propositions.
  (𝔐 , 𝔰) ⊧ (φ ⟶ ψ)  = Logic.¬((𝔐 , 𝔰) ⊧ φ) Logic.∨ ((𝔐 , 𝔰) ⊧ ψ)
  (𝔐 , 𝔰) ⊧ (Ɐ(x) φ) = Logic.∀ₗ(t ↦ (𝔐 , mapSingle{𝔐 = 𝔐} 𝔰 x t) ⊧ φ)
  (𝔐 , 𝔰) ⊧ (∃(x) φ) = Logic.∃(t ↦ (𝔐 , mapSingle{𝔐 = 𝔐} 𝔰 x t) ⊧ φ)

  -- Satisfication of a set of formulas.
  -- This means that a model satisfies all formulas at the same time.
  _⊧₊_ : (Σ Model VarMapping) → PredSet{ℓ}(Formula) → Type
  𝔐 ⊧₊ Γ = ∀ₛ(Γ) (𝔐 ⊧_)

  -- Validity of a formula.
  -- A formula is valid when it is true independent of any model.
  Valid : Formula → Type
  Valid(φ) = Logic.∀ₗ(_⊧ φ)

  -- Satisfiability of sets of formulas.
  -- A set of formulas is valid when there is a model that satisfies all of them at the same time.
  Satisfiable : PredSet{ℓ}(Formula) → Type
  Satisfiable(Γ) = Logic.∃(_⊧₊ Γ)

  -- Unsatisfiability of sets of formulas.
  Unsatisfiable : PredSet{ℓ}(Formula) → Type
  Unsatisfiable{ℓ} = Logic.¬_ ∘ Satisfiable{ℓ}

  -- Semantic entailment of a formula.
  -- A hypothetical statement. If a model would satisfy all formulas in Γ, then this same model satisifes the formula φ.
  _⊨_ : PredSet{ℓ}(Formula) → Formula → Type
  Γ ⊨ φ = ∀{𝔐} → (𝔐 ⊧₊ Γ) → (𝔐 ⊧ φ)

  _⊭_ : PredSet{ℓ}(Formula) → Formula → Type
  _⊭_ = (Logic.¬_) ∘₂ (_⊨_)

  -- Axiomatization of a theory by a set of axioms.
  -- A set of axioms is a set of formulas.
  -- A theory is the closure of a set of axioms.
  -- An axiomatization is a subset of formulas of the theory which entails all formulas in the axiomatized theory.
  _axiomatizes_ : PredSet{ℓ₁}(Formula) → PredSet{ℓ₂}(Formula) → Type
  Γ₁ axiomatizes Γ₂ = ∀{φ} → (Γ₁ ⊨ φ) → Γ₂(φ)

  -- A set of formulas is closed when it includes all formulas that it entails.
  Closed : PredSet{ℓ}(Formula) → Type
  Closed(Γ) = Γ axiomatizes Γ

  _⊨₊_ : PredSet{ℓ₁}(Formula) → PredSet{ℓ₂}(Formula) → Type
  Γ₁ ⊨₊ Γ₂ = ∀{𝔐} → (𝔐 ⊧₊ Γ₁) → (𝔐 ⊧₊ Γ₂)

  _⊭₊_ : PredSet{ℓ₁}(Formula) → PredSet{ℓ₂}(Formula) → Type
  _⊭₊_ = (Logic.¬_) ∘₂ (_⊨₊_)
