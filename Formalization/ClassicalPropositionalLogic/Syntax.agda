module Formalization.ClassicalPropositionalLogic.Syntax where

import      Lvl
open import Functional
open import Sets.PredicateSet using (PredSet)
open import Type

private variable ℓₚ ℓ : Lvl.Level

module _ (P : Type{ℓₚ}) where
  -- Formulas.
  -- Inductive definition of the grammatical elements of the language of propositional logic.
  -- Note: It is possible to reduce the number of formula variants to for example {•,¬,∨} or {•,¬,∧} (This is called propositional adequacy/functional completeness).
  data Formula : Type{ℓₚ} where
    •_ : P → Formula -- Propositional constants

    ⊤ : Formula -- Tautology (Top / True)
    ⊥ : Formula -- Contradiction (Bottom / False)

    ¬_ : Formula → Formula -- Negation (Not)

    _∧_ : Formula → Formula → Formula -- Conjunction (And)
    _∨_ : Formula → Formula → Formula -- Disjunction (Or)
    _⟶_ : Formula → Formula → Formula -- Implication
    _⟷_ : Formula → Formula → Formula -- Equivalence

  Formulas : Type{ℓₚ Lvl.⊔ Lvl.𝐒(ℓ)}
  Formulas{ℓ} = PredSet{ℓ}(Formula)

  infix 1011 •_
  infix 1010 ¬_ ¬¬_
  infixr 1005 _∧_
  infixr 1004 _∨_
  infixr 1000 _⟷_ _⟶_

module _ {P : Type{ℓₚ}} where
  -- Double negation
  -- ¬¬_ : Formula(P) → Formula(P)
  -- ¬¬_ : (¬_) ∘ (¬_)

  -- Reverse implication
  _⟵_ : Formula(P) → Formula(P) → Formula(P)
  _⟵_ = swap(_⟶_)

  -- (Nor)
  _⊽_ : Formula(P) → Formula(P) → Formula(P)
  _⊽_ = (¬_) ∘₂ (_∨_)

  -- (Nand)
  _⊼_ : Formula(P) → Formula(P) → Formula(P)
  _⊼_ = (¬_) ∘₂ (_∧_)

  -- (Exclusive or / Xor)
  _⊻_ : Formula(P) → Formula(P) → Formula(P)
  _⊻_ = (¬_) ∘₂ (_⟷_)

  infixl 1000 _⟵_
