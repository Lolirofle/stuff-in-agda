open import Numeral.Natural
open import Type

module Formalization.ClassicalPredicateLogic.Syntax {ℓₚ ℓᵥ ℓₒ} (Prop : ℕ → Type{ℓₚ}) (Var : Type{ℓᵥ}) (Obj : ℕ → Type{ℓₒ}) where

open import Data.ListSized
import      Lvl
open import Functional using (_∘_ ; _∘₂_ ; swap)
open import Sets.PredicateSet using (PredSet)

private variable ℓ : Lvl.Level
private variable n : ℕ

data Term : Type{ℓᵥ Lvl.⊔ ℓₒ} where
  var  : Var → Term                -- Variables
  func : Obj(n) → List(Term)(n) → Term -- Constants/functions

-- Formulas.
-- Inductive definition of the grammatical elements of the language of predicate logic.
data Formula : Type{ℓₚ Lvl.⊔ ℓᵥ Lvl.⊔ ℓₒ} where
  _$_ : Prop(n) → List(Term)(n) → Formula -- Relations

  ⊤ : Formula -- Tautology (Top / True)
  ⊥ : Formula -- Contradiction (Bottom / False)

  _∧_ : Formula → Formula → Formula -- Conjunction (And)
  _∨_ : Formula → Formula → Formula -- Disjunction (Or)
  _⟶_ : Formula → Formula → Formula -- Implication

  Ɐ : Var → Formula → Formula
  ∃ : Var → Formula → Formula

infix  1011 _$_
infixr 1005 _∧_
infixr 1004 _∨_
infixr 1000 _⟶_

-- Negation
¬_ : Formula → Formula
¬_ = _⟶ ⊥

-- Double negation
¬¬_ : Formula → Formula
¬¬_ = (¬_) ∘ (¬_)

-- Reverse implication
_⟵_ : Formula → Formula → Formula
_⟵_ = swap(_⟶_)

-- Equivalence
_⟷_ : Formula → Formula → Formula
p ⟷ q = (p ⟵ q) ∧ (p ⟶ q)

-- (Nor)
_⊽_ : Formula → Formula → Formula
_⊽_ = (¬_) ∘₂ (_∨_)

-- (Nand)
_⊼_ : Formula → Formula → Formula
_⊼_ = (¬_) ∘₂ (_∧_)

-- (Exclusive or / Xor)
_⊻_ : Formula → Formula → Formula
_⊻_ = (¬_) ∘₂ (_⟷_)

infix  1010 ¬_ ¬¬_
infixl 1000 _⟵_ _⟷_
