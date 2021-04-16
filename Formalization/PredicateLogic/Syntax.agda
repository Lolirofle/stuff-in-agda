open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Syntax (𝔏 : Signature) where
open Signature(𝔏)

open import Data.ListSized
import      Lvl
open import Functional using (_∘_ ; _∘₂_ ; swap)
open import Numeral.Finite
open import Numeral.Natural
open import Sets.PredicateSet using (PredSet)
open import Type

private variable ℓ : Lvl.Level
private variable args vars : ℕ

data Term (vars : ℕ) : Type{ℓₒ} where
  var  : 𝕟(vars) → Term(vars)                       -- Variables
  func : Obj(args) → List(Term(vars))(args) → Term(vars) -- Constants/functions

-- Formulas.
-- Inductive definition of the grammatical elements of the language of predicate logic.
data Formula : ℕ → Type{ℓₚ Lvl.⊔ ℓₒ} where
  _$_ : Prop(args) → List(Term(vars))(args) → Formula(vars) -- Relations

  ⊤ : Formula(vars) -- Tautology (Top / True)
  ⊥ : Formula(vars) -- Contradiction (Bottom / False)

  _∧_ : Formula(vars) → Formula(vars) → Formula(vars) -- Conjunction (And)
  _∨_ : Formula(vars) → Formula(vars) → Formula(vars) -- Disjunction (Or)
  _⟶_ : Formula(vars) → Formula(vars) → Formula(vars) -- Implication

  Ɐ : Formula(𝐒(vars)) → Formula(vars)
  ∃ : Formula(𝐒(vars)) → Formula(vars)

-- A sentence is a formula with no variables occurring.
Sentence = Formula(𝟎)

infix  1011 _$_
infixr 1005 _∧_
infixr 1004 _∨_
infixr 1000 _⟶_

-- Negation
¬_ : Formula(vars) → Formula(vars)
¬_ = _⟶ ⊥

-- Double negation
¬¬_ : Formula(vars) → Formula(vars)
¬¬_ = (¬_) ∘ (¬_)

-- Reverse implication
_⟵_ : Formula(vars) → Formula(vars) → Formula(vars)
_⟵_ = swap(_⟶_)

-- Equivalence
_⟷_ : Formula(vars) → Formula(vars) → Formula(vars)
p ⟷ q = (p ⟵ q) ∧ (p ⟶ q)

-- (Nor)
_⊽_ : Formula(vars) → Formula(vars) → Formula(vars)
_⊽_ = (¬_) ∘₂ (_∨_)

-- (Nand)
_⊼_ : Formula(vars) → Formula(vars) → Formula(vars)
_⊼_ = (¬_) ∘₂ (_∧_)

-- (Exclusive or / Xor)
_⊻_ : Formula(vars) → Formula(vars) → Formula(vars)
_⊻_ = (¬_) ∘₂ (_⟷_)

infix  1010 ¬_ ¬¬_
infixl 1000 _⟵_ _⟷_

Ɐ₊ : Formula(vars) → Sentence
Ɐ₊{𝟎}   φ = φ
Ɐ₊{𝐒 v} φ = Ɐ₊{v} (Ɐ φ)

∃₊ : Formula(vars) → Sentence
∃₊{𝟎}   φ = φ
∃₊{𝐒 v} φ = ∃₊{v} (∃ φ)
