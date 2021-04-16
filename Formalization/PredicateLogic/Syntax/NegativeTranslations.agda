open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Syntax.NegativeTranslations (𝔏 : Signature) where
open Signature(𝔏)

open import Data.ListSized
import      Lvl
open import Formalization.PredicateLogic.Syntax (𝔏)
open import Functional using (_∘_ ; _∘₂_ ; swap)
open import Numeral.Finite
open import Numeral.Natural
open import Sets.PredicateSet using (PredSet)
open import Type

private variable ℓ : Lvl.Level
private variable args vars : ℕ

-- Also called: Gödel-Gentzen's negative translation.
-- 2.3.3
ggTrans : Formula(vars) → Formula(vars)
ggTrans (P $ x) = ¬¬(P $ x)
ggTrans ⊤       = ⊤
ggTrans ⊥       = ⊥
ggTrans (φ ∧ ψ) = (ggTrans φ) ∧ (ggTrans ψ)
ggTrans (φ ∨ ψ) = ¬(¬(ggTrans φ) ∧ ¬(ggTrans ψ))
ggTrans (φ ⟶ ψ) = (ggTrans φ) ⟶ (ggTrans ψ)
ggTrans (Ɐ φ)   = Ɐ(ggTrans φ)
ggTrans (∃ φ)   = ¬ Ɐ(¬(ggTrans φ))

-- Also called: Kolmogorov's negative translation.
-- 2.3.7A
koTrans : Formula(vars) → Formula(vars)
koTrans (P $ x) = ¬¬(P $ x)
koTrans ⊤       = ⊤
koTrans ⊥       = ⊥
koTrans (φ ∧ ψ) = ¬¬((koTrans φ) ∧ (koTrans ψ))
koTrans (φ ∨ ψ) = ¬¬((koTrans φ) ∨ (koTrans ψ))
koTrans (φ ⟶ ψ) = ¬¬((koTrans φ) ⟶ (koTrans ψ))
koTrans (Ɐ φ)   = ¬¬ Ɐ(koTrans φ)
koTrans (∃ φ)   = ¬¬ ∃(koTrans φ)

-- Also called: Kuroda's negative translation.
-- 2.3.7B
kuTrans : Formula(vars) → Formula(vars)
kuTrans (P $ x) = P $ x
kuTrans ⊤       = ⊤
kuTrans ⊥       = ⊥
kuTrans (φ ∧ ψ) = ((koTrans φ) ∧ (koTrans ψ))
kuTrans (φ ∨ ψ) = ((koTrans φ) ∨ (koTrans ψ))
kuTrans (φ ⟶ ψ) = ((koTrans φ) ⟶ (koTrans ψ))
kuTrans (Ɐ φ)   = Ɐ(¬¬(koTrans φ))
kuTrans (∃ φ)   = ∃(koTrans φ)
