open import Data.Tuple.RaiseTypeᵣ
open import Numeral.Natural
open import Type

module Logic.Decidable (n : ℕ) {ℓ𝓈} {As : Types{n}(ℓ𝓈)} where

import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Proofs using (module IsTrue ; module IsFalse)
open import Data.Boolean.Proofs
open import Functional
open import Function.Multi
open import Function.Multi.Functions
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Logic.Predicate.Theorems
open import Relator.Equals
open import Type
open import Type.Properties.Empty
open import Syntax.Function

private variable ℓ : Lvl.Level

-- TODO: Maybe not like this. It is difficult to prove stuff generally for all n
record Decider (P : As ⇉ Stmt{ℓ}) (decide : As ⇉ Bool) : Stmt{ℓ Lvl.⊔ Lvl.⨆(ℓ𝓈)} where
  constructor intro
  field
    decide-is-true  : ∀₊(n) (pointwise(n)(2) (_↔_) P         (IsTrue ∘ᵣ decide))
    decide-is-false : ∀₊(n) (pointwise(n)(2) (_↔_) (¬_ ∘ᵣ P) (IsFalse ∘ᵣ decide))
    -- decidable : ∀₊(as ↦ P(as) ∨ (¬ P(as)))


Decidable : (As ⇉ Stmt{ℓ}) → Stmt
Decidable(P) = ∃(Decider(P))

decide : ∀{P : As ⇉ Stmt{ℓ}} ⦃ _ : Decidable(P) ⦄ → (As ⇉ Bool)
decide ⦃ d ⦄ = [∃]-witness(d)
