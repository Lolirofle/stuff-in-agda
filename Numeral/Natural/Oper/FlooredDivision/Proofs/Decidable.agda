module Numeral.Natural.Oper.FlooredDivision.Proofs.Decidable where

import      Lvl
open import Data.Boolean.Stmt
open import Functional.Instance
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order.Decidable
open import Type.Properties.Decidable.Proofs

[⌊/⌋]-positive-[≥?] : ∀{a b} ⦃ pos-b : Positive(b) ⦄ ⦃ ge-ab : IsTrue(a ≥? b) ⦄ → Positive(a ⌊/⌋ b)
[⌊/⌋]-positive-[≥?] {a}{b} = [↔]-to-[→] ([⌊/⌋]-positive {a}{b}) ([↔]-to-[←] decider-true infer)
