module Numeral.Natural.Relation.Order.Classical where

import Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Classical
open import Logic.Computability.Binary
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Order.Computability
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Type

[≰]-to-[>] : ∀{a b : ℕ} → (a ≰ b) → (a > b)
[≰]-to-[>] {a}{b} (a≰b) with excluded-middle _ ⦃ ComputablyDecidable.classical(_>_) ⦄
... | [∨]-introₗ a>b = a>b
... | [∨]-introᵣ a≯b = [⊥]-elim ([≰][≯]-not (a≰b) (a≯b))

[≯]-to-[≤] : ∀{a b : ℕ} → (a ≯ b) → (a ≤ b)
[≯]-to-[≤] {a}{b} = contrapositive-variant2ₗ ⦃ ComputablyDecidable.classical(_≤_) ⦄ ([≰]-to-[>] {a}{b})

[≱]-to-[<] : ∀{a b : ℕ} → (a ≱ b) → (a < b)
[≱]-to-[<] {a}{b} (a≱b) with excluded-middle _ ⦃ ComputablyDecidable.classical(_<_) ⦄
... | [∨]-introₗ a<b = a<b
... | [∨]-introᵣ a≮b = [⊥]-elim ([≮][≱]-not (a≮b) (a≱b))

[≮]-to-[≥] : ∀{a b : ℕ} → (a ≮ b) → (a ≥ b)
[≮]-to-[≥] {a}{b} = contrapositive-variant2ₗ ⦃ ComputablyDecidable.classical(_≥_) ⦄ ([≱]-to-[<] {a}{b})

[≤]-or-[>] : ∀{a b : ℕ} → (a ≤ b)∨(a > b)
[≤]-or-[>] with excluded-middle _ ⦃ ComputablyDecidable.classical(_≤_) ⦄
... | [∨]-introₗ a≤b = [∨]-introₗ a≤b
... | [∨]-introᵣ a≰b = [∨]-introᵣ ([≰]-to-[>] a≰b)

[≥]-or-[<] : ∀{a b : ℕ} → (a < b)∨(a ≥ b)
[≥]-or-[<] with excluded-middle _  ⦃ ComputablyDecidable.classical(_≤_) ⦄
... | [∨]-introₗ a≥b = [∨]-introᵣ a≥b
... | [∨]-introᵣ a≱b = [∨]-introₗ ([≱]-to-[<] a≱b)
