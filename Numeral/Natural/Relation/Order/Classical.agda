module Numeral.Natural.Relation.Order.Classical where

import Lvl
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Natural
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Decidable
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Properties
open import Relator.Ordering.Proofs
open import Type.Properties.Decidable.Proofs
open import Type

instance
  [≰][>]-sub : (_≰_) ⊆₂ (_>_)
  [≰][>]-sub = From-[≤][<].ByReflTriSub.[≰][>]-sub (_≤_)(_<_) ⦃ [<][≤]-sub = intro(sub₂(_<_)(_≤_)) ⦄ ⦃ [<]-classical = decider-classical _ ⦄

instance
  [≯][≤]-sub : (_≯_) ⊆₂ (_≤_)
  [≯][≤]-sub = From-[≤][<].ByReflTriSub.[≯][≤]-sub (_≤_)(_<_) ⦃ [<][≤]-sub = intro(sub₂(_<_)(_≤_)) ⦄ ⦃ [≤]-classical = decider-classical _ ⦄

instance
  [≱][<]-sub : (_≱_) ⊆₂ (_<_)
  [≱][<]-sub = From-[≤][<].ByReflTriSub.[≱][<]-sub (_≤_)(_<_) ⦃ [<][≤]-sub = intro(sub₂(_<_)(_≤_)) ⦄ ⦃ [<]-classical = decider-classical _ ⦄

instance
  [≮][≥]-sub : (_≮_) ⊆₂ (_≥_)
  [≮][≥]-sub = From-[≤][<].ByReflTriSub.[≮][≥]-sub (_≤_)(_<_) ⦃ [<][≤]-sub = intro(sub₂(_<_)(_≤_)) ⦄ ⦃ [≤]-classical = decider-classical _ ⦄

[≤]-or-[>] : ∀{a b : ℕ} → (a ≤ b) ∨ (a > b)
[≤]-or-[>] = From-[≤][<].ByReflTriSub.[≤]-or-[>] (_≤_)(_<_) ⦃ [<][≤]-sub = intro(sub₂(_<_)(_≤_)) ⦄ ⦃ [≤]-classical = decider-classical _ ⦄ ⦃ [<]-classical = decider-classical _ ⦄

[≥]-or-[<] : ∀{a b : ℕ} → (a ≥ b) ∨ (a < b)
[≥]-or-[<] = From-[≤][<].ByReflTriSub.[≥]-or-[<] (_≤_)(_<_) ⦃ [<][≤]-sub = intro(sub₂(_<_)(_≤_)) ⦄ ⦃ [≤]-classical = decider-classical _ ⦄ ⦃ [<]-classical = decider-classical _ ⦄
