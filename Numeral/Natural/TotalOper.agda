module Numeral.Natural.TotalOper where

import Lvl
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural hiding (𝐏)
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs

-- Total predecessor function (Truncated predecessor)
𝐏 : (n : ℕ) → ⦃ _ : Positive(n) ⦄ → ℕ
𝐏(𝐒(n)) = n

-- Total subtraction (Truncated subtraction)
_−_ : (a : ℕ) → (b : ℕ) → ⦃ _ : a ≥ b ⦄ → ℕ
_−_ a 𝟎 = a
_−_ 𝟎 (𝐒(b)) ⦃ 0≥𝐒b ⦄ with ([<]-to-[≱] ([<]-minimum{b})) (0≥𝐒b)
... | ()
_−_ (𝐒(a)) (𝐒(b)) ⦃ 𝐒b≤𝐒a ⦄ = _−_ a b ⦃ [≤]-without-[𝐒] {b} (𝐒b≤𝐒a) ⦄

-- Total division (Positive whole number division)
_/_ : (a : ℕ) → (b : ℕ) → ⦃ _ : (b ∣ a) ⦄ → ⦃ _ : Positive(b) ⦄ → ℕ
_/_ _ _ ⦃ b-div-a ⦄ ⦃ _ ⦄ with divides-elim (b-div-a)
... | [∃]-intro (n) ⦃ b⋅n≡a ⦄ = n
