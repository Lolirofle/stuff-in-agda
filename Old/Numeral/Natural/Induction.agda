module Numeral.Natural.Induction{ℓ} where

open import Logic.Propositional{ℓ}
open import Functional
open import Numeral.Natural

-- The induction proof method on natural numbers
-- TODO: There seems to be a problem making i implicit with unsolved metas.
[ℕ]-induction : ∀{φ : ℕ → Stmt} → φ(𝟎) → (∀(i : ℕ) → φ(i) → φ(𝐒(i))) → (∀{n} → φ(n))
[ℕ]-induction {φ} (base) (next) {𝟎}    = base
[ℕ]-induction {φ} (base) (next) {𝐒(n)} = next(n) ([ℕ]-induction {φ} (base) (next) {n})

[ℕ]-inductionᵢ : ∀{φ : ℕ → Stmt} → φ(𝟎) → (∀{i : ℕ} → φ(i) → φ(𝐒(i))) → (∀{n} → φ(n))
[ℕ]-inductionᵢ {φ} (base) (next) = [ℕ]-induction {φ} (base) (i ↦ next{i})
