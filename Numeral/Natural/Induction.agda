module Numeral.Natural.Induction{ℓ} where

open import Logic
open import Logic.Propositional
open import Functional
open import Numeral.Natural

-- The induction proof method on natural numbers
-- TODO: There seems to be a problem making i implicit with unsolved metas.
-- TODO: Maybe rename to elim because this is the elimination rule for ℕ
ℕ-elim : ∀{T : ℕ → Stmt{ℓ}} → T(𝟎) → ((i : ℕ) → T(i) → T(𝐒(i))) → ((n : ℕ) → T(n))
ℕ-elim {T} base step 𝟎      = base
ℕ-elim {T} base step (𝐒(n)) = step n (ℕ-elim {T} base step n)

[ℕ]-induction : ∀{φ : ℕ → Stmt{ℓ}} → φ(𝟎) → (∀(i : ℕ) → φ(i) → φ(𝐒(i))) → (∀{n} → φ(n))
[ℕ]-induction {φ} base step {n} = ℕ-elim {φ} base step n

[ℕ]-inductionᵢ : ∀{φ : ℕ → Stmt{ℓ}} → φ(𝟎) → (∀{i : ℕ} → φ(i) → φ(𝐒(i))) → (∀{n} → φ(n))
[ℕ]-inductionᵢ {φ} base step = [ℕ]-induction {φ} base (i ↦ step{i})
