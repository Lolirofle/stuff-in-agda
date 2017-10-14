module Numeral.Natural.Proof where

open import Numeral.Natural

-- The induction proof method on natural numbers
-- TODO: Consider making i and n implicit
[ℕ]-induction : ∀{ℓ}{X : ℕ → Set(ℓ)} → X(𝟎) → ((i : ℕ) → X(i) → X(𝐒(i))) → (n : ℕ) → X(n)
[ℕ]-induction base next 𝟎 = base
[ℕ]-induction base next (𝐒(n)) = next(n)([ℕ]-induction base next n)

-- [ℕ]-induction' : ∀{X : ℕ → Set}{b : ℕ} → (∀{i : ℕ} → i ≤ b → X(i)) → ((i : ℕ) → X(i) → X(𝐒(i))) → (n : ℕ) → X(n)
