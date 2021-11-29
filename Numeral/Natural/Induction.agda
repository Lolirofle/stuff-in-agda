module Numeral.Natural.Induction where

open import Numeral.Natural
open import Type

-- The ℕ eliminator.
-- Also the induction proof method on natural numbers.
ℕ-elim : ∀{ℓ} → (T : ℕ → Type{ℓ}) → T(𝟎) → ((i : ℕ) → T(i) → T(𝐒(i))) → ((n : ℕ) → T(n))
ℕ-elim T base step 𝟎      = base
ℕ-elim T base step (𝐒(n)) = step n (ℕ-elim T base step n)
