module Numeral.Natural where

-- The set of natural numbers (0,..).
-- Positive integers including zero.
data ℕ : Set where
  𝟎 : ℕ      -- Zero
  𝐒 : ℕ → ℕ -- Successor function (Intuitively: 𝐒(n) = n+1)
{-# BUILTIN NATURAL ℕ #-}

-- Limited predecessor function
-- Intuitively: 𝐏(n) = max(0,n-1)
𝐏 : ℕ → ℕ
𝐏(𝟎)    = 𝟎
𝐏(𝐒(n)) = n

-- The induction proof method on natural numbers
[ℕ]-induction : ∀{lvl}{X : ℕ → Set(lvl)} → X(𝟎) → ((i : ℕ) → X(i) → X(𝐒(i))) → (n : ℕ) → X(n)
[ℕ]-induction base next 𝟎 = base
[ℕ]-induction base next (𝐒(n)) = next(n)([ℕ]-induction base next n)

-- [ℕ]-induction' : ∀{X : ℕ → Set}{b : ℕ} → (∀{i : ℕ} → i ≤ b → X(i)) → ((i : ℕ) → X(i) → X(𝐒(i))) → (n : ℕ) → X(n)
