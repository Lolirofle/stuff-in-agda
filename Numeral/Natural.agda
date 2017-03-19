module Numeral.Natural where

data ℕ : Set where
  𝟎 : ℕ
  𝐒 : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

[ℕ]-induction : {X : ℕ → Set} → X(𝟎) → ((i : ℕ) → X(i) → X(𝐒(i))) → (n : ℕ) → X(n)
[ℕ]-induction base next 𝟎 = base
[ℕ]-induction base next (𝐒(n)) = next(n)([ℕ]-induction base next n)
