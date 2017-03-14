module Numeral.Natural where

data ℕ : Set where
  𝟎 : ℕ
  𝐒 : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
