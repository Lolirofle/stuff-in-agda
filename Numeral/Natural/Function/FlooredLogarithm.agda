module Numeral.Natural.Function.FlooredLogarithm where

open import Data
open import Data.Boolean.Stmt
open import Numeral.Natural
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Strict.Properties

⌊log⌋ : (b : ℕ) → ⦃ _ : IsTrue(b ≥? 2) ⦄ → (n : ℕ) → ⦃ _ : IsTrue(n ≥? 1) ⦄ → ℕ
⌊log⌋ b@(𝐒(𝐒 _)) n = wellfounded-recursion (_<_) f(n) where
  f : (n : ℕ) → ((prev : ℕ) ⦃ _ : (prev < n) ⦄ → ℕ) → ℕ
  f 𝟎          _    = 𝟎
  f (𝐒 𝟎)      _    = 𝟎
  f n@(𝐒(𝐒 _)) prev = 𝐒(prev((n ⌊/⌋ b)) ⦃ [⌊/⌋]-ltₗ {b = b} ⦄)
