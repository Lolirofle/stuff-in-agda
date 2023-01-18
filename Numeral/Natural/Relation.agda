module Numeral.Natural.Relation where

open import Data.Boolean.Stmt
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Logic.Propositional
open import Logic
open import Relator.Equals

Positive : ℕ → Stmt
Positive(n) = IsTrue(positive? n)

zero-not-positive : ¬ Positive(𝟎)
zero-not-positive ()

positive-not-zero : ∀{n} → ⦃ _ : Positive(n) ⦄ → (n ≢ 𝟎)
positive-not-zero {𝟎} ⦃ pos ⦄ _ = pos

non-zero-positive : ∀{n} → (n ≢ 𝟎) → Positive(n)
non-zero-positive {𝟎}   p = p [≡]-intro
non-zero-positive {𝐒 n} p = [⊤]-intro
