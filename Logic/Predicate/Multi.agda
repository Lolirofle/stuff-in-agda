module Logic.Predicate.Multi where

open import Data.Tuple.RaiseTypeᵣ
open import Function.Multi
open import Function.Multi.Functions
open import Numeral.Natural
open import Logic.Predicate
open import Logic

-- Universal quantification of multiple variables.
-- Example:
--   ∀₊(3) P = ∀{x}{y}{z} → P(x)(y)(z)
∀₊ : (n : ℕ) → ∀{ℓ}{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (As ⇉ Stmt{ℓ}) → Stmt
∀₊(n) = quantifier₊(n) ∀ₗ

-- Existential quantification of multiple variables.
-- Example:
--   ∃₊(3) P = ∃(x ↦ ∃(y ↦ ∃(z ↦ P(x)(y)(z))))
∃₊ : (n : ℕ) → ∀{ℓ}{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (As ⇉ Stmt{ℓ}) → Stmt
∃₊(n) = quantifier₊(n) ∃
