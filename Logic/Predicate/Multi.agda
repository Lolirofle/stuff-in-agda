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

{- TODO: Move this somewhere
[∀₊]-unrelatedᵣ-[→] : (n : ℕ) → ∀{ℓ₁ ℓ₂}{ℓ𝓈 : Lvl.Level ^ n}{As : Types(ℓ𝓈)}{P : Type{ℓ₁}}{Q : As ⇉ Type{ℓ₂}} → ∀₊(n) (compose(n) (P →ᶠ_) Q) → (P → ∀₊(n) Q)
[∀₊]-unrelatedᵣ-[→] 0        apq      = apq
[∀₊]-unrelatedᵣ-[→] 1        apq p{x} = apq{x} p
[∀₊]-unrelatedᵣ-[→] (𝐒(𝐒 n)) apq p{x} = [∀₊]-unrelatedᵣ-[→] (𝐒 n) (apq{x}) p
-}
