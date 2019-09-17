module Numeral.Integer where

open import Data.Tuple
open import Logic
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals
open import Type
open import Type.Quotient

-- Equivalence relation of difference equality.
-- Essentially (if one would already work in the integers):
--   (a₁ , a₂) diff-≡_ (b₁ , b₂)
--   ⇔ a₁ + b₂ ≡ a₂ + b₁
--   ⇔ a₁ − a₂ ≡ b₁ − b₂
_diff-≡_ : (ℕ ⨯ ℕ) → (ℕ ⨯ ℕ) → Stmt{Lvl.𝟎}
(a₁ , a₂) diff-≡ (b₁ , b₂) = (a₁ + b₂ ≡ a₂ + b₁)

ℤ : Type{Lvl.𝟎}
ℤ = (ℕ ⨯ ℕ) / (_diff-≡_)
