module Numeral.Rational where

open import Data.Tuple
open import Logic
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Integer
open import Numeral.Integer.Oper
open import Relator.Equals
open import Type
open import Type.Quotient

-- Equivalence relation of quotient equality.
-- Essentially (if one would already work in the rationals):
--   (a₁ , a₂) quot-≡_ (b₁ , b₂)
--   ⇔ a₁ ⋅ b₂ ≡ a₂ ⋅ b₁
--   ⇔ a₁ / a₂ ≡ b₁ / b₂
_quot-≡_ : (ℤ ⨯ ℕ₊) → (ℤ ⨯ ℕ₊) → Stmt{Lvl.𝟎}
(a₁ , a₂) quot-≡ (b₁ , b₂) = (a₁ ⋅ b₂ ≡ a₂ ⋅ b₁)

ℤ : Type{Lvl.𝟎}
ℤ = (ℤ ⨯ ℕ₊) / (_quot-≡_)
