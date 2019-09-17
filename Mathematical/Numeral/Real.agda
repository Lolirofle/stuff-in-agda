module Numeral.Real where

open import Data.Tuple
open import Logic
import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Rational
open import Numeral.Rational.Oper
open import Relator.Equals
open import Type
open import Type.Quotient

-- TODO: This will not work, but it is the standard concept at least. Maybe there is a better way

record CauchySequence (a : ℕ → ℚ) : Stmt where
  field
    N : ℚ₊ → ℕ
    ∀{ε : ℚ₊}{m n : ℕ} → (m > N(ε)) → (n > N(ε)) → (‖ a(m) − a(n) ‖ < ε)

_converges-to-same_ : Σ(CauchySequence) → Σ(CauchySequence) → Stmt{Lvl.𝟎}
a converges-to-same b = lim(n ↦ Σ.left(a) − Σ.left(b)) ≡ 𝟎

ℝ : Type{Lvl.𝟎}
ℝ = Σ(CauchySequence) / (_converges-to-same_)

-- TODO: Here is another idea: https://github.com/dylanede/cubical-experiments/blob/master/scratch.agda
-- TODO: Also these: https://en.wikipedia.org/wiki/Construction_of_the_real_numbers#Construction_from_Cauchy_sequences
