module Numeral.Natural.Induction.Proofs where

open import Numeral.Natural
open import Numeral.Natural.Induction
open import Syntax.Function
open import Type

module _
  {ℓ₁ ℓ₂}
  (T : ℕ → Type{ℓ₁})
  (P : (x : ℕ) → T(x) → Type{ℓ₂})
  {base : T(𝟎)}
  {step : (x : ℕ) → T(x) → T(𝐒(x))}
  (pbase : P(𝟎)(base))
  (pstep : (x : ℕ) → P x (ℕ-elim T base step x) → P(𝐒(x)) (step x (ℕ-elim T base step x)))
  where

  ℕ-elim-intro : (x : ℕ) → P x (ℕ-elim T base step x)
  ℕ-elim-intro = ℕ-elim(x ↦ P x (ℕ-elim T base step x)) pbase pstep
