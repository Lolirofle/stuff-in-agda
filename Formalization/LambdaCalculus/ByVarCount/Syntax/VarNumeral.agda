module Formalization.LambdaCalculus.ByVarCount.Syntax.VarNumeral where

open import Formalization.LambdaCalculus.ByVarCount
open import Numeral.Finite
open import Syntax.Number

-- Syntax for writing Var as a numeral.
instance
  Term-from-ℕ : ∀{N} → Numeral(Term(N)) (Numeral.Restriction(𝕟-numeral{N}))
  num ⦃ Term-from-ℕ ⦄ (n) = Var(num n)
