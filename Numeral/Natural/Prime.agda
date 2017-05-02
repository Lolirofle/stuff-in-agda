module Numeral.Natural.Prime where

import Level as Lvl
open import Logic.Propositional{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation

Prime : (n : ℕ) → Stmt
Prime n = ∀{x y : ℕ} → (n divides (x ⋅ y)) → (n divides x) ∨ (n divides y)

-- [2]-prime : Prime 2
-- [2]-prime n = 
