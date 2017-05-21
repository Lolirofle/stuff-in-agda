module Numeral.Natural.Prime{lvl} where

import Level as Lvl
open import Logic.Propositional{lvl}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation{lvl}

Prime : (n : ℕ) → Stmt
Prime n = ∀{x y : ℕ} → (n divides (x ⋅ y)) → (n divides x) ∨ (n divides y)
-- ∀{x y} → (x ≢ 0)∧(x ≢ 1) → (y ≢ 0)∧(y ≢ 1) → ¬(x ⋅ y ≡ n)

-- [2]-prime : Prime 2
-- [2]-prime n = 
