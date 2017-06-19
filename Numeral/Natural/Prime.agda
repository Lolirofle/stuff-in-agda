module Numeral.Natural.Prime{ℓ} where

import Level as Lvl
open import Logic.Propositional{ℓ}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Relation{ℓ}
open import Numeral.Natural.Relation.Properties{ℓ}
open import Relator.Equals{ℓ}

data Prime(n : ℕ) : Stmt where
  Prime-intro : (∀{x} → (x divides n) → (x ≡ 1)∨(x ≡ n)) → Prime(n)
-- ∀{x y : ℕ} → (n divides (x ⋅ y)) → (n divides x) ∨ (n divides y)
-- ∀{x y} → (x ≢ 0)∧(x ≢ 1) → (y ≢ 0)∧(y ≢ 1) → ¬(x ⋅ y ≡ n)

-- [2]-prime : Prime(2)
-- [2]-prime = f where
--   f : ∀{x} → (x divides 2) → (x ≡ 1)∨(x ≡ 2)
--   f{0} (0div2) = [⊥]-elim([0]-divides-not(0div2))
--   f{1} (1div2) = [∨]-introₗ ([≡]-intro)
--   f{2} (2div2) = [∨]-introᵣ ([≡]-intro)
--   f{3} (3div2) = f(div)
--   f{𝐒(n)} (ndiv2) = f(div)
