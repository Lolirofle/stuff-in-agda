module Numeral.Integer.Relation{ℓ} where

import      Lvl
open import Logic.Propositional{ℓ}
open import Numeral.Integer
open import Numeral.Integer.Oper
import      Numeral.Natural.Relation.Order as ℕ
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}

-- Inequalities/Comparisons
data _≤_ : ℤ → ℤ → Stmt where
  [−]≤[+] : ∀{a b} → (−𝐒ₙ(a)) ≤ (+ₙ b)
  instance [+]≤[+] : ∀{a b} → ⦃ _ : ℕ._≤_ {ℓ} a b ⦄ → (+ₙ a)   ≤ (+ₙ b)
  instance [-]≤[-] : ∀{a b} → ⦃ _ : ℕ._≤_ {ℓ} a b ⦄ → (−𝐒ₙ(b)) ≤ (−𝐒ₙ(a))

_<_ : ℤ → ℤ → Stmt
_<_ a b = (𝐒(a) ≤ b)

open From-[≤][<] (_≤_) (_<_) public
