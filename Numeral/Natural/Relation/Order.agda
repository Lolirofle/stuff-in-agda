module Numeral.Natural.Relation.Order {ℓ} where

import Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}

-- Inequalities/Comparisons

data _≤_ : ℕ → ℕ → Stmt where
  instance
    [≤][0]ᵣ-minimum : ∀{y}   → (𝟎 ≤ y)
    [≤]-with-[𝐒]   : ∀{x y} → (x ≤ y) → (𝐒(x) ≤ 𝐒(y))

_<_ : ℕ → ℕ → Stmt
_<_ a b = (𝐒(a) ≤ b)

open From-[≤][<] (_≤_) (_<_) public
