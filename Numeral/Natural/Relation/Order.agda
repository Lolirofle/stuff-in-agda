module Numeral.Natural.Relation.Order where

import Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals
open import Relator.Equals.Proofs
open import Relator.Ordering

-- Inequalities/Comparisons

data _≤_ : ℕ → ℕ → Stmt{Lvl.𝟎} where
  min  : ∀{y} → (𝟎 ≤ y)
  succ : ∀{x y} → (x ≤ y) → (𝐒(x) ≤ 𝐒(y))

_<_ : ℕ → ℕ → Stmt
_<_ a b = (𝐒(a) ≤ b)

open From-[≤][<] (_≤_)(_<_) public
