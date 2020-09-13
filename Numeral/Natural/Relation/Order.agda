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
  instance
    [≤]-minimum  : ∀{y}   → (𝟎 ≤ y)
    [≤]-with-[𝐒] : ∀{x y} → ⦃ _ : x ≤ y ⦄ → (𝐒(x) ≤ 𝐒(y))

_<_ : ℕ → ℕ → Stmt
_<_ a b = (𝐒(a) ≤ b)

pattern [<]-minimum {y} = [≤]-with-[𝐒] ⦃ [≤]-minimum {y} ⦄

open From-[≤][<] (_≤_) (_<_) public
