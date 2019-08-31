module Numeral.Natural.Relation.Order.Existence{ℓ} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}
open import Structure.Relator.Ordering{ℓ}{Lvl.𝟎}

_≤_ : ℕ → ℕ → Stmt
_≤_ a b = ∃ \(n : ℕ) → (a + n ≡ b)

_<_ : ℕ → ℕ → Stmt
_<_ a b = (𝐒(a) ≤ b)

open From-[≤][<] (_≤_) (_<_) public
