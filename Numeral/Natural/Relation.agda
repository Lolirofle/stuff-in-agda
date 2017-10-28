module Numeral.Natural.Relation{ℓ} where

import Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals{ℓ}{Lvl.𝟎}

-- Inequalities/Comparisons
-- TODO: Consider defining (_≤_) in the same way as (_divides_)

data _lteq_ : ℕ → ℕ → Stmt where
  instance
    LtEq𝟎 : ∀{x} → 0 lteq x
    LtEq𝐒 : ∀{x y} → (x lteq y) → (x lteq (𝐒(y)))

_≤_ : ℕ → ℕ → Stmt
_≤_ a b = ∃ \(n : ℕ) → (a + n ≡ b)

_<_ : ℕ → ℕ → Stmt
_<_ a b = (𝐒(a) ≤ b)

_≥_ : ℕ → ℕ → Stmt
_≥_ a b = (b ≤ a)

_>_ : ℕ → ℕ → Stmt
_>_ a b = (b < a)

_≰_ : ℕ → ℕ → Stmt
_≰_ a b = (a > b)

_≮_ : ℕ → ℕ → Stmt
_≮_ a b = (a ≥ b)

_≱_ : ℕ → ℕ → Stmt
_≱_ a b = (a < b)

_≯_ : ℕ → ℕ → Stmt
_≯_ a b = (a ≤ b)

-- TODO: CoPrime
