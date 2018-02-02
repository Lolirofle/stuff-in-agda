module Numeral.Natural.Relation{ℓ} where

import Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals{ℓ}{Lvl.𝟎}
open import Relator.Equals.Theorems{ℓ}{Lvl.𝟎}

-- Inequalities/Comparisons
-- TODO: Consider defining (_≤_) in the same way as (_divides_)

data _lteq_ : ℕ → ℕ → Stmt where
  instance
    LtEq𝟎 : ∀{y} → 0 lteq y
    LtEq𝐒 : ∀{x y} → (x lteq y) → (x lteq (𝐒(y)))

_lteq2_ : ℕ → ℕ → Stmt
𝟎    lteq2 n    = ⊤
𝐒(_) lteq2 𝟎    = ⊥
𝐒(a) lteq2 𝐒(b) = a lteq2 b

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

-- TODO: Prove that these are the negations
