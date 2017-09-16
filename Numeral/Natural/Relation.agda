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

-- Divisibility
data Even : ℕ → Stmt where
  instance
    Even0 : Even 𝟎
    Even𝐒 : ∀{x : ℕ} → (Even x) → (Even(𝐒(𝐒(x))))

data Odd : ℕ → Stmt where
  instance
    Odd0 : Odd (𝐒(𝟎))
    Odd𝐒 : ∀{x : ℕ} → (Odd x) → (Odd(𝐒(𝐒(x))))

data _divides_ (y : ℕ) : ℕ → Stmt where
  instance
    Div𝟎 : y divides 𝟎
    Div𝐒 : ∀{x : ℕ} → (y divides x) → (y divides (y + x))

data _divides_withRemainder_ : ℕ → ℕ → ℕ → Stmt where -- TODO: Make _divides_ a special case of this
  instance
    DivRem𝟎 : ∀{x : ℕ}{r : ℕ} → (r < x) → x divides r withRemainder r
    DivRem𝐒 : ∀{x : ℕ}{y : ℕ}{r : ℕ} → (x divides y withRemainder r) → (x divides (x + y) withRemainder r)
