module Numeral.Natural.Relation where

import Level as Lvl
open import Logic(Lvl.𝟎)
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals(Lvl.𝟎)

-- Divisibility
data Even : ℕ → Stmt where
  Even0 : Even 𝟎
  Even𝐒 : {x : ℕ} → (Even x) → (Even(𝐒(𝐒(x))))

data Odd : ℕ → Stmt where
  Odd0 : Odd (𝐒(𝟎))
  Odd𝐒 : {x : ℕ} → (Odd x) → (Odd(𝐒(𝐒(x))))

data _divides_ : ℕ → ℕ → Stmt where
  Div0 : {x : ℕ} → x divides 𝟎
  Div𝐒 : {x : ℕ}{y : ℕ} → (x divides y) → (x divides (x + y))

data _divides_withRemainder_ : ℕ → ℕ → ℕ → Stmt where
  DivRem0 : {x : ℕ}{r : ℕ} → x divides r withRemainder r
  DivRem𝐒 : {x : ℕ}{y : ℕ}{r : ℕ} → (x divides y withRemainder r) → (x divides (x + y) withRemainder r)

-- Inequalities/Comparisons
_≤_ : ℕ → ℕ → Stmt
_≤_ a b = ∃ \(n : ℕ) → (a + n ≡ b)

_<_ : ℕ → ℕ → Stmt
_<_ a b = (𝐒(a) ≤ b)

_≥_ : ℕ → ℕ → Stmt
_≥_ a b = (b ≤ a)

_>_ : ℕ → ℕ → Stmt
_>_ a b = (b < a)
