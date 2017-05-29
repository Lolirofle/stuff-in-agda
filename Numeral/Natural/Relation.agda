module Numeral.Natural.Relation{ℓ} where

import Level as Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Relator.Equals{ℓ}{Lvl.𝟎}

-- Divisibility
data Even : ℕ → Stmt where
  Even0 : Even 𝟎
  Even𝐒 : ∀{x : ℕ} → (Even x) → (Even(𝐒(𝐒(x))))

data Odd : ℕ → Stmt where
  Odd0 : Odd (𝐒(𝟎))
  Odd𝐒 : ∀{x : ℕ} → (Odd x) → (Odd(𝐒(𝐒(x))))

data _divides_ : ℕ → ℕ → Stmt where
  Div0 : ∀{y : ℕ} → y divides 𝟎
  Div𝐒 : ∀{x : ℕ}{y : ℕ} → (y divides x) → (y divides (y + x))

DivN : ∀{y : ℕ} → (n : ℕ) → y divides (y ⋅ n)
DivN {y}(𝟎)    = Div0
DivN {y}(𝐒(n)) = Div𝐒(DivN{y}(n))

divides-intro : ∀{x y} → (∃ \(n : ℕ) → (y ⋅ n ≡ x)) → (y divides x)
divides-intro {x}{y} ([∃]-intro (n) (y⋅n≡x)) = [≡]-elimᵣ (y⋅n≡x) {expr ↦ (y divides expr)} (DivN{y}(n))

data _divides_withRemainder_ : ℕ → ℕ → ℕ → Stmt where
  DivRem0 : ∀{x : ℕ}{r : ℕ} → x divides r withRemainder r
  DivRem𝐒 : ∀{x : ℕ}{y : ℕ}{r : ℕ} → (x divides y withRemainder r) → (x divides (x + y) withRemainder r)

-- Inequalities/Comparisons
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
