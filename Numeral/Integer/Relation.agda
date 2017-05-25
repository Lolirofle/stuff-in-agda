module Numeral.Integer.Relation{lvl} where

open import Logic.Propositional{lvl}
open import Numeral.Integer
open import Numeral.Integer.Oper
import      Numeral.Natural.Relation as ℕ

-- Inequalities/Comparisons
data _≤_ : ℤ → ℤ → Stmt where
  [−]≤[+] : ∀{a b} → (−𝐒(a)) ≤ (+ b)
  [+]≤[+] : ∀{a b} → (a ℕ.≤ b) → (+ a)   ≤ (+ b)
  [-]≤[-] : ∀{a b} → (a ℕ.≤ b) → (−𝐒(b)) ≤ (−𝐒(a))

_<_ : ℤ → ℤ → Stmt
_<_ a b = (𝐒(a) ≤ b)

_≥_ : ℤ → ℤ → Stmt
_≥_ a b = (b ≤ a)

_>_ : ℤ → ℤ → Stmt
_>_ a b = (b < a)

_≰_ : ℤ → ℤ → Stmt
_≰_ a b = (a > b)

_≮_ : ℤ → ℤ → Stmt
_≮_ a b = (a ≥ b)

_≱_ : ℤ → ℤ → Stmt
_≱_ a b = (a < b)

_≯_ : ℤ → ℤ → Stmt
_≯_ a b = (a ≤ b)
