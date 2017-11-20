module Numeral.Integer.Relation{ℓ} where

open import Logic.Propositional{ℓ}
open import Numeral.Integer
open import Numeral.Integer.Oper
import      Numeral.Natural.Relation as ℕ

-- Inequalities/Comparisons
data _≤_ : ℤ → ℤ → Stmt where
  [−]≤[+] : ∀{a b} → (−𝐒ₙ(a)) ≤ (+ₙ b)
  [+]≤[+] : ∀{a b} → (ℕ._≤_ {ℓ} a b) → (+ₙ a)   ≤ (+ₙ b)
  [-]≤[-] : ∀{a b} → (ℕ._≤_ {ℓ} a b) → (−𝐒ₙ(b)) ≤ (−𝐒ₙ(a))

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
