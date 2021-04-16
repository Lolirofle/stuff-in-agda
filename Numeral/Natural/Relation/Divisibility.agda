module Numeral.Natural.Relation.Divisibility where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Type

-- Divisibility relation of natural numbers.
-- `(y ∣ x)` means that `y` is divisible by `x`.
-- In other words: `x/y` is an integer.
-- Or: `∃(c: ℕ). x = c⋅y`.
-- Note on the definition of Div𝐒:
--   The order (y + x) works and depends on rewriting rules of ℕ at the moment (Specifically on the commuted identity and successor rules, I think).
--   Without rewriting rules, deconstruction of Div𝐒 seems not working.
--   Example:
--     div23 : ¬(2 ∣ 3)
--     div23(Div𝐒())
--     This is a "valid" proof, but would not type-check because deconstruction from (2 ∣ 3) to (2 ∣ 1) is impossible.
--     Seems like the compiler would see (3 = 2+x), but because of definition of (_+_), only (3 = x+2) can be found.
--   Defining Div𝐒 with (x + y) inside would work, but then the definition of DivN becomes more complicated because (_⋅_) is defined in this order.
-- Note on zero divisors:
--   (0 ∣ 0) is true, and it is the only number divisible by 0.
-- Example definitions of special cases of the divisibility relation and the divisibility with remainder relation:
--   data Even : ℕ → Stmt{Lvl.𝟎} where
--     Even0 : Even(𝟎)
--     Even𝐒 : ∀{x : ℕ} → Even(x) → Even(𝐒(𝐒(x)))
--   data Odd : ℕ → Stmt{Lvl.𝟎} where
--     Odd0 : Odd(𝐒(𝟎))
--     Odd𝐒 : ∀{x : ℕ} → Odd(x) → Odd(𝐒(𝐒(x)))
data _∣_ : ℕ → ℕ → Stmt{Lvl.𝟎} where
  Div𝟎 : ∀{y}   → (y ∣ 𝟎)
  Div𝐒 : ∀{y x} → (y ∣ x) → (y ∣ (y + x))

_∤_ : ℕ → ℕ → Stmt
y ∤ x = ¬(y ∣ x)

-- `Divisor(n)(d)` means that `d` is a divisor of `n`.
Divisor = swap(_∣_)

-- `Multiple(n)(m)` means that `m` is a multiple of `n`.
Multiple = _∣_

-- Elimination rule for (_∣_).
divides-elim : ∀{ℓ}{P : ∀{y x} → (y ∣ x) → Type{ℓ}} → (∀{y} → P(Div𝟎{y})) → (∀{y x}{p : y ∣ x} → P(p) → P(Div𝐒 p)) → (∀{y x} → (p : y ∣ x) → P(p))
divides-elim        z s Div𝟎     = z
divides-elim{P = P} z s (Div𝐒 p) = s(divides-elim{P = P} z s p)
