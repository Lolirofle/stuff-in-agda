module Numeral.Natural.Prime where

import Lvl
open import Data.Boolean.Stmt
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Relator.Equals

PrimeProof : {_ : ℕ} → Stmt{Lvl.𝟎}
PrimeProof{n} = (∀{x} → (𝐒(x) ∣ 𝐒(𝐒(n))) → ((x ≡ 𝟎) ∨ (x ≡ 𝐒(n))))

-- A prime number is a number `n` in which its only divisors are `{1,n}`.
data Prime : ℕ → Stmt{Lvl.𝟎} where
  intro : ∀{n} → PrimeProof{n} → Prime(𝐒(𝐒(n)))

-- A composite number is a number which are the product of two numbers greater than or equals 2.
data Composite : ℕ → Stmt{Lvl.𝟎} where
  intro : (a b : ℕ) → Composite(𝐒(𝐒(a)) ⋅ 𝐒(𝐒(b)))

Composite-intro : (a b : ℕ) → ⦃ _ : IsTrue(a ≥? 2) ⦄ ⦃ _ : IsTrue(b ≥? 2) ⦄ → Composite(a ⋅ b)
Composite-intro (𝐒(𝐒 a)) (𝐒(𝐒 b)) = intro a b

-- PrimeFactor(n)(p) means that `p` is a prime factor of `n`.
-- A prime factor `p` of `n` is a prime number that divides `n`.
record PrimeFactor(n : ℕ) (p : ℕ) : Stmt{Lvl.𝟎} where
  constructor intro
  field
    ⦃ prime ⦄  : Prime(p)
    ⦃ factor ⦄ : (p ∣ n)

-- greater-prime-existence : ∀{p} → Prime(p) → ∃(p₂ ↦ Prime(p₂) ∧ (p₂ > p))

-- TODO: https://math.stackexchange.com/questions/2786458/a-formal-statement-of-the-fundamental-theorem-of-arithmetic
-- TODO: Needs to be a finite multiset of primes.
-- PrimeMultiset = Type{Lvl.𝟎}
-- PrimeMultiSet = ((p : ℕ) → ⦃ _ : Prime(p) ⦄ → ℕ)
