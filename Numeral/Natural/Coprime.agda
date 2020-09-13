module Numeral.Natural.Coprime where

import Lvl
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Logic
open import Numeral.Natural
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Prime
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type

-- Two numbers are coprime when their only divisor is 1.
record Coprime (x : ℕ) (y : ℕ) : Stmt{Lvl.𝟎} where
  constructor intro
  field proof : ∀{n} → (n ∣ x) → (n ∣ y) → (n ≡ 1)

Coprime-reflexivity-condition : ∀{n} → Coprime(n)(n) ↔ (n ≡ 1)
Coprime-reflexivity-condition {n} = [↔]-intro l (r{n}) where
  l : Coprime(n)(n) ← (n ≡ 1)
  Coprime.proof(l [≡]-intro) {a} a1 _ = [1]-only-divides-[1] (a1)

  r : ∀{n} → Coprime(n)(n) → (n ≡ 1)
  r {𝟎}       (intro z1)   = z1 Div𝟎 Div𝟎
  r {𝐒(𝟎)}    _            = [≡]-intro
  r {𝐒(𝐒(n))} (intro ssn1) = ssn1 {𝐒(𝐒(n))} divides-reflexivity divides-reflexivity

Coprime-symmetry : Symmetry(Coprime)
Coprime.proof(Symmetry.proof Coprime-symmetry (intro proof)) {n} (nx) (ny) = proof {n} (ny) (nx)

Coprime-of-[0]ₗ-condition : ∀{x} → Coprime(0)(x) → (x ≡ 1)
Coprime-of-[0]ₗ-condition {0}       (intro n1) = n1 Div𝟎 Div𝟎
Coprime-of-[0]ₗ-condition {1}       (intro n1) = [≡]-intro
Coprime-of-[0]ₗ-condition {𝐒(𝐒(x))} (intro n1) = n1 Div𝟎 divides-reflexivity

Coprime-of-[1]ₗ : ∀{x} → Coprime(1)(x)
Coprime.proof (Coprime-of-[1]ₗ {x}) {n} n1 nx = [1]-only-divides-[1] n1

Coprime-with-[+] : ∀{x y} → Coprime(x)(y) → Coprime(x)(x + y)
Coprime.proof (Coprime-with-[+] {x}{y} (intro proof)) {n} nx nxy = proof {n} nx (divides-without-[+]ᵣ nxy nx)

postulate Coprime-of-Prime : ∀{y} → Prime(y) → ∀{x} → (𝐒(x) < y) → Coprime(𝐒(x))(y)

-- _ : Coprime(x)(y) ↔ (gcd(x)(y) ≡ 1)

-- coprime : ℕ → ℕ → (ℕ ⨯ ℕ)
-- coprime(x)(y) = (x / gcd(x)(y) , y / gcd(x)(y))

{-
-- Also called: Euclid's lemma
divides-coprime-product : ∀{a b c} → Coprime(b)(c) → (a ∣ (b ⋅ c)) → ((a ∣ b) ∨ (a ∣ c))
divides-coprime-product co-bc abc = {!!}
-}
