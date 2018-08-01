module Numeral.Natural.Coprime{ℓ} where

import Lvl
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Relation.Divisibility{ℓ}
open import Numeral.Natural.Relation.Divisibility.Proofs{ℓ}
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Prime{ℓ}
open import Numeral.Natural.Relation.Order{ℓ}
open import Relator.Equals{ℓ}
open import Relator.Equals.Proofs{ℓ}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

-- Two numbers are coprime when their only divisor is 1.
Coprime : ℕ → ℕ → Stmt
Coprime(x)(y) = (∀{n} → (n ∣ x) → (n ∣ y) → (n ≡ 1))

Coprime-reflexivity-condition : ∀{n} → Coprime(n)(n) ↔ (n ≡ 1)
Coprime-reflexivity-condition {n} = [↔]-intro l (r{n}) where
  l : Coprime(n)(n) ← (n ≡ 1)
  l [≡]-intro {a} a1 _ = [1]-only-divides-[1] (a1)

  r : ∀{n} → Coprime(n)(n) → (n ≡ 1)
  r {𝟎}       z1   = z1 Div𝟎 Div𝟎
  r {𝐒(𝟎)}    _    = [≡]-intro
  r {𝐒(𝐒(n))} ssn1 = ssn1 {𝐒(𝐒(n))} divides-reflexivity divides-reflexivity

Coprime-symmetry : Symmetry(Coprime)
symmetry ⦃ Coprime-symmetry ⦄ (proof) {n} (nx) (ny) = proof {n} (ny) (nx)

Coprime-of-[0]ₗ-condition : ∀{x} → Coprime(0)(x) → (x ≡ 1)
Coprime-of-[0]ₗ-condition {0}       n1 = n1 Div𝟎 Div𝟎
Coprime-of-[0]ₗ-condition {1}       n1 = [≡]-intro
Coprime-of-[0]ₗ-condition {𝐒(𝐒(x))} n1 = n1 Div𝟎 divides-reflexivity

Coprime-of-[1]ₗ : ∀{x} → Coprime(1)(x)
Coprime-of-[1]ₗ {x}{n} n1 nx = [1]-only-divides-[1] n1

Coprime-with-[+] : ∀{x y} → Coprime(x)(y) → Coprime(x)(x + y)
Coprime-with-[+] {x}{y} proof {n} nx nxy = proof {n} nx (divides-without-[+]ᵣ nxy nx)

postulate Coprime-of-Prime : ∀{y} → Prime(y) → ∀{x} → (𝐒(x) < y) → Coprime(𝐒(x))(y)

-- _ : Coprime(x)(y) ↔ (gcd(x)(y) ≡ 1)

-- coprime : ℕ → ℕ → (ℕ ⨯ ℕ)
-- coprime(x)(y) = (x / gcd(x)(y) , y / gcd(x)(y))
