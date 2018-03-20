module Numeral.Natural.Coprime{ℓ} where

import Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ}
open import Logic.Predicate{ℓ}{Lvl.𝟎}
open import Numeral.Natural
open import Numeral.Natural.Divisibility{ℓ}
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ}
open import Numeral.Natural.Prime{ℓ}
open import Numeral.Natural.Relation{ℓ}
open import Relator.Equals{ℓ}
open import Relator.Equals.Theorems{ℓ}
open import Structure.Operator.Properties{ℓ}{Lvl.𝟎}
open import Structure.Relator.Properties{ℓ}{Lvl.𝟎}
open import Type

-- Two numbers are coprime when their only divisor is 1.
Coprime : ℕ → ℕ → Stmt
Coprime(x)(y) = (∀{n} → (n ∣ x) → (n ∣ y) → (n ≡ 1))

postulate Coprime-reflexivity-condition : ∀{n} → Coprime(n)(n) ↔ (n ≡ 1)
postulate Coprime-symmetry : Symmetry(Coprime)

postulate Coprime-of-[0]ₗ-condition : ∀{n} → Coprime(0)(n) → (n ≡ 1)
postulate Coprime-of-[1]ₗ : ∀{n} → Coprime(1)(n)
postulate Coprime-with-[+] : ∀{x y} → Coprime(x)(y) → Coprime(x)(x + y)

postulate Coprime-of-Prime : ∀{y} → Prime(y) → ∀{x} → (𝐒(x) < y) → Coprime(𝐒(x))(y)

-- coprime : ℕ → ℕ → (ℕ ⨯ ℕ)
-- coprime(x)(y) = (x / gcd(x)(y) , y / gcd(x)(y))
