module Numeral.Natural.Coprime.Proofs where

open import Functional
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Propositional.Theorems
import      Lvl
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Coprime
open import Numeral.Natural.Decidable
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Prime
open import Numeral.Natural.Prime.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Structure.Relator.Properties
open import Type.Properties.Decidable.Proofs
open import Type

private variable n x y d p : ℕ

-- 1 is the only number coprime to itself because it does not have any divisors except for itself.
Coprime-reflexivity-condition : Coprime(n)(n) ↔ (n ≡ 1)
Coprime-reflexivity-condition {n} = [↔]-intro l (r{n}) where
  l : Coprime(n)(n) ← (n ≡ 1)
  Coprime.proof(l [≡]-intro) {a} a1 _ = [1]-only-divides-[1] (a1)

  r : ∀{n} → Coprime(n)(n) → (n ≡ 1)
  r {𝟎}       (intro z1)   = z1 Div𝟎 Div𝟎
  r {𝐒(𝟎)}    _            = [≡]-intro
  r {𝐒(𝐒(n))} (intro ssn1) = ssn1 {𝐒(𝐒(n))} divides-reflexivity divides-reflexivity

instance
  Coprime-symmetry : Symmetry(Coprime)
  Coprime.proof(Symmetry.proof Coprime-symmetry (intro proof)) {n} nx ny = proof {n} ny nx

-- The only number coprime to 0 is 1 because while all numbers divide 0, only 1 divides 1.
Coprime-of-0-condition : ∀{x} → Coprime(0)(x) → (x ≡ 1)
Coprime-of-0-condition {0}       (intro n1) = n1 Div𝟎 Div𝟎
Coprime-of-0-condition {1}       (intro n1) = [≡]-intro
Coprime-of-0-condition {𝐒(𝐒(x))} (intro n1) = n1 Div𝟎 divides-reflexivity

-- 1 is coprime to all numbers because only 1 divides 1.
Coprime-of-1 : Coprime(1)(x)
Coprime.proof (Coprime-of-1 {x}) {n} n1 nx = [1]-only-divides-[1] n1

Coprime-of-[+] : Coprime(x)(y) → Coprime(x)(x + y)
Coprime.proof (Coprime-of-[+] {x}{y} (intro proof)) {n} nx nxy = proof {n} nx ([↔]-to-[→] (divides-without-[+] nxy) nx)

-- Coprimality is obviously equivalent to the greatest common divisor being 1 by definition.
Coprime-gcd : Coprime(x)(y) ↔ (gcd(x)(y) ≡ 1)
Coprime-gcd = [↔]-transitivity ([↔]-intro l r) Gcd-gcd-value where
  l : Coprime(x)(y) ← Gcd(x)(y) 1
  Coprime.proof (l p) nx ny = [1]-only-divides-[1] (Gcd.maximum₂ p nx ny)

  r : Coprime(x)(y) → Gcd(x)(y) 1
  Gcd.divisor(r (intro coprim)) 𝟎     = [1]-divides
  Gcd.divisor(r (intro coprim)) (𝐒 𝟎) = [1]-divides
  Gcd.maximum(r (intro coprim)) dv with [≡]-intro ← coprim (dv 𝟎) (dv(𝐒 𝟎)) = [1]-divides

-- A smaller number and a greater prime number is coprime.
-- If the greater number is prime, then no smaller number will divide it except for 1, and greater numbers never divide smaller ones.
-- Examples (y = 7):
--   The prime factors of 7 is only itself (because it is prime).
--   Then the only alternatives for x are:
--   x ∈ {1,2,3,4,5,6}
--   None of them is able to have 7 as a prime factor because it is greater:
--   1=1, 2=2, 3=3, 4=2⋅2, 5=5, 6=2⋅3
Coprime-of-Prime : (𝐒(x) < y) → Prime(y) → Coprime(𝐒(x))(y)
Coprime.proof (Coprime-of-Prime (succ(succ lt)) prim) nx ny with prime-only-divisors prim ny
Coprime.proof (Coprime-of-Prime (succ(succ lt)) prim) nx ny | [∨]-introₗ n1        = n1
Coprime.proof (Coprime-of-Prime (succ(succ lt)) prim) nx ny | [∨]-introᵣ [≡]-intro with () ← [≤]-to-[≯] lt ([≤]-without-[𝐒] (divides-upper-limit nx))

-- A prime number either divides a number or forms a coprime pair.
-- If a prime number does not divide a number, then it cannot share any divisors because by definition, a prime only has 1 as a divisor.
Prime-to-div-or-coprime : Prime(x) → ((x ∣ y) ∨ Coprime(x)(y))
Prime-to-div-or-coprime {y = y} (intro {x} prim) = [¬→]-disjunctive-formᵣ ⦃ decider-to-classical ⦄ (intro ∘ coprim) where
  coprim : (𝐒(𝐒(x)) ∤ y) → ∀{n} → (n ∣ 𝐒(𝐒(x))) → (n ∣ y) → (n ≡ 1)
  coprim nxy {𝟎}   nx ny with () ← [0]-divides-not nx
  coprim nxy {𝐒 n} nx ny with prim nx
  ... | [∨]-introₗ [≡]-intro = [≡]-intro
  ... | [∨]-introᵣ [≡]-intro with () ← nxy ny

divides-to-converse-coprime : ∀{x y z} → (x ∣ y) → Coprime(y)(z) → Coprime(x)(z)
divides-to-converse-coprime xy (intro yz) = intro(nx ↦ nz ↦ yz (transitivity(_∣_) nx xy) nz)
