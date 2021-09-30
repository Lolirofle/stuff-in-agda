module Numeral.Natural.Relation.Divisibility.Proofs.Product where

open import Data.Tuple
open import Functional
open import Logic
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Numeral.Integer
import      Numeral.Integer.Oper as ℤ
open import Numeral.Integer.Oper.Proofs
import      Numeral.Integer.Relation.Divisibility as ℤ
import      Numeral.Integer.Relation.Divisibility.Proofs as ℤ
open import Numeral.Natural
open import Numeral.Natural.Coprime
open import Numeral.Natural.Coprime.Proofs
open import Numeral.Natural.Function.GreatestCommonDivisor.Extended
open import Numeral.Natural.Oper
open import Numeral.Natural.Prime
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Implication
open import Syntax.Transitivity
open import Syntax.Type

private variable n x y d p x₁ x₂ y₁ y₂ : ℕ

-- When d and x does not have any common divisors, thus no common prime divisors, it means that all common prime divisors lies in d and y.
-- Also called: Generalized Euclid's lemma.
coprime-divides-of-[⋅] : (d ∣ (x ⋅ y)) → Coprime(d)(x) → (d ∣ y)
coprime-divides-of-[⋅] {d}{x}{y} dxy coprim
  with [∃]-intro (a , b) ⦃ p ⦄ ← gcd-linearCombination-existence {d}{x}
  = sub₂((ℤ._∣_) on₂ (+ₙ_))(_∣_) (substitute₂ᵣ(ℤ._∣_) {+ₙ d} eq div) where
    eq =
      ((+ₙ d) ℤ.⋅ a ℤ.⋅ (+ₙ y)) ℤ.+ ((+ₙ x) ℤ.⋅ b ℤ.⋅ (+ₙ y)) 🝖[ _≡_ ]-[ distributivityᵣ(ℤ._⋅_)(ℤ._+_) {(+ₙ d) ℤ.⋅ a}{(+ₙ x) ℤ.⋅ b}{+ₙ y} ]-sym
      (((+ₙ d) ℤ.⋅ a) ℤ.+ ((+ₙ x) ℤ.⋅ b)) ℤ.⋅ (+ₙ y)          🝖[ _≡_ ]-[ congruence₂ₗ(ℤ._⋅_)(+ₙ y) {_}{+ₙ 1} (p 🝖 congruence₁(+ₙ_) ([↔]-to-[→] Coprime-gcd coprim)) ]
      (+ₙ 1) ℤ.⋅ (+ₙ y)                                       🝖[ _≡_ ]-[ identityₗ(ℤ._⋅_)(+ₙ 1) ]
      (+ₙ y)                                                  🝖-end

    r-eq : (+ₙ(x ⋅ y)) ℤ.⋅ b ≡ (+ₙ x) ℤ.⋅ b ℤ.⋅ (+ₙ y)
    r-eq =
      (+ₙ (x ⋅ y)) ℤ.⋅ b        🝖[ _≡_ ]-[ congruence₂ₗ(ℤ._⋅_)(b) (preserving₂(+ₙ_)(_⋅_)(ℤ._⋅_)) ]
      ((+ₙ x) ℤ.⋅ (+ₙ y)) ℤ.⋅ b 🝖[ _≡_ ]-[ One.commuteᵣ-assocₗ {a = +ₙ x}{b = +ₙ y}{c = b} ]
      ((+ₙ x) ℤ.⋅ b) ℤ.⋅ (+ₙ y) 🝖-end

    div : (+ₙ d) ℤ.∣ ((+ₙ d) ℤ.⋅ a ℤ.⋅ (+ₙ y) ℤ.+ (+ₙ x) ℤ.⋅ b ℤ.⋅ (+ₙ y))
    div = ℤ.divides-with-[+] {+ₙ d}{(+ₙ d) ℤ.⋅ a ℤ.⋅ (+ₙ y)}{(+ₙ x) ℤ.⋅ b ℤ.⋅ (+ₙ y)}
      (ℤ.divides-with-[⋅] {+ₙ d}{(+ₙ d) ℤ.⋅ a} ([∨]-introₗ (ℤ.divides-with-[⋅] {+ₙ d}{+ₙ d} ([∨]-introₗ (reflexivity(_∣_))))))
      (substitute₂ᵣ(ℤ._∣_) {+ₙ d} r-eq (ℤ.divides-with-[⋅] {+ₙ d}{+ₙ(x ⋅ y)} ([∨]-introₗ dxy)))

coprime-divides-is-unit : (d ∣ x) → Coprime(d)(x) → (d ≡ 1)
coprime-divides-is-unit = [1]-only-divides-[1] ∘₂ coprime-divides-of-[⋅]

-- A prime number dividing a product means that the prime divides one of its factors.
-- Obvious intuitively because prime numbers are the "smallest units" in the context of divisibility.
-- Also called: Euclid's lemma.
prime-divides-of-[⋅] : Prime(p) → (p ∣ (x ⋅ y)) → ((p ∣ x) ∨ (p ∣ y))
prime-divides-of-[⋅] {p}{x}{y} prim pxy with Prime-to-div-or-coprime {y = x} prim
... | [∨]-introₗ div    = [∨]-introₗ div
... | [∨]-introᵣ coprim = [∨]-introᵣ (coprime-divides-of-[⋅] pxy coprim)

Coprime-of-[⋅] : ∀{x y z} → Coprime(x)(y) → Coprime(x)(z) → Coprime(x)(y ⋅ z)
Coprime-of-[⋅] {x}{y}{z} xy (intro xz) = intro (\{n} → nx ↦ nyz ↦ xz nx (coprime-divides-of-[⋅] {n}{y}{z} nyz (divides-to-converse-coprimeₗ nx xy)))

Coprime-of-[^]ₗ : Coprime(x)(y) ← Coprime(x)(y ^ 𝐒(n))
Coprime-of-[^]ₗ {x}{y}{ℕ.𝟎}   p         = p
Coprime-of-[^]ₗ {x}{y}{ℕ.𝐒 n} (intro p) = Coprime-of-[^]ₗ {n = n} (intro \{d} dx dyn → p dx (divides-with-[⋅] {d}{y}{y ^ 𝐒(n)} ([∨]-introᵣ dyn)))

Coprime-of-[^]ᵣ : Coprime(x)(y) → Coprime(x)(y ^ n)
Coprime-of-[^]ᵣ {x}{y}{ℕ.𝟎}   p = symmetry(Coprime) Coprime-of-1
Coprime-of-[^]ᵣ {x}{y}{ℕ.𝐒 n} p = Coprime-of-[⋅] p (Coprime-of-[^]ᵣ {n = n} p)

-- Coprime-[+][⋅] : Coprime(x)(y) ↔ Coprime(x + y)(x ⋅ y)
