module Numeral.Natural.Function.GreatestCommonDivisor.Proofs.Distributivity where

open import Data
open import Functional
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Natural
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Function.GreatestCommonDivisor.Proofs
open import Numeral.Natural.Function.GreatestCommonDivisor.Relation.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Structure.Operator
open import Structure.Operator.Properties
open import Syntax.Transitivity

private variable a b c d d₁ d₂ n a₁ a₂ b₁ b₂ : ℕ

instance
  [⋅]-gcd-distributivityᵣ : Distributivityᵣ(_⋅_)(gcd)
  [⋅]-gcd-distributivityᵣ = intro(\{x}{y}{z} → proof{x}{y}{z}) where
    proof : (gcd(a)(b) ⋅ c ≡ gcd(a ⋅ c)(b ⋅ c))
    proof {a}{b}{𝟎}       = [≡]-intro
    proof {a}{b}{c@(𝐒 C)} =
      gcd a b ⋅ c                  🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(c) ([↔]-to-[→] Gcd-gcd-value (Gcd-without-[⋅]ᵣ {a}{b}{c}{gcd(a ⋅ c)(b ⋅ c) ⌊/⌋ c} ([↔]-to-[←] Gcd-gcd-value (symmetry(_≡_) q)))) ]
      gcd(a ⋅ c) (b ⋅ c) ⌊/⌋ c ⋅ c 🝖[ _≡_ ]-[ q ]
      gcd(a ⋅ c) (b ⋅ c)           🝖-end
      where q = [⋅][⌊/⌋]-inverseOperatorᵣ (gcd-divisors{(c)}{a ⋅ c}{b ⋅ c} (divides-with-[⋅] {c}{a} ([∨]-introᵣ (reflexivity(_∣_)))) (divides-with-[⋅]  {c}{b} ([∨]-introᵣ (reflexivity(_∣_)))))

instance
  [⋅]-gcd-distributivityₗ : Distributivityₗ(_⋅_)(gcd)
  Distributivityₗ.proof [⋅]-gcd-distributivityₗ {x}{y}{z} =
    x ⋅ gcd y z        🝖[ _≡_ ]-[ commutativity(_⋅_) {x}{gcd y z} ]
    gcd y z ⋅ x        🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(gcd) {y}{z}{x} ]
    gcd(y ⋅ x)(z ⋅ x)  🝖[ _≡_ ]-[ congruence₂(gcd) (commutativity(_⋅_) {y}{x}) (commutativity(_⋅_) {z}{x}) ]
    gcd(x ⋅ y)(x ⋅ z)  🝖-end

import      Numeral.Natural.Function as ℕ

gcd-of-powers-min : (gcd(n ^ a)(n ^ b) ≡ n ^ ℕ.min(a)(b))
gcd-of-powers-min {n}{𝟎}  {𝟎}   = [≡]-intro
gcd-of-powers-min {n}{𝟎}  {𝐒 b} = absorberₗ(gcd)(1) {n ^ 𝐒(b)}
gcd-of-powers-min {n}{𝐒 a}{𝟎}   = absorberᵣ(gcd)(1) {n ^ 𝐒(a)}
gcd-of-powers-min {n}{𝐒 a}{𝐒 b} =
  gcd (n ^ 𝐒(a)) (n ^ 𝐒(b))       🝖[ _≡_ ]-[]
  gcd (n ⋅ (n ^ a)) (n ⋅ (n ^ b)) 🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(gcd) {n}{n ^ a}{n ^ b} ]-sym
  n ⋅ gcd (n ^ a) (n ^ b)         🝖[ _≡_ ]-[ congruence₂-₂(_⋅_)(n) (gcd-of-powers-min {n}{a}{b}) ]
  n ⋅ n ^ ℕ.min(a)(b)             🝖[ _≡_ ]-[]
  n ^ 𝐒(ℕ.min(a)(b))              🝖[ _≡_ ]-[]
  n ^ ℕ.min(𝐒(a))(𝐒(b))           🝖-end
