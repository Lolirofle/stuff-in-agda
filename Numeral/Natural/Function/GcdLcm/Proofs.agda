module Numeral.Natural.Function.GcdLcm.Proofs where

open import Functional
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Function.LeastCommonMultiple
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Function.GreatestCommonDivisor.Relation.Proofs
open import Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Relation.Divisibility as ℕ
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Syntax.Implication
open import Syntax.Transitivity

private variable a b c : ℕ

[⋅]-gcd-lcm : gcd a b ⋅ lcm a b ≡ a ⋅ b
[⋅]-gcd-lcm {a}{b} =
  Gcd.divisorₗ(Gcd-gcd{a}{b}) ⇒
  gcd a b ∣ a                                ⇒-[ divides-with-[⋅] {c = b} ∘ [∨]-introₗ ]
  gcd a b ∣ (a ⋅ b)                          ⇒-[ [⋅][⌊/⌋₀]-inverseOperatorₗ {a ⋅ b}{gcd a b} ]
  gcd a b ⋅ ((a ⋅ b) ⌊/⌋₀ (gcd a b)) ≡ a ⋅ b ⇒-[]
  gcd a b ⋅ lcm a b                  ≡ a ⋅ b ⇒-end
