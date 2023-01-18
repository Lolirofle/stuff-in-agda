module Numeral.Natural.Function.LeastCommonMultiple.Proofs where

open import Data
open import Data.Tuple
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Integer as ℤ using (+ₙ_)
import      Numeral.Integer.Oper as ℤ
import      Numeral.Integer.Oper.Proofs as ℤ
import      Numeral.Integer.Relation.Divisibility as ℤ
import      Numeral.Integer.Relation.Divisibility.Proofs as ℤ
open import Numeral.Natural
open import Numeral.Natural.Coprime
open import Numeral.Natural.Coprime.Proofs
open import Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Function.LeastCommonMultiple
open import Numeral.Natural.Function.LeastCommonMultiple.Relation.Proofs
open import Numeral.Natural.Function.GcdLcm.Proofs
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Function.GreatestCommonDivisor.Extended.Proofs
open import Numeral.Natural.Function.GreatestCommonDivisor.Relation.Proofs
open import Numeral.Natural.Function.GreatestCommonDivisor.Proofs
open import Numeral.Natural.Relation.Divisibility as ℕ
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs.FlooredDivision
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator
open import Structure.Relator.Properties
open import Syntax.Implication
open import Syntax.Transitivity
open import Syntax.Type
open import Type

private variable a b c : ℕ

lcm-absorberᵣ : lcm a 0 ≡ 0
lcm-absorberᵣ {a} =
  lcm a 0                🝖[ _≡_ ]-[]
  (a ⋅ 𝟎) ⌊/⌋₀ (gcd a 0) 🝖[ _≡_ ]-[]
  𝟎 ⌊/⌋₀ (gcd a 0)       🝖[ _≡_ ]-[ [⌊/⌋₀]-of-0ₗ {gcd a 0} ]
  𝟎                      🝖-end

Lcm-lcm : Lcm a b (lcm a b)
Lcm-lcm{a}{𝟎}       = substitute₁ₗ(Lcm a 0) (lcm-absorberᵣ{a}) Lcm-absorberᵣ
Lcm-lcm{a}{b@(𝐒 _)} = Lcm.intro₂
  (divides-[⋅]ᵣ⌊/⌋₀-transferᵣ {a}{a ℕ.⋅ b}{gcd a b} (divides-with-[⋅]ₗ-both {gcd a b}{b}{a} (Gcd.divisorᵣ {a}{b} Gcd-gcd)))
  (divides-[⋅]ₗ⌊/⌋₀-transferᵣ {b}{a ℕ.⋅ b}{gcd a b} (divides-with-[⋅]ᵣ-both {gcd a b}{a}{b} (Gcd.divisorₗ {a}{b} Gcd-gcd)))
  (\{m} am bm → let [∃]-intro (X , Y) ⦃ aXbY-gcd ⦄ = gcd-linearCombination-existence {a}{b} ; A = +ₙ a ; B = +ₙ b ; M = +ₙ m in
    • (
      • A ℤ.∣ (A ℤ.⋅ X)               :-[ ℤ.divides-[⋅]ₗ {A}{X} ]
      • B ℤ.∣ M                       :-[ bm ]
      ⇒₂-[ ℤ.divides-with-[⋅]-both {A}{B}{A ℤ.⋅ X}{M} ]
      (A ℤ.⋅ B) ℤ.∣ ((A ℤ.⋅ X) ℤ.⋅ M) ⇒-[ substitute₂-₂ᵣ(ℤ._∣_)(A ℤ.⋅ B) (commutativity(ℤ._⋅_) {A ℤ.⋅ X}{M}) ]
      (A ℤ.⋅ B) ℤ.∣ (M ℤ.⋅ (A ℤ.⋅ X)) ⇒-end
    )
    • (
      • A ℤ.∣ M                       :-[ am ]
      • B ℤ.∣ (B ℤ.⋅ Y)               :-[ ℤ.divides-[⋅]ₗ {B}{Y} ]
      ⇒₂-[ ℤ.divides-with-[⋅]-both {A}{B}{M}{B ℤ.⋅ Y} ]
      (A ℤ.⋅ B) ℤ.∣ (M ℤ.⋅ (B ℤ.⋅ Y)) ⇒-end
    )
    ⇒₂-[ ℤ.divides-with-[+] {A ℤ.⋅ B} {M ℤ.⋅ (A ℤ.⋅ X)} {M ℤ.⋅ (B ℤ.⋅ Y)} ]
    (A ℤ.⋅ B) ℤ.∣ ((M ℤ.⋅ (A ℤ.⋅ X)) ℤ.+ (M ℤ.⋅ (B ℤ.⋅ Y))) ⇒-[ substitute₂-₂ₗ(ℤ._∣_)(A ℤ.⋅ B) (distributivityₗ(ℤ._⋅_)(ℤ._+_) {M}) ]
    (A ℤ.⋅ B) ℤ.∣ (M ℤ.⋅ ((A ℤ.⋅ X) ℤ.+ (B ℤ.⋅ Y)))         ⇒-[ substitute₂-₂ᵣ(ℤ._∣_)(A ℤ.⋅ B) (congruence₂-₂(ℤ._⋅_)(M) aXbY-gcd) ]
    (A ℤ.⋅ B) ℤ.∣ (M ℤ.⋅ (+ₙ gcd a b))                      ⇒-[ substitute₂ₗ(ℤ._∣_) (preserving₂(+ₙ_)(ℕ._⋅_)(ℤ._⋅_) {a}{b}) (preserving₂(+ₙ_)(ℕ._⋅_)(ℤ._⋅_) {m}{gcd a b}) ]
    (a ⋅ b) ∣ (m ⋅ gcd a b)                                 ⇒-[ [↔]-to-[←] (divides-⌊/⌋₀[⋅]ᵣ-transfer ⦃ [∨]-introᵣ ([↔]-to-[→] (gcd-positive{a}{b}) ([∨]-introᵣ <>)) ⦄ (divides-with-[⋅] {gcd a b}{a}{b} ([∨]-introₗ (Gcd.divisorₗ Gcd-gcd)))) ]
    ((a ⋅ b) ⌊/⌋₀ gcd a b) ∣ m                              ⇒-[]
    (lcm a b) ∣ m                                           ⇒-end
  )

[⋅]-lcm-coprim : Coprime a b → (lcm a b ≡ a ⋅ b)
[⋅]-lcm-coprim {a}{b} coprim =
  lcm a b                🝖[ _≡_ ]-[ identityₗ(_⋅_)(𝟏) {lcm a b} ]-sym
  𝟏 ⋅ lcm a b            🝖[ _≡_ ]-[ congruence₂-₁(_⋅_)(lcm a b) ([↔]-to-[→] Coprime-gcd coprim) ]-sym
  gcd a b ⋅ lcm a b      🝖[ _≡_ ]-[ [⋅]-gcd-lcm {a}{b} ]
  a ⋅ b                  🝖-end

divides-[⋅]-lcm : lcm a b ∣ (a ⋅ b)
divides-[⋅]-lcm {a}{b} = Lcm.minimum₂(Lcm-lcm{a}{b})
  (divides-with-[⋅] {c = b} ([∨]-introₗ (reflexivity(_∣_))))
  (divides-with-[⋅] {b = a} ([∨]-introᵣ (reflexivity(_∣_))))
