module Numeral.Natural.Function.Coprimalize.Proofs where

open import Data
open import Data.Tuple
open import Functional
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Numeral.Natural
open import Numeral.Natural.Coprime
open import Numeral.Natural.Coprime.Proofs
open import Numeral.Natural.Function.Coprimalize
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Function.GreatestCommonDivisor.Relation.Proofs
open import Numeral.Natural.Function.GreatestCommonDivisor.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator
open import Syntax.Implication

private variable a b x y : ℕ

-- TODO: Maybe prove something like (b ∣ a) → ((d ∣ (a / b)) ↔ ((d ∣ a) ∧ (d ∤ b))) if it holds? (20210728: Why? Where is this proof required?)

-- Two numbers without their common divisors are coprime.
-- gcd returns the product of all the common divisors (the greatest). Dividing the numbers by this product will therefore remove all the common divisors by division being an inverse.
[⌊/⌋₀]-gcd-coprime : ⦃ Positive(a) ∨ Positive(b) ⦄ → Coprime(a ⌊/⌋₀ gcd(a)(b)) (b ⌊/⌋₀ gcd(a)(b))
[⌊/⌋₀]-gcd-coprime {a}{b} ⦃ nz ⦄ =
  let d = gcd(a)(b)
      D = gcd(a ⌊/⌋₀ d) (b ⌊/⌋₀ d)
      gcd-D = Gcd-gcd {a ⌊/⌋₀ d} {b ⌊/⌋₀ d}
      instance d-pos = [↔]-to-[→] gcd-positive nz
  in
    • (
      Gcd.divisorₗ gcd-D ⇒
      (D ∣ (a ⌊/⌋₀ d))         ⇒-[ divides-with-[⋅]ᵣ-both {z = d} ]
      (D ⋅ d ∣ (a ⌊/⌋₀ d) ⋅ d) ⇒-[ substitute₂-₂ᵣ(_∣_) _ ([⋅][⌊/⌋₀]-inverseOperatorᵣ (gcd-dividesₗ {b = b})) ]
      (D ⋅ d ∣ a)              ⇒-[ substitute₂-₁ᵣ(_∣_) _ (commutativity(_⋅_) {D}{d}) ]
      (d ⋅ D ∣ a)              ⇒-end
    )
    • (
      Gcd.divisorᵣ gcd-D ⇒
      (D ∣ (b ⌊/⌋₀ d))         ⇒-[ divides-with-[⋅]ᵣ-both {z = d} ]
      (D ⋅ d ∣ (b ⌊/⌋₀ d) ⋅ d) ⇒-[ substitute₂-₂ᵣ(_∣_) _ ([⋅][⌊/⌋₀]-inverseOperatorᵣ (gcd-dividesᵣ {a = a})) ]
      (D ⋅ d ∣ b)              ⇒-[ substitute₂-₁ᵣ(_∣_) _ (commutativity(_⋅_) {D}{d}) ]
      (d ⋅ D ∣ b)              ⇒-end
    )
    ⇒₂-[ Gcd.maximum₂ Gcd-gcd ]
    ((d ⋅ D) ∣ d)                ⇒-[]
    ((d ⋅ D) ∣ (d ⋅ 1))          ⇒-[ divides-without-[⋅]ₗ-both' ]
    (D ∣ 1)                      ⇒-[ [1]-only-divides-[1] ]
    (D ≡ 1)                      ⇒-[ [↔]-to-[←] Coprime-gcd ]
    Coprime(a ⌊/⌋₀ d) (b ⌊/⌋₀ d) ⇒-end

[⌊/⌋]-gcd-coprime : ⦃ nz : Positive(a) ∨ Positive(b) ⦄ → Coprime((a ⌊/⌋ gcd(a)(b)) ⦃ [↔]-to-[→] gcd-positive nz ⦄) ((b ⌊/⌋ gcd(a)(b)) ⦃ [↔]-to-[→] gcd-positive nz ⦄)
[⌊/⌋]-gcd-coprime {a}{b} ⦃ nz ⦄ = substitute₂ᵣ(Coprime)
  ([⌊/⌋][⌊/⌋₀]-equality ⦃ [↔]-to-[→] gcd-positive nz ⦄)
  ([⌊/⌋][⌊/⌋₀]-equality ⦃ [↔]-to-[→] gcd-positive nz ⦄)
  ([⌊/⌋₀]-gcd-coprime ⦃ nz ⦄)

-- The resulting pair of numbers of coprimalize are coprime.
coprimalize-is-coprime : ⦃ Positive(x) ∨ Positive(y) ⦄ → uncurry Coprime(coprimalize(x , y))
coprimalize-is-coprime = [⌊/⌋₀]-gcd-coprime

-- A number from the result of coprimalize is positive when the original number is positive.
coprimalize-positive : ∀{x y} → let (px , py) = coprimalize(x , y) in (Positive(x) ↔ Positive(px)) ∧ (Positive(y) ↔ Positive(py))
coprimalize-positive {x}{y}
  = [∧]-intro
    ([↔]-intro
      (l{x}{y})
      (r{x}{y})
    )
    ([↔]-intro
      (l{y}{x} ∘ substitute₁ᵣ(Positive) (congruence₂-₂(_⌊/⌋₀_)(y) (commutativity(gcd) {x}{y})))
      (substitute₁ᵣ(Positive) (congruence₂-₂(_⌊/⌋₀_)(y) (commutativity(gcd) {y}{x})) ∘ r{y}{x})
    )
    where
      l : ∀{x y} → Positive(x) ← Positive(x ⌊/⌋₀ (gcd x y))
      l {𝟎}   {𝟎}   pos-gcd = pos-gcd
      l {𝟎}   {𝐒 y} pos-gcd = pos-gcd
      l {𝐒 x} {_}   _       = <>

      r : ∀{x y} → Positive(x) → Positive(x ⌊/⌋₀ (gcd x y))
      r{x}{y} pos-x =
        let instance gcd-pos = [↔]-to-[→] (gcd-positive{x}{y}) ([∨]-introₗ pos-x)
        in substitute₁ₗ(Positive)
          ([⌊/⌋][⌊/⌋₀]-equality {x}{gcd x y})
          ([↔]-to-[→] ([⌊/⌋]-positive {x}{gcd x y}) (divides-upper-limit ⦃ pos-x ⦄ (gcd-dividesₗ {b = y})))

open import Numeral.Natural.Oper.FlooredDivision.Proofs.Compatibility
open import Syntax.Transitivity

-- The resulting pair of numbers of coprimalize have the same quotient/ratio as the original nubmers.
coprimalize-quotient-equality : ∀{x y} ⦃ pos-y : Positive(y) ⦄ → (uncurry(_⌊/⌋₀_) (coprimalize(x , y)) ≡ (x ⌊/⌋₀ y))
coprimalize-quotient-equality {x}{y@(𝐒 Y)} =
  let
    instance pos-cy = [↔]-to-[→] ([∧]-elimᵣ (coprimalize-positive {x}{y})) <>
    eq =
      (x ⌊/⌋₀ (gcd x y)) ⋅ y 🝖[ _≡_ ]-[ [⌊/⌋₀][⋅]ₗ-compatibility {x}{y} (gcd-dividesₗ{x}{y}) ]-sym
      (x ⋅ y) ⌊/⌋₀ (gcd x y) 🝖[ _≡_ ]-[ [⌊/⌋₀][⋅]ᵣ-compatibility {x}{y} (gcd-dividesᵣ{x}{y}) ]
      x ⋅ (y ⌊/⌋₀ (gcd x y)) 🝖-end
  in [⌊/⌋][⌊/⌋₀]-equality ⦃ pos-cy ⦄ 🝖 [⌊/⌋]-equalityᵣ {x ⌊/⌋₀ (gcd x y)}{y ⌊/⌋₀ (gcd x y)}{x}{y} eq
