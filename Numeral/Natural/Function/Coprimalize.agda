module Numeral.Natural.Function.Coprimalize where

open import Data.Tuple
open import Numeral.Natural
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Oper.FlooredDivision

-- Two numbers without their common divisors (without their common primes).
-- This will result in two coprime numbers that have the same ratio as the original numbers.
-- Example:
--   168           = 2³⋅3⋅7
--   30            = 2⋅3⋅5
--   gcd(168 , 30) = 2⋅3
--   coprimalize(168 , 30) = (28 , 5)
coprimalize : (ℕ ⨯ ℕ) → (ℕ ⨯ ℕ)
coprimalize(x , y) = ((x ⌊/⌋₀ gcd(x)(y)) , (y ⌊/⌋₀ gcd(x)(y)))

-- TODO: Maybe prove something like (b ∣ a) → ((d ∣ (a / b)) ↔ ((d ∣ a) ∧ (d ∤ b))) if it holds? (20210728: Why? Where is this proof required?)
open import Functional
open import Logic.Propositional
open import Numeral.Natural.Coprime
open import Numeral.Natural.Function.GreatestCommonDivisor.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv

-- The resulting pair of numbers of coprimalize are coprime.
coprimalize-is-coprime : ∀{x y} → (Positive(x) ∨ Positive(y)) → uncurry Coprime(coprimalize(x , y))
coprimalize-is-coprime = [⌊/⌋₀]-gcd-coprime

open import Data
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Relator

-- A number from the result of coprimalize is positive when the original number is positive.
coprimalize-positive : ∀{x y} → let (px , py) = coprimalize(x , y) in (Positive(x) ↔ Positive(px)) ∧ (Positive(y) ↔ Positive(py))
coprimalize-positive {x}{y}
  = [∧]-intro
    ([↔]-intro
      (l{x}{y})
      (r{x}{y})
    )
    ([↔]-intro
      (l{y}{x} ∘ substitute₁(Positive) (congruence₂-₂(_⌊/⌋₀_)(y) (commutativity(gcd) {x}{y})))
      (substitute₁(Positive) (congruence₂-₂(_⌊/⌋₀_)(y) (commutativity(gcd) {y}{x})) ∘ r{y}{x})
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

open import Numeral.Natural.Oper
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
