module Numeral.Rational.Proofs where

open import Data.Boolean.Stmt
import      Lvl
open import Numeral.Integer as ℤ using (ℤ)
import      Numeral.Integer.Oper as ℤ
import      Numeral.Integer.Relation as ℤ
open import Numeral.Integer.Proofs
open import Numeral.Natural as ℕ using (ℕ)
open import Numeral.Natural.Function.GreatestCommonDivisor
import      Numeral.Natural.Oper as ℕ
import      Numeral.Natural.Oper.Comparisons as ℕ
open import Numeral.Natural.Relation
open import Numeral.Rational
open import Type

open import Data
open import Functional
open import Logic.Propositional
open import Numeral.Natural.Coprime
open import Numeral.Natural.Coprime.Proofs
open import Numeral.Natural.Decidable
open import Numeral.Natural.Function.GreatestCommonDivisor.Proofs
open import Structure.Operator.Properties
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Syntax.Number
open import Type.Properties.Decidable.Proofs

NonZero : ℚ → Type
NonZero = ℤ.NonZero ∘ ℚ.numerator

fromCoprimePair : (x : ℤ) → (y : ℕ) → ⦃ pos : Positive(y) ⦄ → Coprime(ℤ.absₙ x)(y) → ℚ
fromCoprimePair x y cop = (x /ₙ y) ⦃ [↔]-to-[→] decider-true ([↔]-to-[→] Coprime-gcd cop) ⦄

fromℤ : ℤ → ℚ
fromℤ x = (x /ₙ 1) ⦃ [↔]-to-[→] decider-true (absorberᵣ(gcd)(1) {ℤ.absₙ x}) ⦄

fromℕ : ℕ → ℚ
fromℕ = fromℤ ∘ (ℤ.+ₙ_)

instance
  ℚ-InfiniteNegativeNumeral : InfiniteNegativeNumeral(ℚ)
  ℚ-InfiniteNegativeNumeral = InfiniteNegativeNumeral.intro(fromℤ ∘ (ℤ.−ₙ_))

instance
  ℚ-InfiniteNumeral : InfiniteNumeral(ℚ)
  ℚ-InfiniteNumeral = InfiniteNumeral.intro(fromℕ)

-- _/↓_ : ℤ → ℕ → ℚ
-- x /↓ y = (x ⌊/⌋ gcd x y) /ₙ (y ⌊/⌋ gcd x y)

{-
−_ : ℚ → ℚ
−(x /ₙ y) rewrite symmetry(_≡_) (absₙ-of-[−] {x}) = ((ℤ.− x) /ₙ y)

_+_ : ℚ → ℚ → ℚ
(x₁ /ₙ y₁) + (x₂ /ₙ y₂) = (((x₁ ℤ.⋅ (ℤ.+ₙ y₂)) ℤ.+ ((ℤ.+ₙ y₁) ℤ.⋅ x₂)) /ₙ (y₁ ℕ.⋅ y₂)) ⦃ {!!} ⦄ ⦃ {!!} ⦄

_−_ : ℚ → ℚ → ℚ
x − y = x + (− y)

⅟ : (x : ℚ) ⦃ nz : NonZero(x) ⦄ → ℚ
⅟ ((ℤ.+𝐒ₙ x) /ₙ y) = ((ℤ.+𝐒ₙ y) /ₙ x) ⦃ {!!} ⦄ ⦃ {!!} ⦄
⅟ ((ℤ.−𝐒ₙ x) /ₙ y) = ((ℤ.−𝐒ₙ y) /ₙ x) ⦃ {!!} ⦄ ⦃ {!!} ⦄

_⋅_ : ℚ → ℚ → ℚ
(x₁ /ₙ y₁) ⋅ (x₂ /ₙ y₂) = {!(x₁ ℤ.⋅ x₂) /ₙ (y₁ ℕ.⋅ y₂)!}

_/_ : ℚ → (y : ℚ) ⦃ nz : NonZero(y) ⦄ → ℚ
x / y = x ⋅ (⅟ y)

abs : ℚ → ℚ
abs(x /ₙ y) = (ℤ.abs(x) /ₙ y) ⦃ {!!} ⦄

test : ℚ
test = 256 /ₙ 3
-}

-- open import Numeral.Natural.Coprime
-- Coprime (absₙ numerator) denominator
