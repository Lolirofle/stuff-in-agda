module Numeral.Natural.Function.GreatestCommonDivisor.Relation.Existence where

open import Data
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Function.GreatestCommonDivisor
open import Numeral.Natural.Function.GreatestCommonDivisor.Relation.Proofs
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Proofs

private variable a b c d d₁ d₂ n a₁ a₂ b₁ b₂ : ℕ

-- Note: Alternative construction for the existence. it is following the same steps as in the definition of the function `gcd`, but unlike `gcd` which does not pass the termination checker, this uses ℕ-strong-induction to pass it.
Gcd-existence : ∃(Gcd a b)
Gcd-existence{a}{b} = ℕ-strong-induction(b ↦ ∀{a} → ∃(Gcd a b)) base step b {a} where
  base : ∀{a} → ∃(Gcd a 𝟎)
  base{a} = [∃]-intro a ⦃ Gcd-identityᵣ ⦄

  step : (i : ℕ) → ((j : ℕ) → (j ≤ i) → ∀{a} → ∃(Gcd a j)) → ∀{a} → ∃(Gcd a (𝐒(i)))
  step i prev {a} with [≥]-or-[<] {a}{𝐒(i)}
  ... | [∨]-introₗ ia = [∃]-map-proof (\{x} → Gcd-onₗ-mod ∘ Gcd-commutativity) (prev(a mod 𝐒(i)) ([≤]-without-[𝐒] (mod-maxᵣ{a}{𝐒(i)})) {𝐒(i)})
  ... | [∨]-introᵣ (succ ai) = [∃]-map-proof Gcd-commutativity(prev a ai {𝐒(i)})
