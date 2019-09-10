module Numeral.FiniteInclusive where

import Lvl
open import Syntax.Number
open import Data.Boolean.Stmt
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
import      Numeral.Natural.Relation.Order
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Type

-- A structure corresponding to a finite set of natural numbers (0,..,n).
-- Specifically an upper bounded set of natural numbers, and the boundary is lesser than or equals the parameter.
-- Positive integers including zero less than a specified integer (0≤_≤n).
-- This structure works in the following way:
--   • 𝟎fin can always be constructed, for any upper bound (n).
--   • 𝐒fin can only be constructed from a smaller upper bounded 𝕟₌.
--       Example: A 𝕟₌ constructed through 𝐒fin{3} can only be the following:
--         0 ≡ 𝟎fin{3}
--         1 ≡ 𝐒fin{3} (𝟎fin{2})
--         2 ≡ 𝐒fin{3} (𝐒fin{2} (𝟎fin{1}))
--         3 ≡ 𝐒fin{3} (𝐒fin{2} (𝐒fin{1} (𝟎fin{0})))
--         because there is nothing that could fill the blank in (𝐒fin{3} (𝐒fin{2} (𝐒fin{1} (𝐒fin{0} (_))))).
--       The smallest upper bound that can be is 0 (from using ℕ and its definition).
--       This limits how many successors (𝐒fin) that can "fit".
data 𝕟₌ : ℕ → Set where
  𝟎fin : ∀{n} → 𝕟₌(n)              -- Zero
  𝐒fin : ∀{n} → 𝕟₌(n) → 𝕟₌(𝐒(n)) -- Successor function
{-# INJECTIVE 𝕟₌ #-}

[𝕟₌]-to-[ℕ] : ∀{n} → 𝕟₌(n) → ℕ
[𝕟₌]-to-[ℕ] (𝟎fin)    = 𝟎
[𝕟₌]-to-[ℕ] (𝐒fin(n)) = 𝐒([𝕟₌]-to-[ℕ] (n))

module _ {ℓ} where
  open Numeral.Natural.Relation.Order

  [ℕ]-to-[𝕟₌] : (x : ℕ) → ∀{n} → ⦃ _ : IsTrue(x ≤? n) ⦄ → 𝕟₌(n)
  [ℕ]-to-[𝕟₌] (𝟎)    {_}    ⦃ _ ⦄ = 𝟎fin
  [ℕ]-to-[𝕟₌] (𝐒(_)) {𝟎}    ⦃ ⦄
  [ℕ]-to-[𝕟₌] (𝐒(x)) {𝐒(n)} ⦃ p ⦄ = 𝐒fin([ℕ]-to-[𝕟₌] (x) {n} ⦃ p ⦄)

instance
  𝕟₌-from-ℕ : ∀{N} → Numeral(𝕟₌(N))
  Numeral.restriction-ℓ ( 𝕟₌-from-ℕ {N} ) = Lvl.𝟎
  Numeral.restriction   ( 𝕟₌-from-ℕ {N} ) (n) = IsTrue(n ≤? N) where
    open Numeral.Natural.Relation.Order
  num ⦃ 𝕟₌-from-ℕ {N} ⦄ (n) ⦃ proof ⦄ = [ℕ]-to-[𝕟₌] (n) {N} ⦃ proof ⦄ where

module Theorems{ℓ} where
  open import Numeral.Natural.Function
  open import Numeral.Natural.Function.Proofs
  open import Numeral.Natural.Oper
  open import Numeral.Natural.Oper.Proofs
  open        Numeral.Natural.Relation.Order
  open import Relator.Equals
  open import Relator.Equals.Proofs

  bound-𝐒 : ∀{n} → 𝕟₌(n) → 𝕟₌(𝐒(n))
  bound-𝐒 (𝟎fin)    = 𝟎fin
  bound-𝐒 (𝐒fin(n)) = 𝐒fin(bound-𝐒 (n))

  bound-[+] : ∀{n₁ n₂} → 𝕟₌(n₁) → 𝕟₌(n₁ + n₂)
  bound-[+] (𝟎fin) = 𝟎fin
  bound-[+] {𝐒(n₁)}{n₂}(𝐒fin(n)) =
    [≡]-substitutionₗ ([+1]-commutativity{n₁}{n₂}) {𝕟₌} (𝐒fin{n₁ + n₂}(bound-[+] {n₁}{n₂} (n)))

  bound-maxₗ : ∀{n₁ n₂} → 𝕟₌(n₁) → 𝕟₌(max n₁ n₂)
  bound-maxₗ {n₁}{n₂} (n) = [≡]-substitutionₗ (max-elementary{n₁}{n₂}) {𝕟₌} (bound-[+] {n₁}{n₂ −₀ n₁} (n))

  bound-maxᵣ : ∀{n₁ n₂} → 𝕟₌(n₂) → 𝕟₌(max n₁ n₂)
  bound-maxᵣ {n₁}{n₂} (n) = [≡]-substitutionᵣ (commutativity(_≡_) {n₂}{n₁}) {𝕟₌} (bound-maxₗ {n₂}{n₁} (n))

  instance
    bound-instance : ∀{n} → ⦃ _ : 𝕟₌(n) ⦄ → 𝕟₌(𝐒(n))
    bound-instance {n} ⦃ proof ⦄ = bound-𝐒 {n} (proof)

  instance
    postulate downscale-instance : ∀{n} → ⦃ nfin : 𝕟₌(𝐒(n)) ⦄ → ⦃ _ : IsTrue{ℓ}([𝕟₌]-to-[ℕ]{𝐒(n)}(nfin) ≤? n) ⦄ → 𝕟₌(n)
