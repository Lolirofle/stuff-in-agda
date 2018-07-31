module Numeral.Finite where

import Lvl
open import Syntax.Number
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
import      Numeral.Natural.Relation.Order
open import Structure.Function.Domain
open import Type

-- A structure corresponding to a finite set of natural numbers (0,..,n).
-- Specifically an upper bounded set of natural numbers, and the boundary is lesser than or equals the parameter.
-- Positive integers including zero less than a specified integer (0≤_≤n).
-- This structure works in the following way:
--   • 𝟎fin can always be constructed, for any upper bound (n).
--   • 𝐒fin can only be constructed from a smaller upper bounded ℕfin.
--       Example: A ℕfin constructed through 𝐒fin{3} can only be the following:
--         0 ≡ 𝟎fin{3}
--         1 ≡ 𝐒fin{3} (𝟎fin{2})
--         2 ≡ 𝐒fin{3} (𝐒fin{2} (𝟎fin{1}))
--         3 ≡ 𝐒fin{3} (𝐒fin{2} (𝐒fin{1} (𝟎fin{0})))
--         because there is nothing that could fill the blank in (𝐒fin{3} (𝐒fin{2} (𝐒fin{1} (𝐒fin{0} (_))))).
--       The smallest upper bound that can be is 0 (from using ℕ and its definition).
--       This limits how many successors (𝐒fin) that can "fit".
data ℕfin : ℕ → Set where
  𝟎fin : ∀{n} → ℕfin(n)              -- Zero
  𝐒fin : ∀{n} → ℕfin(n) → ℕfin(𝐒(n)) -- Successor function
{-# INJECTIVE ℕfin #-}

[ℕfin]-to-[ℕ] : ∀{n} → ℕfin(n) → ℕ
[ℕfin]-to-[ℕ] (𝟎fin)    = 𝟎
[ℕfin]-to-[ℕ] (𝐒fin(n)) = 𝐒([ℕfin]-to-[ℕ] (n))

module _ {ℓ} where
  open Numeral.Natural.Relation.Order{ℓ}

  [ℕ]-to-[ℕfin] : (x : ℕ) → ∀{n} → ⦃ _ : (x lteq2 n) ⦄ → ℕfin(n)
  [ℕ]-to-[ℕfin] (𝟎)    {_}    ⦃ _ ⦄ = 𝟎fin
  [ℕ]-to-[ℕfin] (𝐒(_)) {𝟎}    ⦃ ⦄
  [ℕ]-to-[ℕfin] (𝐒(x)) {𝐒(n)} ⦃ p ⦄ = 𝐒fin([ℕ]-to-[ℕfin] (x) {n} ⦃ p ⦄)

instance
  ℕfin-from-ℕ : ∀{N} → From-ℕsubset(ℕfin(N))
  From-ℕsubset.restriction ( ℕfin-from-ℕ {N} ) (n) = (n lteq2 N) where
    open Numeral.Natural.Relation.Order
  from-ℕsubset ⦃ ℕfin-from-ℕ {N} ⦄ (n) ⦃ proof ⦄ = [ℕ]-to-[ℕfin] (n) {N} ⦃ proof ⦄ where

module Theorems{ℓ} where
  open import Numeral.Natural.Function
  open import Numeral.Natural.Oper
  open import Numeral.Natural.Oper.Properties{ℓ}
  open        Numeral.Natural.Relation.Order{ℓ}
  open import Relator.Equals{ℓ}{Lvl.𝟎}
  open import Relator.Equals.Proofs{ℓ}{Lvl.𝟎}

  bound-𝐒 : ∀{n} → ℕfin(n) → ℕfin(𝐒(n))
  bound-𝐒 (𝟎fin)    = 𝟎fin
  bound-𝐒 (𝐒fin(n)) = 𝐒fin(bound-𝐒 (n))

  bound-[+] : ∀{n₁ n₂} → ℕfin(n₁) → ℕfin(n₁ + n₂)
  bound-[+] (𝟎fin) = 𝟎fin
  bound-[+] {𝐒(n₁)}{n₂}(𝐒fin(n)) =
    [≡]-substitutionₗ ([+1]-commutativity{n₁}{n₂}) {ℕfin} (𝐒fin{n₁ + n₂}(bound-[+] {n₁}{n₂} (n)))

  bound-maxₗ : ∀{n₁ n₂} → ℕfin(n₁) → ℕfin(max n₁ n₂)
  bound-maxₗ {n₁}{n₂} (n) = [≡]-substitutionₗ (Theorems.max-elementary{ℓ}{n₁}{n₂}) {ℕfin} (bound-[+] {n₁}{n₂ −₀ n₁} (n))

  bound-maxᵣ : ∀{n₁ n₂} → ℕfin(n₂) → ℕfin(max n₁ n₂)
  bound-maxᵣ {n₁}{n₂} (n) = [≡]-substitutionᵣ (Theorems.max-commutativity{ℓ}{n₂}{n₁}) {ℕfin} (bound-maxₗ {n₂}{n₁} (n))

  instance
    bound-instance : ∀{n} → ⦃ _ : ℕfin(n) ⦄ → ℕfin(𝐒(n))
    bound-instance {n} ⦃ proof ⦄ = bound-𝐒 {n} (proof)

  instance
    postulate downscale-instance : ∀{n} → ⦃ nfin : ℕfin(𝐒(n)) ⦄ → ⦃ _ : [ℕfin]-to-[ℕ]{𝐒(n)}(nfin) lteq2 n ⦄ → ℕfin(n)
