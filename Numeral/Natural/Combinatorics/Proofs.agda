module Numeral.Natural.Combinatorics.Proofs where

open import Functional
import      Lvl
open import Logic
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Combinatorics
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Oper.Proofs.Multiplication
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Relator.Equals.Proofs.Equiv
open import Structure.Setoid hiding (_≡_ ; _≢_)
open import Structure.Function.Domain
open import Structure.Function
open import Structure.Operator.Proofs.Util
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Transitivity
open import Type

factorial-non-zero : ∀{n} → ((n !) ≢ 𝟎)
factorial-non-zero {𝟎}   ()
factorial-non-zero {𝐒 n} p with [⋅]-product-is-0 {a = 𝐒 n}{b = n !} p
... | [∨]-introᵣ n!0 = factorial-non-zero {n} n!0

instance
  factorial-positive : ∀{n} → Positive(n !)
  factorial-positive {n} = non-zero-positive(factorial-non-zero {n})

-- Also called: Pascals's identity
𝑐𝐶-step : ∀{n k} → (𝑐𝐶 (𝐒(n)) (𝐒(k)) ≡ 𝑐𝐶 n k + 𝑐𝐶 n (𝐒(k)))
𝑐𝐶-step = [≡]-intro

𝑐𝐶-empty-subsets : ∀{n} → (𝑐𝐶 n 𝟎 ≡ 𝐒(𝟎))
𝑐𝐶-empty-subsets {𝟎}   = [≡]-intro
𝑐𝐶-empty-subsets {𝐒 n} = [≡]-intro

𝑐𝐶-singleton-subsets : ∀{n} → (𝑐𝐶 n (𝐒 𝟎) ≡ n)
𝑐𝐶-singleton-subsets {𝟎}   = [≡]-intro
𝑐𝐶-singleton-subsets {𝐒 n} = congruence₁(𝐒) (𝑐𝐶-singleton-subsets {n})
{-# REWRITE 𝑐𝐶-singleton-subsets #-}

𝑐𝐶-larger-subsets : ∀{n k} → (n < k) → (𝑐𝐶 n k ≡ 𝟎)
𝑐𝐶-larger-subsets {𝟎}         (succ _) = [≡]-intro
𝑐𝐶-larger-subsets {𝐒 n} {𝐒 k} (succ p)
  rewrite 𝑐𝐶-larger-subsets {n} {k} p
  rewrite 𝑐𝐶-larger-subsets {n} {𝐒 k} ([≤]-successor p)
  = [≡]-intro

𝑐𝐶-full-subsets : ∀{n} → (𝑐𝐶 n n ≡ 𝐒(𝟎))
𝑐𝐶-full-subsets {𝟎}   = [≡]-intro
𝑐𝐶-full-subsets {𝐒 n}
  rewrite 𝑐𝐶-full-subsets {n}
  rewrite 𝑐𝐶-larger-subsets {n}{𝐒 n} (reflexivity(_≤_))
  = [≡]-intro

𝑐𝐶-excluding-single-subsets : ∀{n} → (𝑐𝐶 (𝐒 n) n ≡ 𝐒(n))
𝑐𝐶-excluding-single-subsets {𝟎}   = [≡]-intro
𝑐𝐶-excluding-single-subsets {𝐒 n}
  rewrite 𝑐𝐶-excluding-single-subsets {n}
  rewrite 𝑐𝐶-full-subsets {n}
  rewrite 𝑐𝐶-larger-subsets {n}{𝐒 n} (reflexivity(_≤_))
  = [≡]-intro

{-
𝑐𝐶-test2 : ∀{k₁ k₂} → (𝑐𝐶 (𝐒(k₁ + k₂)) k₁ + 𝑐𝐶 (k₁ + k₂) (𝐒 k₁) ≡ 𝑐𝐶 (𝐒(k₁ + k₂)) k₂ + 𝑐𝐶 (k₁ + k₂) (𝐒 k₂))
𝑐𝐶-test2 {𝟎} {𝟎} = [≡]-intro
𝑐𝐶-test2 {𝟎} {𝐒 k₂}
  rewrite 𝑐𝐶-full-subsets {k₂}
  rewrite 𝑐𝐶-larger-subsets {k₂} (reflexivity(_≤_))
  rewrite 𝑐𝐶-larger-subsets {k₂} ([≤]-successor(reflexivity(_≤_)))
  rewrite 𝑐𝐶-excluding-single-subsets {k₂}
  = [≡]-intro
𝑐𝐶-test2 {𝐒 k₁} {𝟎}
  rewrite 𝑐𝐶-full-subsets {k₁}
  rewrite 𝑐𝐶-larger-subsets {k₁} (reflexivity(_≤_))
  rewrite 𝑐𝐶-larger-subsets {k₁} ([≤]-successor(reflexivity(_≤_)))
  rewrite 𝑐𝐶-excluding-single-subsets {k₁}
  = [≡]-intro
𝑐𝐶-test2 {𝐒 k₁} {𝐒 k₂}
  -- rewrite test2 {k₁ + k₂} {k₁} {k₂} [≡]-intro
  -- rewrite test2 {𝐒(k₁ + k₂)} {𝐒 k₁} {k₂} [≡]-intro
  -- rewrite test2 {𝐒(k₁ + k₂)} {k₁} {𝐒 k₂} [≡]-intro
  = {!!}

𝑐𝐶-symmetric : ∀{n k₁ k₂} → (k₁ + k₂ ≡ n) → (𝑐𝐶 n k₁ ≡ 𝑐𝐶 n k₂)
𝑐𝐶-symmetric {𝟎} {𝟎} {𝟎} x = [≡]-intro
𝑐𝐶-symmetric {𝐒 n} {𝟎} {𝐒 .n} [≡]-intro
  rewrite 𝑐𝐶-full-subsets {n}
  rewrite 𝑐𝐶-larger-subsets {n} (reflexivity(_≤_))
  = [≡]-intro
𝑐𝐶-symmetric {𝐒 n} {𝐒 .n} {𝟎} [≡]-intro
  rewrite 𝑐𝐶-full-subsets {n}
  rewrite 𝑐𝐶-larger-subsets {n} (reflexivity(_≤_))
  = [≡]-intro
𝑐𝐶-symmetric {𝐒 .(𝐒(k₁ + k₂))} {𝐒 k₁} {𝐒 k₂} [≡]-intro
  =
    𝑐𝐶 (𝐒(𝐒(k₁ + k₂))) (𝐒 k₁)                                    🝖[ _≡_ ]-[]
    𝑐𝐶 (𝐒(k₁ + k₂)) k₁ + 𝑐𝐶 (𝐒(k₁ + k₂)) (𝐒 k₁)                  🝖[ _≡_ ]-[]
    𝑐𝐶 (𝐒(k₁ + k₂)) k₁ + (𝑐𝐶 (k₁ + k₂) k₁ + 𝑐𝐶 (k₁ + k₂) (𝐒 k₁)) 🝖[ _≡_ ]-[ One.commuteₗ-assocᵣ {_▫_ = _+_}{a = 𝑐𝐶 (𝐒(k₁ + k₂)) k₁}{b = 𝑐𝐶 (k₁ + k₂) k₁}{c = 𝑐𝐶 (k₁ + k₂) (𝐒 k₁)} ]
    𝑐𝐶 (k₁ + k₂) k₁ + (𝑐𝐶 (𝐒(k₁ + k₂)) k₁ + 𝑐𝐶 (k₁ + k₂) (𝐒 k₁)) 🝖[ _≡_ ]-[ congruence₂(_+_) (𝑐𝐶-symmetric {k₁ + k₂} {k₁} {k₂} [≡]-intro) (𝑐𝐶-test2 {k₁}{k₂}) ]
    𝑐𝐶 (k₁ + k₂) k₂ + (𝑐𝐶 (𝐒(k₁ + k₂)) k₂ + 𝑐𝐶 (k₁ + k₂) (𝐒 k₂)) 🝖[ _≡_ ]-[ One.commuteₗ-assocᵣ {_▫_ = _+_}{a = 𝑐𝐶 (𝐒(k₁ + k₂)) k₂}{b = 𝑐𝐶 (k₁ + k₂) k₂}{c = 𝑐𝐶 (k₁ + k₂) (𝐒 k₂)} ]-sym
    𝑐𝐶 (𝐒(k₁ + k₂)) k₂ + (𝑐𝐶 (k₁ + k₂) k₂ + 𝑐𝐶 (k₁ + k₂) (𝐒 k₂)) 🝖[ _≡_ ]-[]
    𝑐𝐶 (𝐒(k₁ + k₂)) k₂ + 𝑐𝐶 (𝐒(k₁ + k₂)) (𝐒 k₂)                  🝖[ _≡_ ]-[]
    𝑐𝐶 (𝐒(𝐒(k₁ + k₂))) (𝐒 k₂)                                    🝖-end
-}


-- ∀{n k} → 𝑐𝐶 n k ≡ 𝑐𝐶 n (n−k)
-- ∀{n k} → 𝑐𝐶 (𝐒 n) (𝐒 k) ≡ 𝑐𝐶 n k ⋅ (𝐒 n) / (𝐒 k)
-- ∀{n} → (∑(𝟎 ‥ n) (𝑐𝐶 n) ≡ 2 ^ n)
-- ∀{n k} → (𝑐𝐶 (𝐒 n) (𝐒 k) ≡ ∑(0 ‥ n) (i ↦ 𝑐𝐶 i k) = ∑(k ‥ n) (i ↦ 𝑐𝐶 i k))

𝑐𝑃-empty : ∀{n} → (𝑐𝑃 n 𝟎 ≡ 𝐒(𝟎))
𝑐𝑃-empty {𝟎}   = [≡]-intro
𝑐𝑃-empty {𝐒 n} = [≡]-intro

𝑐𝑃-singleton : ∀{n} → (𝑐𝑃 n (𝐒 𝟎) ≡ n)
𝑐𝑃-singleton {𝟎}   = [≡]-intro
𝑐𝑃-singleton {𝐒 n} = [≡]-intro
{-# REWRITE 𝑐𝑃-singleton #-}

𝑐𝑃-step-diff : ∀{n k} → (𝑐𝑃 n k ⋅ n ≡ 𝑐𝑃 n k ⋅ k + 𝑐𝑃 n (𝐒 k)) -- TODO: Prove this for 𝑐𝐶 by using 𝑐𝐶-permutations-is-𝑐𝑃
𝑐𝑃-step-diff {𝟎} {𝟎} = [≡]-intro
𝑐𝑃-step-diff {𝟎} {𝐒 k} = [≡]-intro
𝑐𝑃-step-diff {𝐒 n} {𝟎} = [≡]-intro
𝑐𝑃-step-diff {𝐒 n} {𝐒 k} =
  𝑐𝑃 (𝐒 n) (𝐒 k) ⋅ (𝐒 n)                                      🝖[ _≡_ ]-[]
  (𝑐𝑃 n k ⋅ (𝐒 n)) ⋅ (𝐒 n)                                    🝖[ _≡_ ]-[]
  (𝑐𝑃 n k + 𝑐𝑃 n k ⋅ n) ⋅ (𝐒 n)                               🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) {x = 𝑐𝑃 n k}{y = 𝑐𝑃 n k ⋅ n}{z = 𝐒 n} ]
  (𝑐𝑃 n k ⋅ (𝐒 n)) + ((𝑐𝑃 n k ⋅ n) ⋅ (𝐒 n))                   🝖[ _≡_ ]-[ congruence₂(_+_) (reflexivity(_≡_) {x = 𝑐𝑃 (𝐒 n) (𝐒 k)}) proof1 ]
  𝑐𝑃 (𝐒 n) (𝐒 k) + ((𝑐𝑃 (𝐒 n) (𝐒 k) ⋅ k) + 𝑐𝑃 (𝐒 n) (𝐒(𝐒 k))) 🝖[ _≡_ ]-[ associativity(_+_) {x = 𝑐𝑃 (𝐒 n) (𝐒 k)}{y = 𝑐𝑃 (𝐒 n) (𝐒 k) ⋅ k}{z = 𝑐𝑃 (𝐒 n) (𝐒(𝐒 k))} ]-sym
  (𝑐𝑃 (𝐒 n) (𝐒 k) + (𝑐𝑃 (𝐒 n) (𝐒 k) ⋅ k)) + 𝑐𝑃 (𝐒 n) (𝐒(𝐒 k)) 🝖[ _≡_ ]-[]
  (𝑐𝑃 (𝐒 n) (𝐒 k) ⋅ 𝐒 k) + 𝑐𝑃 (𝐒 n) (𝐒(𝐒 k))                  🝖-end
  where
    proof2 =
      (𝑐𝑃 n k ⋅ k) ⋅ (𝐒 n) 🝖[ _≡_ ]-[ One.commuteᵣ-assocₗ {_▫_ = _⋅_}{a = 𝑐𝑃 n k}{b = k}{c = 𝐒 n} ]
      (𝑐𝑃 n k ⋅ (𝐒 n)) ⋅ k 🝖[ _≡_ ]-[]
      𝑐𝑃 (𝐒 n) (𝐒 k) ⋅ k   🝖-end

    proof1 =
      (𝑐𝑃 n k ⋅ n) ⋅ (𝐒 n)                          🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(𝐒 n) (𝑐𝑃-step-diff {n}{k}) ]
      (𝑐𝑃 n k ⋅ k + 𝑐𝑃 n (𝐒 k)) ⋅ (𝐒 n)             🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) {x = 𝑐𝑃 n k ⋅ k}{y = 𝑐𝑃 n (𝐒 k)}{z = 𝐒 n} ]
      ((𝑐𝑃 n k ⋅ k) ⋅ (𝐒 n)) + (𝑐𝑃 n (𝐒 k) ⋅ (𝐒 n)) 🝖[ _≡_ ]-[ congruence₂(_+_) proof2 (reflexivity(_≡_)) ]
      (𝑐𝑃 (𝐒 n) (𝐒 k) ⋅ k) + 𝑐𝑃 (𝐒 n) (𝐒(𝐒 k))      🝖-end

𝑐𝑃-step-alt : ∀{n k} → (𝑐𝑃 (𝐒 n) (𝐒 k) ≡ (𝑐𝑃 n k ⋅ 𝐒 k) + 𝑐𝑃 n (𝐒 k))
𝑐𝑃-step-alt {n}{k} rewrite 𝑐𝑃-step-diff {n}{k} = symmetry(_≡_) (associativity(_+_) {x = 𝑐𝑃 n k}{y = 𝑐𝑃 n k ⋅ k}{z = 𝑐𝑃 n (𝐒 k)})

𝑐𝐶-permutations-is-𝑐𝑃 : ∀{n k} → (𝑐𝐶 n k ⋅ (k !) ≡ 𝑐𝑃 n k)
𝑐𝐶-permutations-is-𝑐𝑃 {𝟎} {𝟎}     = [≡]-intro
𝑐𝐶-permutations-is-𝑐𝑃 {𝟎} {𝐒 k}   = [≡]-intro
𝑐𝐶-permutations-is-𝑐𝑃 {𝐒 n} {𝟎}   = [≡]-intro
𝑐𝐶-permutations-is-𝑐𝑃 {𝐒 n} {𝐒 k} =
  (𝑐𝐶 n k + 𝑐𝐶 n (𝐒 k)) ⋅ (𝐒 k ⋅ (k !))                   🝖-[ distributivityᵣ(_⋅_)(_+_) {x = 𝑐𝐶 n k}{y = 𝑐𝐶 n (𝐒 k)}{z = 𝐒 k ⋅ (k !)} ]
  (𝑐𝐶 n k ⋅ (𝐒 k ⋅ (k !))) + (𝑐𝐶 n (𝐒 k) ⋅ (𝐒 k ⋅ (k !))) 🝖-[ congruence₂(_+_) l r ]
  (𝑐𝑃 n k ⋅ 𝐒 k) + 𝑐𝑃 n (𝐒 k)                             🝖-[ 𝑐𝑃-step-alt {n}{k} ]-sym
  𝑐𝑃 n k ⋅ 𝐒 n                                            🝖-end
  where
    l =
      𝑐𝐶 n k ⋅ (𝐒 k ⋅ (k !)) 🝖-[ congruence₂ᵣ(_⋅_)(𝑐𝐶 n k) (commutativity(_⋅_) {𝐒 k}{k !}) ]
      𝑐𝐶 n k ⋅ ((k !) ⋅ 𝐒 k) 🝖-[ associativity(_⋅_) {x = 𝑐𝐶 n k}{y = k !}{z = 𝐒 k} ]-sym
      (𝑐𝐶 n k ⋅ (k !)) ⋅ 𝐒 k 🝖-[ congruence₂ₗ(_⋅_)(𝐒 k) (𝑐𝐶-permutations-is-𝑐𝑃 {n} {k}) ]
      𝑐𝑃 n k ⋅ 𝐒 k           🝖-end

    r =
      𝑐𝐶 n (𝐒 k) ⋅ (𝐒 k ⋅ (k !)) 🝖[ _≡_ ]-[]
      𝑐𝐶 n (𝐒 k) ⋅ ((𝐒 k)!)      🝖[ _≡_ ]-[ 𝑐𝐶-permutations-is-𝑐𝑃 {n} {𝐒 k} ]
      𝑐𝑃 n (𝐒 k)                 🝖-end

𝑐𝑃-full : ∀{n} → (𝑐𝑃 n n ≡ n !)
𝑐𝑃-full {n} =
  𝑐𝑃 n n         🝖[ _≡_ ]-[ 𝑐𝐶-permutations-is-𝑐𝑃 {n}{n} ]-sym
  𝑐𝐶 n n ⋅ (n !) 🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(n !) (𝑐𝐶-full-subsets {n}) ]
  𝐒(𝟎) ⋅ (n !)   🝖[ _≡_ ]-[]
  n !            🝖-end

𝑐𝐶-step-diff : ∀{n k} → (𝑐𝐶 n k ⋅ n ≡ (𝑐𝐶 n k ⋅ k) + (𝑐𝐶 n (𝐒 k) ⋅ (𝐒 k)))
𝑐𝐶-step-diff {n}{k} = [⋅]-cancellationᵣ {x = k !} ⦃ factorial-positive {k} ⦄ $
  (𝑐𝐶 n k ⋅ n) ⋅ (k !)                                  🝖[ _≡_ ]-[ One.commuteᵣ-assocₗ {_▫_ = _⋅_}{a = 𝑐𝐶 n k}{b = n}{c = k !} ]
  (𝑐𝐶 n k ⋅ (k !)) ⋅ n                                  🝖[ _≡_ ]-[ congruence₁(_⋅ n) (𝑐𝐶-permutations-is-𝑐𝑃 {n}{k}) ]
  𝑐𝑃 n k ⋅ n                                            🝖[ _≡_ ]-[ 𝑐𝑃-step-diff {n}{k} ]
  𝑐𝑃 n k ⋅ k + 𝑐𝑃 n (𝐒 k)                               🝖[ _≡_ ]-[ congruence₂(_+_) (congruence₁(_⋅ k) (symmetry(_≡_) (𝑐𝐶-permutations-is-𝑐𝑃 {n}{k}))) (symmetry(_≡_) (𝑐𝐶-permutations-is-𝑐𝑃 {n}{𝐒 k})) ]
  (𝑐𝐶 n k ⋅ (k !)) ⋅ k + (𝑐𝐶 n (𝐒 k) ⋅ ((𝐒 k) !))       🝖[ _≡_ ]-[]
  (𝑐𝐶 n k ⋅ (k !)) ⋅ k + (𝑐𝐶 n (𝐒 k) ⋅ ((𝐒 k) ⋅ (k !))) 🝖[ _≡_ ]-[ congruence₂(_+_) (One.commuteᵣ-assocₗ {_▫_ = _⋅_}{a = 𝑐𝐶 n k}{b = k !}{c = k}) (symmetry(_≡_) (associativity(_⋅_) {x = 𝑐𝐶 n (𝐒 k)}{y = 𝐒 k}{z = k !})) ]
  (𝑐𝐶 n k ⋅ k) ⋅ (k !) + ((𝑐𝐶 n (𝐒 k) ⋅ (𝐒 k)) ⋅ (k !)) 🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) {x = 𝑐𝐶 n k ⋅ k}{y = 𝑐𝐶 n (𝐒 k) ⋅ (𝐒 k)}{z = k !} ]-sym
  ((𝑐𝐶 n k ⋅ k) + (𝑐𝐶 n (𝐒 k) ⋅ (𝐒 k))) ⋅ (k !)         🝖-end

{-
-- Note: This is a variant of the usual definition of 𝑐𝐶 (The usual one: 𝑐𝐶 n k = (n !) / ((k !) ⋅ (n − k)!)).
factorial-of-[+] : ∀{k₁ k₂} → ((k₁ + k₂)! ≡ (k₁ !) ⋅ (k₂ !) ⋅ 𝑐𝐶 (k₁ + k₂) k₁)
factorial-of-[+] {𝟎} {k₂} = [≡]-intro
factorial-of-[+] {𝐒 k₁} {k₂} =
  ((𝐒(k₁) + k₂) !)                                 🝖[ _≡_ ]-[]
  (𝐒(k₁ + k₂) !)                                   🝖[ _≡_ ]-[]
  𝐒(k₁ + k₂) ⋅ ((k₁ + k₂) !)                       🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(𝐒(k₁ + k₂)) (factorial-of-[+] {k₁} {k₂}) ]
  𝐒(k₁ + k₂) ⋅ ((k₁ !) ⋅ (k₂ !) ⋅ 𝑐𝐶 (k₁ + k₂) k₁) 🝖[ _≡_ ]-[]
  (𝐒(k₁) + k₂) ⋅ ((k₁ !) ⋅ (k₂ !) ⋅ 𝑐𝐶 (k₁ + k₂) k₁) 🝖[ _≡_ ]-[ {!!} ]
  ((𝐒(k₁) + k₂) ⋅ (k₁ !)) ⋅ ((k₂ !) ⋅ 𝑐𝐶 (k₁ + k₂) k₁) 🝖[ _≡_ ]-[ {!!} ]
  ((𝐒(k₁) ⋅ (k₁ !)) + (k₂ ⋅ (k₁ !))) ⋅ ((k₂ !) ⋅ 𝑐𝐶 (k₁ + k₂) k₁) 🝖[ _≡_ ]-[ {!!} ]
  ((𝐒(k₁) !) + (k₂ ⋅ (k₁ !))) ⋅ ((k₂ !) ⋅ 𝑐𝐶 (k₁ + k₂) k₁) 🝖[ _≡_ ]-[ {!!} ]
  (𝐒(k₁) !) ⋅ (k₂ !) ⋅ 𝑐𝐶(𝐒(k₁) + k₂) (𝐒(k₁))      🝖-end

𝐒 k₁ ⋅ (k₁ !) ⋅ (k₂ !) ⋅ (𝑐𝐶 (k₁ + k₂) k₁ + 𝑐𝐶 (k₁ + k₂) (𝐒 k₁))
-}
{-factorial-of-[+] {𝟎} {𝟎} = [≡]-intro
factorial-of-[+] {𝟎} {𝐒 k₂} = [≡]-intro
factorial-of-[+] {𝐒 k₁} {𝟎}
  rewrite 𝑐𝐶-full-subsets {k₁}
  rewrite 𝑐𝐶-larger-subsets {k₁} {𝐒 k₁} (reflexivity(_≤_))
  = [≡]-intro
factorial-of-[+] {𝐒 k₁} {𝐒 k₂} = {!!}
𝐒(𝐒(k₁ + k₂)) ⋅ (𝐒(k₁ + k₂) ⋅ ((k₁ + k₂)!))
𝐒(𝐒(k₁ + k₂)) ⋅ (𝐒(k₁ + k₂) ⋅ ((k₁ !) ⋅ (k₂ !) ⋅ 𝑐𝐶 (k₁ + k₂) k₁))
𝐒(k₁) ⋅ (k₁ !) ⋅ (𝐒 k₂ ⋅ (k₂ !)) ⋅ (𝑐𝐶 (𝐒(k₁ + k₂)) k₁ + (𝑐𝐶 (k₁ + k₂) k₁ + 𝑐𝐶 (k₁ + k₂) (𝐒 k₁)))
-}

{-
-- Note: This is a variant of the usual definition of 𝑐𝑃 (The usual one: 𝑐𝑃 n k = (n !) / ((n − k)!)).
factorial-of-[+]-𝑐𝑃 : ∀{k₁ k₂} → ((k₁ + k₂)! ≡ 𝑐𝑃 (k₁ + k₂) k₂ ⋅ (k₁ !))
factorial-of-[+]-𝑐𝑃 {𝟎} {𝟎} = [≡]-intro
factorial-of-[+]-𝑐𝑃 {𝟎} {𝐒 k₂}
  rewrite 𝑐𝑃-full {k₂}
  =
    𝐒 k₂ ⋅ (k₂ !)        🝖[ _≡_ ]-[ commutativity(_⋅_) {𝐒 k₂}{k₂ !} ]
    (k₂ !) ⋅ 𝐒 k₂        🝖[ _≡_ ]-[]
    (k₂ !) + (k₂ !) ⋅ k₂ 🝖-end
factorial-of-[+]-𝑐𝑃 {𝐒 k₁} {𝟎} = [≡]-intro
factorial-of-[+]-𝑐𝑃 {𝐒 k₁} {𝐒 k₂} = {!!}
𝐒(𝐒(k₁ + k₂)) ⋅ (𝐒(k₁ + k₂) ⋅ ((k₁ + k₂)!))
𝐒(𝐒(k₁ + k₂)) ⋅ (𝐒(k₁ + k₂) ⋅ (𝑐𝑃 (k₁ + k₂) k₂ ⋅ (k₁ !)))
(𝑐𝑃 (𝐒(k₁ + k₂)) k₂ + (𝑐𝑃 (𝐒(k₁ + k₂)) k₂ + 𝑐𝑃 (𝐒(k₁ + k₂)) k₂ ⋅ (k₁ + k₂))) ⋅ (𝐒 k₁ ⋅ (k₁ !))
-}
