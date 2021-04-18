module Numeral.Natural.Prime.Proofs.Size where

import      Lvl
open import Data.Either as Either using ()
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Decidable
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Prime
open import Numeral.Natural.Prime.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Decidable
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Structure.Relator.Properties
open import Syntax.Implication
open import Type
open import Type.Properties.Decidable.Proofs

-- There is always a greater prime number.
-- Note: This is a variant of Euclid's proof, using factorial instead of a list of all previous prime numbers.
-- Also called: Euclid's theorem, the infinitude of prime numbers (note that this does not actually state that they are infinite by the usual definition. It is intuitively implied).
-- TODO: So, which prime is this actually returning? The smallest? The answer depends on prime-factor-existence. It would be useful if it returned the least upper bound so that each prime is enumerated in this constructive proof (then the witnessing function results in a bijection between ℕ, and that would be nice). If not, an alternative would be to use this function to retrieve the maximal number for a linear upper bounded searchfor a prime greater than the given one.
prime-greater-existence : (n : ℕ) → ⦃ Prime(n) ⦄ → ∃(s ↦ Prime(s) ∧ (n < s))
prime-greater-existence n@(𝐒(𝐒(N))) ⦃ p ⦄ with prime-or-composite{𝐒(n !)} ⦃ [↔]-to-[→] decider-true (succ ([≤]-of-[!] {n})) ⦄
... | Either.Left  p₊ = [∃]-intro (𝐒(n !)) ⦃ [∧]-intro p₊ (succ ([⋅]ₗ-growing {𝐒(𝐒 N)}{𝐒(N)!} ([≤]-with-[⋅] {1}{1}{𝐒 N}{N !} (succ min) ([≤]-of-[!] {N})))) ⦄
... | Either.Right c₊
  with [∃]-intro d@(𝐒 D) ⦃ intro ⦃ d-prime ⦄ ⦃ d-factor ⦄ ⦄ ← prime-factor-existence {𝐒(n !)} ⦃ [↔]-to-[→] decider-true (succ ([≤]-of-[!] {n})) ⦄
  = [∃]-intro d ⦃ [∧]-intro d-prime (sub₂(_≱_)(_<_) ord) ⦄ where
    ord : ¬(n ≥ d)
    ord nd =
      • (
        nd ⇒
        (n ≥ d)     ⇒-[]
        (d ≤ n)     ⇒-[ divides-factorial {n}{D} ]
        (d ∣ (n !)) ⇒-end
      )
      • (
        d-factor ⇒
        (d ∣ 𝐒(n !))            ⇒-[]
        (d ∣ ((n !) + 1))       ⇒-[ divides-without-[+] {d}{n !}{1} ]
        ((d ∣ (n !)) ↔ (d ∣ 1)) ⇒-[ [↔]-to-[→] ]
        ((d ∣ (n !)) → (d ∣ 1)) ⇒-end
      )
      ⇒₂-[ apply ]
      (d ∣ 1) ⇒-[ [1]-only-divides-[1] ]
      (d ≡ 1) ⇒-[ subtransitivityᵣ(_≤_)(_≡_) (prime-lower-bound{d} d-prime) ]
      (2 ≤ 1) ⇒-[ (\{(succ())}) ]
      ⊥ ⇒-end

primeGreater : (∃ Prime) → (∃ Prime)
primeGreater ([∃]-intro n) = [∃]-map-proof [∧]-elimₗ (prime-greater-existence n)

ℕ-to-prime : ℕ → (∃ Prime) -- TODO: How to prove the injectivity of this?
ℕ-to-prime 𝟎     = [∃]-intro 2 ⦃ [2]-prime ⦄
ℕ-to-prime (𝐒 n) = primeGreater(ℕ-to-prime n)

prime-to-ℕ : (∃ Prime) → ℕ
prime-to-ℕ = [∃]-witness

open import Lang.Instance
open import Logic.Predicate.Equiv
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names

prime-to-ℕ-inj : Injective ⦃ [≡∃]-equiv ⦄ prime-to-ℕ
prime-to-ℕ-inj = intro (\{x}{y} → proof{x}{y}) where
  proof : Names.Injective ⦃ [≡∃]-equiv ⦄ prime-to-ℕ
  proof {x} {[∃]-intro .(prime-to-ℕ x)} [≡]-intro = [≡]-intro

{-prime-to-ℕ-surj : Surjective prime-to-ℕ
∃.witness (Surjective.proof prime-to-ℕ-surj {y}) = ℕ-to-prime y
∃.proof (Surjective.proof prime-to-ℕ-surj {𝟎}) = {!!}
∃.proof (Surjective.proof prime-to-ℕ-surj {𝐒 y}) = {!!}
-}
