module Numeral.Natural.Function.PrimeDivisor.Proofs where

open import Data
open import Data.List
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Function.Divisor
open import Numeral.Natural.Function.Divisor.Proofs
open import Numeral.Natural.Function.PrimeDivisor
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Prime
open import Numeral.Natural.Prime.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Decidable
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator
open import Structure.Relator.Ordering
open import Structure.Relator.Properties
open import Syntax.Implication
open import Type
open import Type.Properties.Decidable.Proofs

private variable a b d n : ℕ

primeDivisors-intro : ∀{ℓ} → (P : ℕ → List(ℕ) → Type{ℓ})
                    → P(0)(∅)
                    → P(1)(∅)
                    → (∀{n} → ⦃ n2 : (n ≥ 2) ⦄
                      → let d = leastDivisor n
                            instance d-pos = leastDivisor-positive{n} ([↔]-to-[←] Positive-greater-than-zero ([≤]-predecessor n2))
                      in P(n ⌊/⌋ d)(primeDivisors(n ⌊/⌋ d)) → P(n)(d ⊰ primeDivisors(n ⌊/⌋ d))
                    )
                    → (∀{n} → P n (primeDivisors n))
primeDivisors-intro P p0 p1 pd {n} = Strict.Properties.wellfounded-recursion-intro(_<_) {rec = primeDivisorsRec}{φ = \{n} → P n} proof {n} where
  proof : (n : ℕ) → ({x : ℕ} ⦃ xy : x < n ⦄ → P(x)(primeDivisors x)) → (primeDivisors n ≡ primeDivisorsRec n (\x → primeDivisors x)) → P(n)(primeDivisors n)
  proof 0          prev [≡]-intro = p0
  proof 1          prev [≡]-intro = p1
  proof n@(𝐒(𝐒 _)) prev eq =
    let d = leastDivisor n
        instance
          pos-d : Positive(d)
          pos-d = leastDivisor-positive{n} <>
    in prev{(n ⌊/⌋ d) ⦃ pos-d ⦄} ⦃ [⌊/⌋]-ltₗ {n}{d} ⦃ [↔]-to-[→] decider-true (leastDivisor-range{n} (succ(succ min))) ⦄ ⦄ ⇒
    P (n ⌊/⌋ d) (primeDivisors(n ⌊/⌋ d)) ⇒-[ pd{n} ]
    P n (d ⊰ primeDivisors(n ⌊/⌋ d))     ⇒-[ substitute₂ᵣ(P) (symmetry(_≡_) eq) ]
    P n (primeDivisors n)                ⇒-end

import      Data.List.Functions as List
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Relation.Divisibility.Proofs.FlooredDivision
open import Structure.Operator
open import Syntax.Transitivity

primeDivisors-prime : AllElements Prime(primeDivisors n)
primeDivisors-prime = primeDivisors-intro(\_ l → AllElements Prime l) ∅ ∅ (\ ⦃ ord ⦄ prev → (leastDivisor-prime ord) AllElements.⊰ prev)

primeDivisors-divisors : AllElements(_∣ n) (primeDivisors n)
primeDivisors-divisors = primeDivisors-intro(\n l → AllElements(_∣ n) l) ∅ ∅ (\ ⦃ n2 ⦄ prev → leastDivisor-correctness AllElements.⊰ AllElements-fn (divides-without-divᵣ ⦃ leastDivisor-positive ([↔]-to-[←] Positive-greater-than-zero ([≤]-predecessor n2)) ⦄ leastDivisor-correctness) prev)

-- Alternative proof of the fundamental theorem of arithmetic.
product-primeDivisors-inverse : ⦃ Positive n ⦄ → (List.foldᵣ(_⋅_) 1 (primeDivisors n) ≡ n)
product-primeDivisors-inverse n@{𝐒 _} = primeDivisors-intro(\n l → ⦃ Positive n ⦄ → List.foldᵣ(_⋅_) 1 l ≡ n) (\ ⦃ ⦄) [≡]-intro \{n} ⦃ pos-n ⦄ eq →
  let
    instance
      leastDiv-pos : Positive(leastDivisor n)
      leastDiv-pos = leastDivisor-positive ([↔]-to-[←] Positive-greater-than-zero ([≤]-predecessor pos-n))
  in
    List.foldᵣ(_⋅_) 1 (leastDivisor n ⊰ primeDivisors((n ⌊/⌋ leastDivisor n) ⦃ _ ⦄)) 🝖[ _≡_ ]-[]
    leastDivisor n ⋅ List.foldᵣ(_⋅_) 1 (primeDivisors((n ⌊/⌋ leastDivisor n) ⦃ _ ⦄)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(leastDivisor n) (eq ⦃ [↔]-to-[→] ([⌊/⌋]-positive{n}) leastDivisor-order ⦄) ]
    leastDivisor n ⋅ (n ⌊/⌋ leastDivisor n) ⦃ _ ⦄                                    🝖[ _≡_ ]-[ [⋅][⌊/⌋]-inverseOperatorₗ leastDivisor-correctness ]
    n                                                                                🝖-end

open import Data.List.Relation.Permutation
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Prime.Proofs.Representation

primeDivisors-product-inverse : ∀{l} → AllElements Prime(l) → (primeDivisors(List.foldᵣ(_⋅_) 1 l) permutes l)
primeDivisors-product-inverse{l} ap = foldᵣ-primes-permutation{primeDivisors(List.foldᵣ(_⋅_) 1 l)}{l} primeDivisors-prime ap (product-primeDivisors-inverse ⦃ foldᵣ-property-all{P = Positive}{Q = Positive} [⋅]-positiveᵣ <> (AllElements-fn prime-positive ap) ⦄)

open import Data.List.Relation.Pairwise
open import Data.List.Sorting
open import Numeral.Natural.Oper.Comparisons

postulate primeDivisors-sorted : Sorted(_≤?_)(primeDivisors n)
{-primeDivisors-sorted = primeDivisors-intro(\_ → Sorted(_≤?_)) AdjacentlyPairwise.empty AdjacentlyPairwise.empty (\{n} → proof{n}) where
  proof : ∀{n} → ⦃ n2 : n ≥ 2 ⦄
          → Sorted(_≤?_)(primeDivisors((n ⌊/⌋ leastDivisor n) ⦃ _ ⦄))
          → Sorted(_≤?_)((leastDivisor n) ⊰ primeDivisors((n ⌊/⌋ leastDivisor n) ⦃ _ ⦄))
  proof {𝐒 𝟎} ⦃ succ () ⦄ s
  proof {𝐒 (𝐒 n)} ⦃ n2 ⦄ s = {!primeDivisors-intro(\_ → Sorted(_≤?_)) AdjacentlyPairwise.empty AdjacentlyPairwise.empty ?!}
  --step ⦃ ? ⦄ ⦃ ? ⦄
-}
