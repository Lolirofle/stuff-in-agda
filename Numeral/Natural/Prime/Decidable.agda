module Numeral.Natural.Prime.Decidable where

open import Data
open import Data.Boolean
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.List
open import Data.List.Decidable as List
open import Data.List.Equiv.Id
open import Functional
open import Lang.Inspect
open import Lang.Inspect
open import Logic.Classical
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Decidable
open import Numeral.Natural.LinearSearch
open import Numeral.Natural.LinearSearch.Proofs
open import Numeral.Natural.Oper.Divisibility
open import Numeral.Natural.Prime
open import Numeral.Natural.Prime.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Decidable
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Syntax.Implication using (•_•_⇒₂-[_]_)
open import Syntax.Implication.Dependent
open import Type.Properties.Decidable
open import Type.Properties.Decidable.Proofs

-- A naive primality test by bruteforcing.
-- It checks if there are any divisors between 2 and p.
-- Note: The performance and space should be terrible on this implementation because it checks whether the list of all divisors is empty.
prime? : ℕ → Bool
prime? 0          = 𝐹
prime? 1          = 𝐹
prime? n@(𝐒(𝐒 _)) = decide(2)(_≡_) ⦃ [∃]-intro _ ⦃ List.[≡]-decider ⦃ dec = [≡?]-decider ⦄ ⦄ ⦄ (findBoundedAll 2 n (_∣₀? n)) ∅

composite? : ℕ → Bool
composite? 0          = 𝐹
composite? 1          = 𝐹
composite? n@(𝐒(𝐒 _)) = not(prime? n)

instance
  Prime-decider : Decider(1)(Prime)(prime?)
  Prime-decider {𝟎} = false \()
  Prime-decider {𝐒 𝟎} = false \()
  Prime-decider {n@(𝐒(𝐒 x))} with prime? n | inspect prime? n
  ... | 𝑇 | intro eq = true $
    eq ⇒
    (prime? n ≡ 𝑇)                                     ⇒-[ [↔]-to-[←] IsTrue.is-𝑇 ]
    IsTrue(prime? n)                                   ⇒-[ [↔]-to-[←] (decider-true ⦃ List.[≡]-decider ⦃ dec = [≡?]-decider ⦄ ⦄) ]
    findBoundedAll 2 n (_∣₀? n) ≡ ∅                    ⇒-[ (\empty {_} → [↔]-to-[←] (findBoundedAll-emptyness{f = _∣₀? n}) empty) ]
    (∀{d} → (2 ≤ d) → (d < n) → IsFalse(d ∣₀? n))      ⇒-[ (\p {i} → [↔]-to-[←] (decider-false ⦃ [∣]-decider ⦄) ∘₂ p) ]
    (∀{d} → (2 ≤ d) → (d < n) → ¬(d ∣ n))              ⇒-[]
    (∀{d} → (2 ≤ d) → (d < 𝐒(𝐒(x))) → ¬(d ∣ 𝐒(𝐒(x))))  ⇒-[ (\p {d} div 2d dx → p{d} 2d (succ dx) div) ]
    (∀{d} → (d ∣ 𝐒(𝐒(x))) → (2 ≤ d) → ¬(d ≤ 𝐒(x)))     ⇒-[ (\p {d} div → [¬→]-disjunctive-formᵣ ⦃ decider-to-classical ⦃ [≡?]-decider ⦄ ⦄ \ nd0 → antisymmetry(_≤_)(_≡_) ([≤]-without-[𝐒] (divides-upper-limit div)) (sub₂(_≯_)(_≤_) (p{𝐒 d} div (succ ([≢]-to-[<]-of-0ᵣ nd0))))) ]
    (∀{d} → (𝐒(d) ∣ 𝐒(𝐒(x))) → ((d ≡ 0) ∨ (d ≡ 𝐒(x)))) ⇒-[ intro ]
    Prime n                                            ⇒-end
  ... | 𝐹 | intro eq = false \p →
    • (
      p ⇒
      Prime(n)                                      ⇒-[ prime-only-divisors ]
      (∀{d} → (d ∣ n) → ((d ≡ 1) ∨ (d ≡ n)))        ⇒-[ (\p {d} 2d dn div → [∨]-elim (\{[≡]-intro → [≤][0]ᵣ-negation ([≤]-without-[𝐒] 2d)}) (\{[≡]-intro → irreflexivity(_<_) dn}) (p div)) ]
      (∀{d} → (2 ≤ d) → (d < n) → ¬(d ∣ n))         ⇒-[ ((\p {i} → [↔]-to-[→] (decider-false ⦃ [∣]-decider ⦄) ∘₂ p)) ]
      (∀{d} → (2 ≤ d) → (d < n) → IsFalse(d ∣₀? n)) ⇒-[ [↔]-to-[→] findBoundedAll-emptyness ]
      findBoundedAll 2 n (_∣₀? n) ≡ ∅               ⇒-[ [↔]-to-[→] (decider-true ⦃ List.[≡]-decider ⦃ dec = [≡?]-decider ⦄ ⦄) ]
      IsTrue(prime? n)                              ⇒-end
    )
    • (
      eq ⇒
      (prime? n ≡ 𝐹)                    ⇒-[ [↔]-to-[←] IsFalse.is-𝐹 ]
      IsFalse(prime? n)                 ⇒-end
    )
    ⇒₂-[ disjointness ]
    Empty ⇒-end

import      Data.Either as Either
open import Data.List.Relation.Membership using (_∈_)
open import Data.List.Relation.Membership.Proofs
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Logic.Propositional.Theorems
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Proofs
open import Numeral.Natural.Relation.Order.Existence using ([≤]-equivalence)
open import Structure.Function.Domain
open import Structure.Operator
open import Structure.Operator.Properties
open import Syntax.Transitivity

prime-composite-not : ∀{n} → Prime(n) → Composite(n) → ⊥
prime-composite-not {.(𝐒(𝐒(a)) ⋅ 𝐒(𝐒(b)))} p (intro a b) =
  Either.map1
    (\())
    ((\()) ∘ cancellationₗ(_+_) {x = a} ∘ injective(𝐒) ∘ injective(𝐒))
    (prime-only-divisors p {𝐒(𝐒(a))} (divides-with-[⋅] {c = 𝐒(𝐒(b))} ([∨]-introₗ (reflexivity(_∣_)))))

-- Using Numeral.Natural.Decidable.prime?, when it is false, there is a divisor d between 2 and n for n. This means that (d ∣ n). Equivalently ∃(k ↦ d ⋅ k ≡ n). The proof of Composite uses these d and k.
-- TODO: Is this actually constructing the pair of the smallest and greatest divisor when the number is composite? Maybe separating the function that does this could be useful in the future?
abstract
  prime-or-composite : ∀{n} → ⦃ _ : IsTrue(n >? 1) ⦄ → Prime(n) ∨ Composite(n)
  prime-or-composite{𝐒(𝐒 n)} = [¬→]-disjunctive-formᵣ ⦃ decider-to-classical ⦃ Prime-decider ⦄ ⦄ $
    ¬ Prime(𝐒(𝐒(n)))                                                                ⇒-[ [↔]-to-[→] (decider-false ⦃ Prime-decider ⦄) ]
    IsFalse(prime? (𝐒(𝐒(n))))                                                       ⇒-[ [↔]-to-[←] (decider-false ⦃ List.[≡]-decider ⦃ dec = [≡?]-decider ⦄ ⦄) ]
    findBoundedAll 2 (𝐒(𝐒(n))) (_∣₀? 𝐒(𝐒(n))) ≢ ∅                                   ⇒-[ non-empty-inclusion-existence ]
    ∃(_∈ findBoundedAll 2 (𝐒(𝐒(n))) (_∣₀? 𝐒(𝐒(n))))                                 ⇒-[ [∃]-map-proof ([↔]-to-[→] (findBoundedAll-membership {f = _∣₀? 𝐒(𝐒(n))})) ]
    ∃(d ↦ (2 ≤ d) ∧ (d < 𝐒(𝐒(n))) ∧ IsTrue(d ∣₀? 𝐒(𝐒(n))))                          ⇒-[ [∃]-map-proof ([∧]-map id ([↔]-to-[←] (decider-true ⦃ [∣]-decider ⦄))) ]
    ∃(d ↦ (2 ≤ d) ∧ (d < 𝐒(𝐒(n))) ∧ (d ∣ 𝐒(𝐒(n))))                                  ⇒-[ (\{([∃]-intro (𝐒 𝟎) ⦃ [∧]-intro ([∧]-intro (succ()) _) _ ⦄) ; ([∃]-intro (𝐒(𝐒 d)) ⦃ [∧]-intro ([∧]-intro d2 dn) div ⦄) → [∃]-intro d ⦃ [∧]-intro dn div ⦄}) ]
    ∃(d ↦ (𝐒(𝐒(d)) < 𝐒(𝐒(n))) ∧ (𝐒(𝐒(d)) ∣ 𝐒(𝐒(n))))                                ⇒-[ (\{([∃]-intro d ⦃ [∧]-intro dn div ⦄) → [∃]-intro d ⦃ [∧]-intro dn ([∃]-intro div ⦃ divides-quotient-correctness {yx = div} ⦄) ⦄}) ]
    ∃(d ↦ (𝐒(𝐒(d)) < 𝐒(𝐒(n))) ∧ ∃{Obj = 𝐒(𝐒(d)) ∣ 𝐒(𝐒(n))}(q ↦ (𝐒(𝐒(d)) ⋅ divides-quotient q ≡ 𝐒(𝐒(n))))) ⇒-[ (\{([∃]-intro d ⦃ [∧]-intro dn ([∃]-intro q ⦃ prod ⦄) ⦄) → [∃]-intro (d , [∃]-witness ([↔]-to-[←] [≤]-equivalence (divides-quotient-composite (succ (succ min)) dn {q}))) ⦃ congruence₂-₂(_⋅_)(𝐒(𝐒(d))) (([∃]-proof ([↔]-to-[←] [≤]-equivalence (divides-quotient-composite (succ (succ min)) dn {q})))) 🝖 prod ⦄}) ]
    ∃{Obj = ℕ ⨯ ℕ}(\(a , b) → (𝐒(𝐒(a)) ⋅ 𝐒(𝐒(b)) ≡ 𝐒(𝐒(n))))                        ⇒-[ [↔]-to-[←] composite-existence ]
    Composite(𝐒(𝐒 n))                                                               ⇒-end

prime-xor-composite : ∀{n} → (n ≥ 2) → Prime(n) ⊕ Composite(n)
prime-xor-composite {.(𝐒(𝐒 _))} (succ(succ _)) = [⊕]-or-not-both prime-or-composite (Tuple.uncurry prime-composite-not)

non-prime-non-composite-condition : ∀{n} → ¬ Prime(n) → ¬ Composite(n) → (n < 2)
non-prime-non-composite-condition {𝟎}          _  _  = succ min
non-prime-non-composite-condition {𝐒 𝟎}        _  _  = succ(succ min)
non-prime-non-composite-condition {n@(𝐒(𝐒 _))} np nc with () ← [∨]-elim np nc (prime-or-composite{n})

instance
  Composite-decider : Decider(1)(Composite)(composite?)
  Composite-decider {𝟎}          = false \()
  Composite-decider {𝐒 𝟎}        = false \()
  Composite-decider {n@(𝐒(𝐒 x))} = [↔]-to-[→] (decider-relator ([⊕]-right-[↔] (prime-xor-composite (succ(succ min)))) [≡]-intro) (not-decider ⦃ Prime-decider ⦄)

open import Data.Tuple
open import Numeral.Natural.Inductions
open import Numeral.Natural.Oper.Proofs.Order
open import Structure.Relator.Ordering

abstract
  prime-factor-existence : ∀{n} → ⦃ _ : IsTrue(n >? 1) ⦄ → ∃(PrimeFactor(n))
  prime-factor-existence {𝐒(𝐒(n))} = Strict.Properties.wellfounded-induction(_<_) {P = \n → ∃(PrimeFactor(𝐒(𝐒(n))))} p {n} where
    p : ∀{n} → ({prev : ℕ} ⦃ _ : prev < n ⦄ → ∃(PrimeFactor (𝐒(𝐒 prev)))) → ∃(PrimeFactor(𝐒(𝐒 n)))
    p{n} prev with prime-or-composite{𝐒(𝐒(n))}
    ... | Either.Left  p = [∃]-intro (𝐒(𝐒(n))) ⦃ intro ⦃ p ⦄ ⦃ reflexivity(_∣_) ⦄ ⦄
    ... | Either.Right c
      with [∃]-intro(a , b) ⦃ p ⦄ ← [↔]-to-[→] composite-existence c
      with [∃]-intro d ⦃ pa ⦄ ← prev{a} ⦃ [≤]-without-[𝐒] ([≤]-without-[𝐒] (subtransitivityᵣ(_≤_)(_≡_) ([⋅]ₗ-strictly-growing {𝐒 a}{𝐒(𝐒(b))} (succ (succ min))) p)) ⦄
      = [∃]-intro d ⦃ divisor-primeFactors ([↔]-to-[→] divides-[⋅]-existence ([∃]-intro (𝐒(𝐒 b)) ⦃ p ⦄)) pa ⦄
