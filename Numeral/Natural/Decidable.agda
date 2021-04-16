module Numeral.Natural.Decidable where

open import Data
open import Data.Boolean
open import Functional
open import Lang.Inspect
open import Logic.Propositional
open import Numeral.Natural
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Relator.Properties
open import Type.Properties.Decidable

module _ where
  open import Numeral.Natural.Oper.Comparisons
  open import Numeral.Natural.Oper.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv

  instance
    [≡?]-decider : Decider(2)(_≡_)(_≡?_)
    [≡?]-decider {𝟎}   {𝟎}   = true [≡]-intro
    [≡?]-decider {𝟎}   {𝐒 y} = false \()
    [≡?]-decider {𝐒 x} {𝟎}   = false \()
    [≡?]-decider {𝐒 x} {𝐒 y} with (x ≡? y) | [≡?]-decider {x} {y}
    ... | 𝑇 | true  xy  = true  (congruence₁(𝐒) xy)
    ... | 𝐹 | false nxy = false (nxy ∘ injective(𝐒))

  zero?-decider : Decider(1)(_≡ 𝟎)(zero?)
  zero?-decider {𝟎}   = true [≡]-intro
  zero?-decider {𝐒 x} = false \()

module _ where
  open import Numeral.Natural.Oper.Comparisons
  open import Numeral.Natural.Oper.Proofs
  open import Numeral.Natural.Oper.Divisibility
  open import Numeral.Natural.Oper.Modulo
  open import Numeral.Natural.Oper.Modulo.Proofs
  open import Numeral.Natural.Relation.Divisibility
  open import Numeral.Natural.Relation.Divisibility.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv

  instance
    [∣]-decider : Decider(2)(_∣_)(_∣₀?_)
    [∣]-decider {𝟎} {𝟎}   = true Div𝟎
    [∣]-decider {𝟎} {𝐒 y} = false [0]-divides-not
    [∣]-decider {𝐒 x} {y} with y mod 𝐒(x) | inspect(\x → y mod 𝐒(x)) x
    ... | 𝟎   | intro eq = true  ([↔]-to-[→] mod-divisibility eq)
    ... | 𝐒 _ | intro eq = false ([𝐒]-not-0 ∘ transitivity(_≡_) (symmetry(_≡_) eq) ∘ [↔]-to-[←] mod-divisibility)

module _ where
  open import Data.Boolean.Stmt
  open import Data.Boolean.Stmt.Proofs
  open import Data.List
  open import Data.List.Decidable as List
  open import Data.List.Equiv.Id
  open import Lang.Inspect
  open import Logic.Classical
  open import Logic.Predicate
  open import Numeral.Natural.LinearSearch
  open import Numeral.Natural.Oper.Divisibility
  open import Numeral.Natural.Prime
  open import Numeral.Natural.Prime.Proofs
  open import Numeral.Natural.Relation.Divisibility
  open import Numeral.Natural.Relation.Divisibility.Proofs
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Classical
  open import Numeral.Natural.Relation.Order.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv
  open import Type.Properties.Decidable.Proofs
  open import Syntax.Implication.Dependent
  open import Syntax.Implication using (•_•_⇒₂-[_]_)

  -- A naive primality test using bruteforce.
  -- It checks if there are any divisors between 2 and p.
  -- Note: The performance and space should be terrible on this implementation because it checks whether the list of all divisors is empty.
  prime? : ℕ → Bool
  prime? 0          = 𝐹
  prime? 1          = 𝐹
  prime? n@(𝐒(𝐒 _)) = decide(2)(_≡_) ⦃ [∃]-intro _ ⦃ List.[≡]-decider ⦃ dec = [≡?]-decider ⦄ ⦄ ⦄ (findBoundedAll 2 n (_∣₀? n)) ∅

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
      (prime-only-divisors p {𝐒(𝐒(a))} (divides-with-[⋅] {c = 𝐒(𝐒(b))} ([∨]-introₗ divides-reflexivity)))

  -- Using Numeral.Natural.Decidable.prime?, when it is false, there is a divisor d between 2 and n for n. This means that (d ∣ n). Equivalently ∃(k ↦ d ⋅ k ≡ n). The proof of Composite uses these d and k.
  prime-or-composite : ∀{n} → Prime(𝐒(𝐒(n))) ∨ Composite(𝐒(𝐒(n)))
  prime-or-composite{n} = [¬→]-disjunctive-formᵣ ⦃ decider-to-classical ⦃ Prime-decider ⦄ ⦄ $
    ¬ Prime(𝐒(𝐒(n)))                                                                ⇒-[ [↔]-to-[→] (decider-false ⦃ Prime-decider ⦄) ]
    IsFalse(prime? (𝐒(𝐒(n))))                                                       ⇒-[ [↔]-to-[←] (decider-false ⦃ List.[≡]-decider ⦃ dec = [≡?]-decider ⦄ ⦄) ]
    findBoundedAll 2 (𝐒(𝐒(n))) (_∣₀? 𝐒(𝐒(n))) ≢ ∅                                   ⇒-[ non-empty-inclusion-existence ]
    ∃(_∈ findBoundedAll 2 (𝐒(𝐒(n))) (_∣₀? 𝐒(𝐒(n))))                                 ⇒-[ [∃]-map-proof ([↔]-to-[→] (findBoundedAll-membership {f = _∣₀? 𝐒(𝐒(n))})) ]
    ∃(d ↦ (2 ≤ d) ∧ (d < 𝐒(𝐒(n))) ∧ IsTrue(d ∣₀? 𝐒(𝐒(n))))                          ⇒-[ [∃]-map-proof ([∧]-map id ([↔]-to-[←] (decider-true ⦃ [∣]-decider ⦄))) ]
    ∃(d ↦ (2 ≤ d) ∧ (d < 𝐒(𝐒(n))) ∧ (d ∣ 𝐒(𝐒(n))))                                  ⇒-[ (\{([∃]-intro (𝐒 𝟎) ⦃ [∧]-intro ([∧]-intro (succ()) _) _ ⦄) ; ([∃]-intro (𝐒(𝐒 d)) ⦃ [∧]-intro ([∧]-intro d2 dn) div ⦄) → [∃]-intro d ⦃ [∧]-intro dn div ⦄}) ]
    ∃(d ↦ (𝐒(𝐒(d)) < 𝐒(𝐒(n))) ∧ (𝐒(𝐒(d)) ∣ 𝐒(𝐒(n))))                                ⇒-[ (\{([∃]-intro d ⦃ [∧]-intro dn div ⦄) → [∃]-intro d ⦃ [∧]-intro dn ([∃]-intro div ⦃ divides-quotient-correctness {yx = div} ⦄) ⦄}) ]
    ∃(d ↦ (𝐒(𝐒(d)) < 𝐒(𝐒(n))) ∧ ∃{Obj = 𝐒(𝐒(d)) ∣ 𝐒(𝐒(n))}(q ↦ (𝐒(𝐒(d)) ⋅ divides-quotient q ≡ 𝐒(𝐒(n))))) ⇒-[ (\{([∃]-intro d ⦃ [∧]-intro dn ([∃]-intro q ⦃ prod ⦄) ⦄) → [∃]-intro (d , [∃]-witness ([↔]-to-[←] [≤]-equivalence (divides-quotient-composite (succ (succ min)) dn {q}))) ⦃ congruence₂ᵣ(_⋅_)(𝐒(𝐒(d))) (([∃]-proof ([↔]-to-[←] [≤]-equivalence (divides-quotient-composite (succ (succ min)) dn {q})))) 🝖 prod ⦄}) ]
    ∃{Obj = ℕ ⨯ ℕ}(\(a , b) → (𝐒(𝐒(a)) ⋅ 𝐒(𝐒(b)) ≡ 𝐒(𝐒(n))))                        ⇒-[ [↔]-to-[←] composite-existence ]
    Composite(𝐒(𝐒 n))                                                               ⇒-end

  prime-xor-composite : ∀{n} → Prime(𝐒(𝐒(n))) ⊕ Composite(𝐒(𝐒(n)))
  prime-xor-composite {n} = [⊕]-or-not-both prime-or-composite (Tuple.uncurry prime-composite-not)

  open import Data.Tuple
  -- open import Numeral.Natural.Inductions
  {-# TERMINATING #-}
  -- TODO: Use strong induction. (a < n) because (a ⋅ b = n).
  prime-factor-existence : ∀{n} → ∃(PrimeFactor(𝐒(𝐒(n))))
  prime-factor-existence {n} with prime-or-composite{n}
  ... | Either.Left  p = [∃]-intro (𝐒(𝐒(n))) ⦃ intro ⦃ p ⦄ ⦄
  ... | Either.Right c
    with [∃]-intro(a , b) ⦃ p ⦄ ← [↔]-to-[→] composite-existence c
    with [∃]-intro d ⦃ pa ⦄ ← prime-factor-existence{a}
    = [∃]-intro d ⦃ divisor-primeFactors ([↔]-to-[→] divides-[⋅]-existence ([∃]-intro (𝐒 (𝐒 b)) ⦃ p ⦄)) pa ⦄
  
