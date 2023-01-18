module Numeral.Natural.Function.Divisor.Proofs where

open import Numeral.Natural
open import Numeral.Natural.Function.Divisor
open import Numeral.Natural.LinearSearch
open import Numeral.Natural.Oper.Divisibility

open import Data
open import Data.Boolean.Stmt
open import Data.Boolean.Stmt.Logic
open import Data.Option
open import Functional
open import Lang.Inspect
open import Logic.Classical
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.Propositional.Theorems
open import Numeral.Natural.LinearSearch.Proofs
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Decidable
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Divisibility.Proofs.Productᵣ
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Classical
open import Numeral.Natural.Relation.Order.Decidable
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Natural.Relation.Proofs
open import Numeral.Natural.Prime
open import Numeral.Natural.Prime.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Syntax.Implication
open import Type.Properties.Decidable.Proofs

private variable a b d n D : ℕ

-- The least divisor is a divisor.
-- This is also a construction for the proof that there is a divisor for every number.
leastDivisor-correctness : (leastDivisor n ∣ n)
leastDivisor-correctness {0}        = Div𝟎
leastDivisor-correctness {1}        = Div𝐒 Div𝟎
leastDivisor-correctness n@{𝐒(𝐒 _)} with findBoundedMin 2 n (_∣₀? n) | inspect (findBoundedMin 2 n) (_∣₀? n)
... | None   | _        = reflexivity(_∣_)
... | Some d | intro eq = [↔]-to-[←] decider-true ([∧]-elimₗ ([∧]-elimₗ ([↔]-to-[→] (findBoundedMin-Some-correctness{2}{n}{_∣₀? n}) eq)))

-- The least divisor is the smallest divisor.
leastDivisor-minimal : (2 ≤ d) → (d ∣ n) → (leastDivisor n ≤ d)
leastDivisor-minimal {d} {0}        range div = min
leastDivisor-minimal {d} {1}        range div = [≤]-predecessor range
leastDivisor-minimal {d} n@{𝐒(𝐒 _)} range div with findBoundedMin 2 n (_∣₀? n) | inspect (findBoundedMin 2 n) (_∣₀? n)
... | None   | intro eq =
  div ⇒
  (d ∣ n)             ⇒-[ [↔]-to-[→] decider-true ]
  IsTrue(d ∣₀? n)     ⇒-[ [↔]-to-[→] true-false-opposites ]
  ¬ IsFalse(d ∣₀? n)  ⇒-[ contrapositiveᵣ ([↔]-to-[→] (findBoundedMin-None-correctness{2}{n}{_∣₀? n}) eq) ]
  ¬(2 ≤ d < n)        ⇒-[ [¬]-preserves-[∧][∨]ᵣ ⦃ decider-classical(2 ≤ d) ⦄ ⦃ decider-classical(d < n) ⦄ ]
  ((2 ≰ d) ∨ (d ≮ n)) ⇒-[ [∨]-elim2 (sub₂(_≰_)(_>_)) (sub₂(_≮_)(_≥_)) ]
  ((2 > d) ∨ (d ≥ n)) ⇒-[ [∨]-elim ([⊥]-elim ∘ [≤]-to-[≯] range) id ]
  (n ≤ d)             ⇒-end
... | Some m | intro eq =
  • (range ⇒
    (2 ≤ d) ⇒-end
  )
  • (div ⇒
    (d ∣ n)         ⇒-[ [↔]-to-[→] decider-true ]
    IsTrue(d ∣₀? n) ⇒-end
  ) ⇒₂-[ [∧]-elimᵣ ([↔]-to-[→] (findBoundedMin-Some-correctness{2}{n}{_∣₀? n}) eq) ]
  (m ≤ d) ⇒-end

-- The least divisor is positive when the number is positive.
leastDivisor-positive : Positive(n) → Positive(leastDivisor n)
leastDivisor-positive {1}        pos = pos
leastDivisor-positive n@{𝐒(𝐒 _)} _   with findBoundedMin 2 n (_∣₀? n) | inspect (findBoundedMin 2 n) (_∣₀? n)
... | None   | _        = <>
... | Some d | intro eq = [↔]-to-[←] Positive-greater-than-zero ([≤]-predecessor ([∧]-elimₗ ([∧]-elimᵣ ([∧]-elimₗ ([↔]-to-[→] (findBoundedMin-Some-correctness{2}{n}{_∣₀? n}) eq)))))

-- The least divisor is greater than 1 when the number is greater than 1.
leastDivisor-range : (2 ≤ n) → (2 ≤ leastDivisor n)
leastDivisor-range n@{.(𝐒 (𝐒 _))} (succ (succ range)) with findBoundedMin 2 n (_∣₀? n) | inspect (findBoundedMin 2 n) (_∣₀? n)
... | None   | _        = succ(succ min)
... | Some d | intro eq = [∧]-elimₗ ([∧]-elimᵣ ([∧]-elimₗ ([↔]-to-[→] (findBoundedMin-Some-correctness{2}{n}{_∣₀? n}) eq)))

leastDivisor-when-0 : (leastDivisor n ≡ 0) → (n ≡ 0)
leastDivisor-when-0 {0}        eq = eq
leastDivisor-when-0 {1}        eq = eq
leastDivisor-when-0 n@{𝐒(𝐒 _)} eq with () ← subtransitivityᵣ(_≤_)(_≡_) (leastDivisor-range {n} (succ(succ min))) eq

leastDivisor-when-1 : (leastDivisor n ≡ 1) → (n ≡ 1)
leastDivisor-when-1 {1}        eq = eq
leastDivisor-when-1 n@{𝐒(𝐒 _)} eq with succ() ← subtransitivityᵣ(_≤_)(_≡_) (leastDivisor-range {n} (succ(succ min))) eq

-- The least divisor is always prime.
-- If the least divisor were composite, it would have strictly smaller components which would be divisors, and this contradicts the fact that the least divisor is the smallest.
leastDivisor-prime : (2 ≤ n) → Prime(leastDivisor n)
leastDivisor-prime {n} range = prime-when-only-divisors (leastDivisor-range range) p where
  p : (d ∣ leastDivisor n) → (d ≡ 1) ∨ (d ≡ leastDivisor n)
  p {0}      div = [∨]-introᵣ (symmetry(_≡_) ([0]-only-divides-[0] div))
  p {1}      div = [∨]-introₗ (reflexivity(_≡_))
  p {𝐒(𝐒 d)} div = [∨]-introᵣ
    (antisymmetry(_≤_)(_≡_)
      (divides-upper-limit ⦃ leastDivisor-positive ([↔]-to-[←] Positive-greater-than-zero ([≤]-predecessor range)) ⦄ div)
      (leastDivisor-minimal{n = n} (succ(succ min)) (transitivity(_∣_) div leastDivisor-correctness) )
    )

leastDivisor-small-or-prime : (n < 2) ∨ Prime(leastDivisor n)
leastDivisor-small-or-prime {0}           = [∨]-introₗ (succ min)
leastDivisor-small-or-prime {1}           = [∨]-introₗ (succ(succ min))
leastDivisor-small-or-prime {n@(𝐒(𝐒(_)))} = [∨]-introᵣ (leastDivisor-prime{n} (succ(succ min)))

leastDivisor-when-fixpoint : (leastDivisor n ≡ n) ↔ ((n < 2) ∨ Prime(n))
leastDivisor-when-fixpoint = [↔]-intro l r where
  l : (leastDivisor n ≡ n) ← ((n < 2) ∨ Prime(n))
  l {n}        ([∨]-introᵣ prim) = [∨]-elim
    ([⊥]-elim ∘ [≤][0]ᵣ-negation ∘ [≤]-without-[𝐒] ∘ (subtransitivityᵣ(_≤_)(_≡_) (prime-lower-bound prim)) ∘ leastDivisor-when-1 {n})
    id
    (prime-only-divisors prim {leastDivisor n} leastDivisor-correctness)
  l {0}        ([∨]-introₗ range) = [≡]-intro
  l {1}        ([∨]-introₗ range) = [≡]-intro
  l n@{𝐒(𝐒 _)} ([∨]-introₗ (succ(succ())))

  r : (leastDivisor n ≡ n) → ((n < 2) ∨ Prime(n))
  r {0}        eq = [∨]-introₗ (succ min)
  r {1}        eq = [∨]-introₗ (succ (succ min))
  r n@{𝐒(𝐒 _)} eq = [∨]-introᵣ (prime-when-only-divisors{n} (succ(succ min)) p) where
    p : (d ∣ n) → (d ≡ 1) ∨ (d ≡ n)
    p {0}      dn with () ← [0]-divides-not dn
    p {1}      dn = [∨]-introₗ [≡]-intro
    p {𝐒(𝐒 d)} dn = [∨]-introᵣ
      (antisymmetry(_≤_)(_≡_)
        (divides-upper-limit dn)
        (subtransitivityₗ(_≤_)(_≡_) (symmetry(_≡_) eq) (leastDivisor-minimal (succ(succ min)) dn))
      )

leastDivisor-order : (leastDivisor n ≤ n)
leastDivisor-order {𝟎}   = min
leastDivisor-order {𝐒 n} = divides-upper-limit leastDivisor-correctness

open import Numeral.Natural.Prime.Decidable
leastDivisor-strict-order : (leastDivisor n < n) ↔ ((n ≥ 2) ∧ Composite(n))
leastDivisor-strict-order{n} =
  leastDivisor n < n           ⇔-[ [↔]-intro ([≤][≢]-to-[<] leastDivisor-order) [<]-to-[≢] ]
  leastDivisor n ≢ n           ⇔-[ [¬]-unaryOperator leastDivisor-when-fixpoint ]
  ¬((n < 2) ∨ Prime n)         ⇔-[ [¬]-unaryOperator ([↔]-intro ([∨]-elim ([∨]-introₗ ∘ sub₂(_≱_)(_<_)) ([¬→]-disjunctive-formᵣ ⦃ decider-to-classical ⦄ ∘ (_∘ sub₂(_≮_)(_≥_)) ∘ swap([⊕]-not-not-left ∘ prime-xor-composite))) ([∨]-elim ([∨]-introₗ ∘ [<]-to-[≱]) ([→]-disjunctive-formᵣ ⦃ decider-to-classical ⦄ ∘ swap([⊕]-not-left ∘ prime-xor-composite)))) ]
  ¬(¬(n ≥ 2) ∨ ¬(Composite n)) ⇔-[ [¬]-unaryOperator ([¬]-preserves-[∧][∨] ⦃ decider-to-classical ⦄ ⦃ decider-to-classical ⦄) ]-sym
  ¬¬((n ≥ 2) ∧ (Composite n))  ⇔-[ double-negation ⦃ [∧]-classical-intro ⦃ decider-to-classical ⦄ ⦃ decider-to-classical ⦄ ⦄ ]-sym
  (n ≥ 2) ∧ Composite n        ⇔-end

open import Numeral.Natural.Decidable
open import Numeral.Natural.Oper.Comparisons

leastDivisor-eq2 : ⦃ IsTrue(D ≥? 2) ⦄ → ⦃ IsTrue(n ≥? 2) ⦄ → (D ∣ n) → (∀{d} → (2 ≤ d < n) → (d ∣ n) → (D ≤ d)) → (leastDivisor n ≡ D)
leastDivisor-eq2 D@{𝐒(𝐒 _)} n@{𝐒(𝐒 _)} div mini with findBoundedMin 2 n (_∣₀? n) | inspect (findBoundedMin 2 n) (_∣₀? n)
... | Some x | intro eq =
  let [∧]-intro ([∧]-intro divt bound) mini2 = [↔]-to-[→] (findBoundedMin-Some-correctness{2}{n}{_∣₀? n}) eq
  in antisymmetry(_≤_)(_≡_) (mini2 (succ(succ min)) ([↔]-to-[→] decider-true div)) (mini bound ([↔]-to-[←] decider-true divt))
... | None   | intro eq with excluded-middle(D ≡ n) ⦃ decider-classical(D ≡ n) ⦄
...   | [∨]-introₗ Dn  = symmetry(_≡_) Dn
...   | [∨]-introᵣ nDn = [⊥]-elim ([↔]-to-[←] (decider-false{P = D ∣ n}{b = D ∣? n}) ([↔]-to-[→] (findBoundedMin-None-correctness{2}{n}{_∣₀? n}) eq {D} ([∧]-intro (succ(succ min)) ([≤][≢]-to-[<] (divides-upper-limit div) nDn))) div)

leastDivisor-eq : (D ∣ n) → (∀{d} → (d ∣ n) → (D ≤ d)) → (leastDivisor n ≡ D) ∨ ((D ≡ 1) ∧ (n ≥ 2))
leastDivisor-eq            {n = 0}    div mini = [∨]-introₗ (symmetry(_≡_) ([≤][0]ᵣ (mini{𝟎} Div𝟎)))
leastDivisor-eq            {n = 1}    div mini = [∨]-introₗ (symmetry(_≡_) ([1]-only-divides-[1] div))
leastDivisor-eq {0}        n@{𝐒(𝐒 _)} div mini with () ← [0]-divides-not div
leastDivisor-eq {1}        n@{𝐒(𝐒 _)} div mini = [∨]-introᵣ([∧]-intro [≡]-intro (succ(succ min)))
leastDivisor-eq D@{𝐒(𝐒 _)} n@{𝐒(𝐒 _)} div mini = [∨]-introₗ (leastDivisor-eq2 div (const mini))

open import Type
leastDivisor-intro : ∀{ℓ} → (P : ℕ → ℕ → Type{ℓ})
                   → ((n : ℕ) → (D : ℕ) → (D ∣ n) → (∀{d} → (2 ≤ d) → (d ∣ n) → (D ≤ d)) → P(n)(D))
                   → ((n : ℕ) → P(n)(leastDivisor n))
leastDivisor-intro P pd 0            = pd 0 0 Div𝟎 (\_ _ → min)
leastDivisor-intro P pd 1            = pd 1 1 (Div𝐒 Div𝟎) (\_ div → sub₂(_≡_)(_≤_) (symmetry(_≡_) ([1]-only-divides-[1] div)))
leastDivisor-intro P pd (n@(𝐒(𝐒 _))) = pd n (leastDivisor n) leastDivisor-correctness leastDivisor-minimal

import      Numeral.Natural.Function as ℕ
open import Numeral.Natural.Function.Proofs
open import Numeral.Natural.Oper
open import Syntax.Transitivity

-- Intuitively, if a divides b, it means that b may have prime divisors that differ from a, and some may be smaller.
-- TODO: Prove when assuming (leastDivisor a ∣ b) instead. It will imply this
leastDivisor-divisibility-order : ∀{a b} → (a ≥ 2) → (a ∣ b) → (leastDivisor a ≥ leastDivisor b)
leastDivisor-divisibility-order {a}{b} dom ab =
  leastDivisor-intro(\b db → (a ∣ b) → (leastDivisor a ≥ db))
    (\b D₁ D₁b mini1 → leastDivisor-intro(\a da → (da ≥ 2) → (a ∣ b) → (da ≥ D₁))
      (\a D₂ D₂a mini2 dom ab → mini1{D₂} dom (D₂a 🝖 ab))
      a (leastDivisor-range dom)
    )
    b
    ab

leastDivisor-[⋅]ₗ-order : ∀{a b} → (a ≥ 2) → (leastDivisor a ≥ leastDivisor(a ⋅ b))
leastDivisor-[⋅]ₗ-order{a}{b} dom = leastDivisor-divisibility-order dom (divides-with-[⋅] {c = b} ([∨]-introₗ (reflexivity(_∣_))))

open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Divisibility.Proofs.Productᵣ

leastDivisor-of-[⋅] : (2 ≤ a) → (2 ≤ b) → (leastDivisor(a ⋅ b) ≡ ℕ.min(leastDivisor a) (leastDivisor b))
leastDivisor-of-[⋅] {a} {b} bound-a bound-b =
  leastDivisor-intro(\b lDb → (2 ≤ b) → (2 ≤ lDb) → (leastDivisor(a ⋅ b) ≡ ℕ.min(leastDivisor a) lDb))
    (\b lDb div-b min-b bound-b bound-lDb → leastDivisor-intro(\a lDa → (2 ≤ a) → (2 ≤ lDa) → (leastDivisor(a ⋅ b) ≡ ℕ.min lDa lDb))
      (\a lDa div-a min-a bound-a bound-lDa → leastDivisor-intro(\ab lDab → Prime(lDab) → (ab ≡ a ⋅ b) → (lDab ≡ ℕ.min lDa lDb))
        (\{ab lDab div-ab min-ab prim-ab [≡]-intro → antisymmetry(_≤_)(_≡_)
          ([↔]-to-[→] [≤]-conjunction-min ([∧]-intro
            (min-ab bound-lDa (div-a 🝖 divides-with-[⋅] {c = b} ([∨]-introₗ (reflexivity(_∣_)))))
            (min-ab bound-lDb (div-b 🝖 divides-with-[⋅] {b = a} ([∨]-introᵣ (reflexivity(_∣_)))))
          ))
          ([↔]-to-[→] [≤]-disjunction-min ([∨]-elim2
            (min-a (prime-lower-bound prim-ab))
            (min-b (prime-lower-bound prim-ab))
            (prime-divides-of-[⋅] {lDab}{a}{b} prim-ab div-ab)))
        })
        (a ⋅ b)
        (leastDivisor-prime{a ⋅ b} (succ(succ(min{2})) 🝖 [≤]-with-[⋅] bound-a bound-b))
        [≡]-intro
      )
      a
      bound-a
      (leastDivisor-range bound-a)
    )
    b
    bound-b
    (leastDivisor-range bound-b)

open import Structure.Operator.Properties

leastDivisor-of-[^] : (2 ≤ a) → ⦃ Positive(n) ⦄ → (leastDivisor(a ^ n) ≡ leastDivisor(a))
leastDivisor-of-[^] {a} {1}      bound-a           = [≡]-intro
leastDivisor-of-[^] {a} {𝐒(𝐒 n)} bound-a ⦃ pos-n ⦄ = leastDivisor-of-[⋅] {a}{a ^ 𝐒(n)} bound-a (bound-a 🝖 [^]ₗ-growing{a}{1}{𝐒(n)} (\()) ([↔]-to-[→] Positive-greater-than-zero pos-n)) 🝖 ([↔]-to-[→] min-defᵣ (leastDivisor-[⋅]ₗ-order {a}{a ^ n} bound-a) 🝖 leastDivisor-of-[^] {a}{𝐒 n} bound-a)

leastDivisor-of-lesser-prime-[⋅]ₗ : Prime(a) → (a ≤ leastDivisor b) → (leastDivisor(a ⋅ b) ≡ a)
leastDivisor-of-lesser-prime-[⋅]ₗ {a}{b} prim-a ab =
  leastDivisor(a ⋅ b)                    🝖[ _≡_ ]-[ leastDivisor-of-[⋅] (prime-lower-bound prim-a) (prime-lower-bound prim-a 🝖 ab 🝖 leastDivisor-order{b}) ]
  ℕ.min(leastDivisor a) (leastDivisor b) 🝖[ _≡_ ]-[ [↔]-to-[→] min-defₗ (leastDivisor-order 🝖 ab) ]
  leastDivisor a                         🝖[ _≡_ ]-[ [↔]-to-[←] leastDivisor-when-fixpoint ([∨]-introᵣ prim-a) ]
  a                                      🝖-end

open import Data.Tuple using (_,_)
open import Logic.Predicate
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Compatibility
open import Structure.Function
open import Structure.Relator

Composite-without-leastDivisor-lower-bound : (c : Composite(n)) →
  let instance _ = leastDivisor-positive (Positive-greater-than(composite-lower-bound c))
  in  ((n ⌊/⌋ leastDivisor n) ≥ 2)
Composite-without-leastDivisor-lower-bound {n} c
  with [∃]-intro (a , b) ⦃ [∧]-intro ([∧]-intro a2 b2) abn ⦄ ← [↔]-to-[→] composite-existence-with-bound c
  =
    let instance _ = leastDivisor-positive (Positive-greater-than(composite-lower-bound c))
    in [∨]-elim
      (\div-a →
        2                          🝖[ _≤_ ]-[ [≤]-with-[⋅] {1}{2}{a ⌊/⌋ leastDivisor n}{b} ([↔]-to-[→] Positive-greater-than-zero ([↔]-to-[→] ([⌊/⌋]-positive {a}{leastDivisor n}) (divides-upper-limit ⦃ Positive-greater-than a2 ⦄ div-a))) b2 ]
        (a ⌊/⌋ leastDivisor n) ⋅ b 🝖[ _≤_ ]-[ sub₂(_≡_)(_≤_) (symmetry(_≡_) ([⌊/⌋][⋅]ₗ-compatibility {a}{b} div-a)) ]
        (a ⋅ b) ⌊/⌋ leastDivisor n 🝖[ _≤_ ]-[ sub₂(_≡_)(_≤_) (congruence₁(_⌊/⌋ leastDivisor n) abn) ]
        n ⌊/⌋ leastDivisor n       🝖-end
      )
      (\div-b →
        2                          🝖[ _≤_ ]-[ [≤]-with-[⋅] {2}{1}{a}{b ⌊/⌋ leastDivisor n} a2 (([↔]-to-[→] Positive-greater-than-zero ([↔]-to-[→] ([⌊/⌋]-positive {b}{leastDivisor n}) (divides-upper-limit ⦃ Positive-greater-than b2 ⦄ div-b)))) ]
        a ⋅ (b ⌊/⌋ leastDivisor n) 🝖[ _≤_ ]-[ sub₂(_≡_)(_≤_) (symmetry(_≡_) ([⌊/⌋][⋅]ᵣ-compatibility {a}{b} div-b)) ]
        (a ⋅ b) ⌊/⌋ leastDivisor n 🝖[ _≤_ ]-[ sub₂(_≡_)(_≤_) (congruence₁(_⌊/⌋ leastDivisor n) abn) ]
        n ⌊/⌋ leastDivisor n       🝖-end
      )
      (prime-divides-of-[⋅] {leastDivisor n}{a}{b}
        (leastDivisor-prime{n} ([≤]-predecessor ([≤]-predecessor ([≤]-with-[⋅] a2 b2)) 🝖 sub₂(_≡_)(_≤_) abn))
        (substitute₂-₂ₗ(_∣_)(_) abn leastDivisor-correctness)
      )
