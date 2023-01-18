module Numeral.Natural.Function.PrimeDivisor.Proofs where

open import Data
open import Data.List
import      Data.Tuple as Tuple
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic.Propositional.Theorems
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

private variable a b d n p : ℕ

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
    P n (d ⊰ primeDivisors(n ⌊/⌋ d))     ⇒-[ substitute₂-₂ₗ(P)(_) eq ]
    P n (primeDivisors n)                ⇒-end

primeDivisors-step : (n2 : n ≥ 2) → (primeDivisors n ≡ leastDivisor n ⊰ primeDivisors((n ⌊/⌋ leastDivisor n) ⦃ leastDivisor-positive([↔]-to-[←] Positive-greater-than-zero([≤]-predecessor n2)) ⦄))
primeDivisors-step n2 = primeDivisors-intro(\n pdn → (n2 : n ≥ 2) → (pdn ≡ leastDivisor n ⊰ primeDivisors((n ⌊/⌋ leastDivisor n) ⦃ leastDivisor-positive([↔]-to-[←] Positive-greater-than-zero([≤]-predecessor n2)) ⦄))) (\()) (\{(succ())}) (\_ _ → [≡]-intro) n2

open import Data.List.Functions as List using (_++_)
open import Structure.Function

primeDivisors-tail : (n2 : n ≥ 2) → (List.tail(primeDivisors n) ≡ primeDivisors((n ⌊/⌋ leastDivisor n) ⦃ leastDivisor-positive([↔]-to-[←] Positive-greater-than-zero([≤]-predecessor n2)) ⦄))
primeDivisors-tail n2 = congruence₁(List.tail) (primeDivisors-step n2)

open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Universal.Functions
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Relation.Divisibility.Proofs.FlooredDivision
open import Structure.Operator
open import Syntax.Transitivity

-- All prime divisors are prime numbers.
primeDivisors-prime : AllElements Prime(primeDivisors n)
primeDivisors-prime = primeDivisors-intro(\_ l → AllElements Prime l) ∅ ∅ (\ ⦃ ord ⦄ prev → (leastDivisor-prime ord) AllElements.⊰ prev)

-- All prime divisors of n are divisors of n.
primeDivisors-divisors : AllElements(_∣ n) (primeDivisors n)
primeDivisors-divisors = primeDivisors-intro(\n l → AllElements(_∣ n) l) ∅ ∅ (\ ⦃ n2 ⦄ prev → leastDivisor-correctness AllElements.⊰ AllElements-fn (divides-withoutᵣ-⌊/⌋ ⦃ [∨]-introᵣ (leastDivisor-positive ([↔]-to-[←] Positive-greater-than-zero ([≤]-predecessor n2))) ⦄ leastDivisor-correctness) prev)

-- The product of the prime divisors of a number is the number itself.
-- Alternative proof of the fundamental theorem of arithmetic.
product-primeDivisors-inverse : ⦃ Positive n ⦄ → (List.foldᵣ(_⋅_) 1 (primeDivisors n) ≡ n)
product-primeDivisors-inverse n@{𝐒 _} = primeDivisors-intro(\n l → ⦃ Positive n ⦄ → List.foldᵣ(_⋅_) 1 l ≡ n) (\ ⦃ ⦄) [≡]-intro \{n} ⦃ pos-n ⦄ eq →
  let
     instance
      leastDiv-pos : Positive(leastDivisor n)
      leastDiv-pos = leastDivisor-positive ([↔]-to-[←] Positive-greater-than-zero ([≤]-predecessor pos-n))
  in
    List.foldᵣ(_⋅_) 1 (leastDivisor n ⊰ primeDivisors((n ⌊/⌋ leastDivisor n) ⦃ _ ⦄)) 🝖[ _≡_ ]-[]
    leastDivisor n ⋅ List.foldᵣ(_⋅_) 1 (primeDivisors((n ⌊/⌋ leastDivisor n) ⦃ _ ⦄)) 🝖[ _≡_ ]-[ congruence₂-₂(_⋅_)(leastDivisor n) (eq ⦃ [↔]-to-[→] ([⌊/⌋]-positive{n}) leastDivisor-order ⦄) ]
    leastDivisor n ⋅ (n ⌊/⌋ leastDivisor n) ⦃ _ ⦄                                    🝖[ _≡_ ]-[ [⋅][⌊/⌋]-inverseOperatorₗ leastDivisor-correctness ]
    n                                                                                🝖-end

open import Numeral.Natural.Oper.FlooredDivision.Proofs.Inverse
open import Numeral.Natural.Relation.Divisibility.Proofs
primeDivisors-intro-by-prime : ∀{ℓ} → (P : ℕ → List(ℕ) → Type{ℓ})
                             → P(0)(∅)
                             → P(1)(∅)
                             → (∀{n p} → ⦃ pos-n : Positive(n) ⦄ → Prime(p) → AllElements(p ≤_)(primeDivisors n) → P(n)(primeDivisors n) → P(p ⋅ n)(p ⊰ primeDivisors(n)))
                             → (∀{n} → P n (primeDivisors n))
primeDivisors-intro-by-prime P p0 p1 pd {n} = primeDivisors-intro(P) p0 p1 (\{ {n@(𝐒 _)} ⦃ ord-n ⦄ prev →
    let instance _ = leastDivisor-positive{n} <> in
    substitute₂-₁ᵣ(P)(_)
      ([⋅][⌊/⌋]-inverseOperatorₗ leastDivisor-correctness)
      (pd{(n ⌊/⌋ leastDivisor n)}{leastDivisor n}
        ⦃ [↔]-to-[→] ([⌊/⌋]-positive {n}{leastDivisor n}) (divides-upper-limit(leastDivisor-correctness)) ⦄
        (leastDivisor-prime ord-n)
        (substitute₂-₂ᵣ(AllElements)(_) (primeDivisors-tail ord-n) ([∧]-elimᵣ ([↔]-to-[→] AllElements-head-tail (AllElements-fn₂ leastDivisor-minimal (AllElements-fn prime-lower-bound (primeDivisors-prime{n = n})) primeDivisors-divisors))))
        prev
      )
  })
  {n}
open import Data.List.Relation.Permutation
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Prime.Proofs.Representation

-- The function of prime divisors of a product of prime numbers is unique up to permutations.
-- TODO: Is this proof actually providing a way of sorting each list l (a sorting algorithm)? (assuming primeDivisors is sorted)
primeDivisors-product-inverse : ∀{l} → AllElements Prime(l) → (primeDivisors(List.foldᵣ(_⋅_) 1 l) permutes l)
primeDivisors-product-inverse{l} ap = foldᵣ-primes-permutation{primeDivisors(List.foldᵣ(_⋅_) 1 l)}{l} primeDivisors-prime ap (product-primeDivisors-inverse ⦃ foldᵣ-property-all{P = Positive}{Q = Positive} [⋅]-positiveᵣ <> (AllElements-fn prime-positive ap) ⦄)

open import Data.List.Relation.Pairwise
open import Data.List.Sorting
open import Data.List.Sorting.Proofs
open import Functional
open import Numeral.Natural.Oper.Comparisons

-- The list of prime divisors from the function is sorted.
primeDivisors-sorted : Sorted(_≤?_)(primeDivisors n)
primeDivisors-sorted = primeDivisors-intro(\_ → Sorted(_≤?_)) AdjacentlyPairwise.empty AdjacentlyPairwise.empty (\{n} → proof{n}) where
  instance
    leastDiv-pos : ∀{n} → ⦃ n2 : n ≥ 2 ⦄ → Positive(leastDivisor n)
    leastDiv-pos ⦃ n2 ⦄ = leastDivisor-positive (Positive-greater-than n2)
    
  proof : ∀{n} → ⦃ n2 : n ≥ 2 ⦄ →
          Sorted(_≤?_)(primeDivisors((n ⌊/⌋ leastDivisor n))) →
          Sorted(_≤?_)((leastDivisor n) ⊰ primeDivisors((n ⌊/⌋ leastDivisor n)))
  proof {n} ⦃ n2 ⦄ s = Sorted-by-least-element(_≤?_) (AllElements-fn₂ (\prim div → [↔]-to-[→] (decider-true ⦃ [≤]-decider ⦄) (leastDivisor-minimal (prime-lower-bound prim) (divides-withoutᵣ-⌊/⌋{n} ⦃ [∨]-introᵣ (leastDiv-pos{n}) ⦄ leastDivisor-correctness div))) primeDivisors-prime primeDivisors-divisors) s

-- TODO: Prove using Sorted-permutes-identity and if the following is proven (∀{l} → AllElements Prime(l) → AllElements(_∣ n) l → → (l permutes primeDivisors n))
-- primeDivisors-uniqueness : ∀{l} → AllElements Prime(l) → AllElements(_∣ n) l → Sorted(_≤?_) l → (l ≡ primeDivisors n)

open import Data.Tuple using (_,_)
open import Data.List.Equiv.Id
open import Data.List.Proofs
open import Data.List.Relation.Permutation.Proofs
open import Logic.Predicate
import      Numeral.Natural.Function as ℕ
open import Numeral.Natural.Function.Proofs
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Compatibility
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Prime.Decidable
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Structure.Function
open import Structure.Operator.Properties

-- The prime divisors of a prime number consists of only the number itself.
primeDivisors-of-prime : Prime(p) → (primeDivisors p ≡ List.singleton p)
primeDivisors-of-prime = primeDivisors-intro-by-prime(\p pp → Prime(p) → (pp ≡ List.singleton p))
  ([⊥]-elim ∘ [0]-nonprime)
  ([⊥]-elim ∘ [1]-nonprime)
  (\{
    {𝐒(𝟎)}           ⦃ n-pos ⦄ prim-p ord-p prev prim-pn → [≡]-intro ;
    {n@(𝐒(𝐒 _))} {p} ⦃ n-pos ⦄ prim-p ord-p prev prim-pn → [⊥]-elim (prime-composite-not prim-pn ([↔]-to-[←] composite-existence-with-bound ([∃]-intro (p , n) ⦃ [∧]-intro ([∧]-intro (prime-lower-bound prim-p) (succ(succ min))) [≡]-intro ⦄)))
  })

-- The prime divisors of the product of a prime number and another number is the prime number and the prime divisors of the number.
primeDivisors-of-[⋅]-prime : ⦃ Prime(a) ⦄ → ⦃ Positive(b) ⦄ → (primeDivisors(a ⋅ b) permutes (a ⊰ (primeDivisors b)))
primeDivisors-of-[⋅]-prime {a}{b} ⦃ pa ⦄ ⦃ pb ⦄ = primeDivisors-intro(\b pdb → ⦃ Positive(b) ⦄ → (primeDivisors(a ⋅ b) permutes (a ⊰ pdb)))
  (\ ⦃ ⦄)
  (sub₂(_≡_)(_permutes_) (primeDivisors-of-prime pa))
  (\{ {b} ⦃ b2 ⦄ prev →
    let
      step = primeDivisors-step (b2 🝖 [⋅]ᵣ-growing {b}{a} ([≤]-predecessor (prime-lower-bound pa)))
      instance pos-minDiv-b = leastDivisor-positive (Positive-greater-than b2)
      instance pos-minDiv-ab = leastDivisor-positive ([↔]-to-[→] [⋅]-positive ([∧]-intro (prime-positive pa) (Positive-greater-than b2)))
    in [∨]-elim
      (\ab →
        let
          min-div-ab : leastDivisor(a ⋅ b) ≡ a
          min-div-ab = leastDivisor-of-lesser-prime-[⋅]ₗ {a}{b} pa ab
        in sub₂(_≡_)(_permutes_) $
          primeDivisors(a ⋅ b)                                                         🝖[ _≡_ ]-[ step ]
          leastDivisor(a ⋅ b) ⊰ primeDivisors(((a ⋅ b) ⌊/⌋ leastDivisor(a ⋅ b)) ⦃ _ ⦄) 🝖[ _≡_ ]-[ congruence₂(_⊰_) min-div-ab (congruence₁(primeDivisors) ([⌊/⌋]-operator (reflexivity(_≡_)) min-div-ab)) ]
          a ⊰ primeDivisors(((a ⋅ b) ⌊/⌋ a) ⦃ _ ⦄)                                     🝖[ _≡_ ]-[ congruence₂-₂(_⊰_)(a) (congruence₁(primeDivisors) ([⌊/⌋][swap⋅]-inverseOperatorᵣ {a}{b} ⦃ prime-positive pa ⦄)) ]
          a ⊰ primeDivisors(b)                                                         🝖[ _≡_ ]-[ congruence₂-₂(_⊰_)(a) (primeDivisors-step b2) ]
          a ⊰ leastDivisor b ⊰ primeDivisors((b ⌊/⌋ leastDivisor b) ⦃ _ ⦄)             🝖-end
      )
      (\nab →
        let
          min-div-ab : leastDivisor(a ⋅ b) ≡ leastDivisor b
          min-div-ab =
            leastDivisor(a ⋅ b)                    🝖[ _≡_ ]-[ leastDivisor-of-[⋅] (prime-lower-bound pa) b2 ]
            ℕ.min(leastDivisor a) (leastDivisor b) 🝖[ _≡_ ]-[ [↔]-to-[→] min-defᵣ (sub₂(_<_)(_≤_) nab 🝖 sub₂(_≡_)(_≤_) (symmetry(_≡_) ([↔]-to-[←] leastDivisor-when-fixpoint ([∨]-introᵣ pa)))) ]
            leastDivisor b                         🝖-end
        in
          primeDivisors(a ⋅ b)                                                         🝖[ _≡_ ]-[ step ]-sub
          leastDivisor(a ⋅ b) ⊰ primeDivisors(((a ⋅ b) ⌊/⌋ leastDivisor(a ⋅ b)) ⦃ _ ⦄) 🝖[ _≡_ ]-[ congruence₂(_⊰_) min-div-ab (congruence₁(primeDivisors) ([⌊/⌋]-operator (reflexivity(_≡_)) min-div-ab)) ]-sub
          leastDivisor b ⊰ primeDivisors(((a ⋅ b) ⌊/⌋ leastDivisor(b)) ⦃ _ ⦄)          🝖[ _≡_ ]-[ congruence₂-₂(_⊰_)(leastDivisor b) (congruence₁(primeDivisors) ([⌊/⌋][⋅]ᵣ-compatibility {a}{b}{leastDivisor b} ⦃ leastDivisor-positive (Positive-greater-than b2) ⦄ leastDivisor-correctness)) ]-sub
          leastDivisor b ⊰ primeDivisors(a ⋅ (b ⌊/⌋ leastDivisor(b)) ⦃ _ ⦄)            🝖[ _permutes_ ]-[ _permutes_.prepend (prev ⦃ [↔]-to-[→] ([⌊/⌋]-positive {b}{leastDivisor b}) (divides-upper-limit(leastDivisor-correctness{b})) ⦄) ]
          leastDivisor b ⊰ a ⊰ primeDivisors((b ⌊/⌋ leastDivisor b) ⦃ _ ⦄)             🝖[ _permutes_ ]-[ _permutes_.swap ]
          a ⊰ leastDivisor b ⊰ primeDivisors((b ⌊/⌋ leastDivisor b) ⦃ _ ⦄)             🝖-end
      )
      ([≤][>]-dichotomy {a}{leastDivisor b})
  })
  {b}

-- The least divisor is the minimum of the prime divisors, or at least a lower bound.
-- Note: leastDivisor(n) is the head of primeDivisors(n) when (n ≥ 2).
primeDivisors-leastDivisor-is-lower-bound : AllElements(leastDivisor n ≤_) (primeDivisors n)
primeDivisors-leastDivisor-is-lower-bound = primeDivisors-intro(\n → AllElements(leastDivisor n ≤_))
  ∅
  ∅
  (\{n} ⦃ n2 ⦄ ap →
    let
      instance
        pos-n : Positive(n)
        pos-n = Positive-greater-than n2
      instance
        pos-minDiv : Positive(leastDivisor n)
        pos-minDiv = leastDivisor-positive pos-n
    in reflexivity(_≤_) ⊰ [∨]-elim
      (\prim → substitute₂-₂ₗ(AllElements)(_) (congruence₁(primeDivisors) {_}{1} ([⌊/⌋]-operator (reflexivity(_≡_)) ([↔]-to-[←] leastDivisor-when-fixpoint ([∨]-introᵣ prim)) 🝖 [⌊/⌋]-of-same {n})) ∅)
      (\comp → AllElements-fn
        (_🝖 leastDivisor-divisibility-order{(n ⌊/⌋ leastDivisor n) ⦃ pos-minDiv ⦄}{n}
          (Composite-without-leastDivisor-lower-bound comp)
          -- ([≤][⌊/⌋]-preserving {4}{n}{2}{leastDivisor n} (composite-lower-bound comp) {!(prime-lower-bound(leastDivisor-prime n2))!})
          {-([↔]-to-[→]
            ([⌊/⌋]-greater-than-1 {n}{leastDivisor n} leastDivisor-correctness)
            ([↔]-to-[←] leastDivisor-strict-order ([∧]-intro n2 comp))
          )-}
          (dividesₗ-div ⦃ [∨]-introᵣ pos-minDiv ⦄ leastDivisor-correctness)
        )
        ap
      )
      ([⊕]-to-[∨] (prime-xor-composite n2))
  )

primeDivisors-leastDivisor-is-minimum : let _ = a in (b ≥ 2) → AllElements(a ≤_) (primeDivisors b) ↔ (a ≤ leastDivisor b)
primeDivisors-leastDivisor-is-minimum {a}{b@(𝐒(𝐒 _))} (succ(succ min)) = [↔]-intro (\ord → AllElements-fn (ord 🝖_) (primeDivisors-leastDivisor-is-lower-bound{b})) AllElements-prepend-head

-- The prime divisors of the product of two numbers are the prime divisors of the two numbers individually.
-- primeDivisors preserves multiplication and concatenation for positive numbers.
primeDivisors-of-[⋅] : ⦃ pos-a : Positive(a) ⦄ → ⦃ pos-b : Positive(b) ⦄ → (primeDivisors(a ⋅ b) permutes ((primeDivisors a) ++ (primeDivisors b)))
primeDivisors-of-[⋅] {a}{b} ⦃ _ ⦄ ⦃ pos-b ⦄ = primeDivisors-intro-by-prime(\a pda → ⦃ Positive(a) ⦄ → (primeDivisors(a ⋅ b) permutes (pda ++ (primeDivisors b))))
  (\ ⦃ ⦄)
  (sub₂(_≡_)(_permutes_) (symmetry(_≡_) (identityₗ(_++_)(∅))))
  (\{a}{p} ⦃ pos-a ⦄ prim-p min-p prev →
    primeDivisors((p ⋅ a) ⋅ b)               🝖[ _≡_ ]-[ congruence₁(primeDivisors) (associativity(_⋅_) {p}{a}{b}) ]-sub
    primeDivisors(p ⋅ (a ⋅ b))               🝖[ _permutes_ ]-[ primeDivisors-of-[⋅]-prime ⦃ prim-p ⦄ ⦃ [↔]-to-[→] [⋅]-positive ([∧]-intro pos-a pos-b) ⦄ ]
    p ⊰ primeDivisors(a ⋅ b)                 🝖[ _permutes_ ]-[ prepend prev ]
    p ⊰ (primeDivisors a ++ primeDivisors b) 🝖[ _permutes_ ]-[]
    (p ⊰ primeDivisors a) ++ primeDivisors b 🝖-end
  )
  {a}

primeDivisors-of-[^] : ⦃ Positive(a) ⦄ → ⦃ Positive(n) ⦄ → (primeDivisors(a ^ n) permutes ((primeDivisors a) List.++^ n))
primeDivisors-of-[^] {𝐒 _}     {𝐒 𝟎}        = sub₂(_≡_)(_permutes_) (symmetry(_≡_) (identityᵣ(List._++^_)(𝟏)))
primeDivisors-of-[^] {a@(𝐒 _)} {𝐒(n@(𝐒 N))} =
  primeDivisors(a ^ 𝐒(n))                           🝖[ _permutes_ ]-[]
  primeDivisors(a ⋅ (a ^ n))                        🝖[ _permutes_ ]-[ primeDivisors-of-[⋅] {a}{a ^ n} ⦃ pos-b = [^]-positive {a}{n} ⦄ ]
  primeDivisors(a) ++ primeDivisors(a ^ n)          🝖[ _permutes_ ]-[ congruence₂-₂ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ (_++_) ⦃ permutes-[++]-function ⦄ (primeDivisors(a)) (primeDivisors-of-[^] {a}{n}) ]
  primeDivisors(a) ++ (primeDivisors(a) List.++^ n) 🝖[ _permutes_ ]-[]
  primeDivisors(a) List.++^ 𝐒(n)                    🝖-end

-- TODO: groupBy stuff so that the gcd and lcm prime divisor list stuff can be proven

{- TODO: Remove. Old stuff
primeDivisors-of-[⋅]-prime2 : Prime(a) → ⦃ Positive(b) ⦄ → (primeDivisors(a ⋅ b) permutes (a ⊰ (primeDivisors b)))
primeDivisors-of-[⋅]-prime2 {a}{b} = ℕ-strong-recursion(\a → (b : ℕ) → Prime(a) → ⦃ Positive(b) ⦄ → (primeDivisors(a ⋅ b) permutes (a ⊰ (primeDivisors b))))
  (\a rec b pa ⦃ pb ⦄ → primeDivisors-intro-by-prime(\B pdb → ⦃ Positive(B) ⦄ → (primeDivisors(a ⋅ B) permutes (a ⊰ pdb)))
    (\ ⦃ ⦄)
    (sub₂(_≡_)(_permutes_) (primeDivisors-of-prime pa))
    (\{
      {1}{p} ⦃ pb ⦄ pp min-p prev →
        primeDivisors(a ⋅ (p ⋅ 𝟏)) 🝖[ _permutes_ ]-[]
        primeDivisors(a ⋅ p)       🝖[ _permutes_ ]-[ {!!} ]
        primeDivisors(p ⋅ a)       🝖[ _permutes_ ]-[ {!rec p !} ]
        p ⊰ primeDivisors(a)       🝖[ _permutes_ ]-[ _permutes_.prepend prev ]
        p ⊰ a ⊰ ∅                  🝖[ _permutes_ ]-[ _permutes_.swap ]
        a ⊰ p ⊰ ∅                  🝖[ _permutes_ ]-[]
        a ⊰ p ⊰ primeDivisors 𝟏    🝖-end ;
      {b@(𝐒(𝐒 B))}{p} ⦃ pb ⦄ pp min-p prev → [∨]-elim
        (\le →
          let
            min-div-pb : leastDivisor(p ⋅ b) ≡ p
            min-div-pb = leastDivisor-of-lesser-prime-[⋅]ₗ {p}{b} pp (AllElements-prepend-head min-p)

            min-div-apb : leastDivisor(a ⋅ (p ⋅ b)) ≡ a
            min-div-apb = leastDivisor-of-lesser-prime-[⋅]ₗ {a}{p ⋅ b} pa (le 🝖 sub₂(_≡_)(_≤_) (symmetry(_≡_) min-div-pb))

            pb2 : p ⋅ b ≥ 2
            pb2 = [≤]-predecessor ([≤]-predecessor ([≤]-with-[⋅] (prime-lower-bound pp) (succ(succ(min{B})))))

            proof : ∀{a b} → Prime(a) → (b ≥ 2) → (a ≤ leastDivisor(b)) → (primeDivisors(a ⋅ b) ≡ a ⊰ primeDivisors(b))
            proof {a}{b} pa b2 a-div-ord =
              let min-div = leastDivisor-of-lesser-prime-[⋅]ₗ {a}{b} pa a-div-ord
              in
                primeDivisors(a ⋅ b)                                                         🝖[ _≡_ ]-[ primeDivisors-step (b2 🝖 [⋅]ᵣ-growing {b}{a} ([≤]-predecessor (prime-lower-bound pa))) ]
                leastDivisor(a ⋅ b) ⊰ primeDivisors(((a ⋅ b) ⌊/⌋ leastDivisor(a ⋅ b)) ⦃ _ ⦄) 🝖[ _≡_ ]-[ congruence₂(_⊰_) min-div (congruence₁(primeDivisors) ([⌊/⌋]-operator ⦃ leastDivisor-positive{a ⋅ b} ([↔]-to-[→] [⋅]-positive ([∧]-intro (prime-positive pa) (Positive-greater-than b2))) ⦄ [≡]-intro min-div)) ]
                a ⊰ primeDivisors(((a ⋅ b) ⌊/⌋ a) ⦃ _ ⦄)                                     🝖[ _≡_ ]-[ congruence₂-₂(_⊰_)(a) (congruence₁(primeDivisors) ([⌊/⌋][swap⋅]-inverseOperatorᵣ {a}{b} ⦃ prime-positive pa ⦄)) ]
                a ⊰ primeDivisors(b)                                                         🝖-end
          in sub₂(_≡_)(_permutes_) $
            primeDivisors(a ⋅ (p ⋅ b)) 🝖[ _≡_ ]-[ proof pa pb2 (sub₂(_≡_)(_≤_) (symmetry(_≡_) min-div-apb) 🝖 leastDivisor-divisibility-order{p ⋅ b}{a ⋅ (p ⋅ b)} pb2 (divides-with-[⋅] {p ⋅ b}{a} ([∨]-introᵣ (reflexivity(_∣_))))) ]
            a ⊰ primeDivisors(p ⋅ b)   🝖[ _≡_ ]-[ congruence₂-₂(_⊰_)(a) (proof{p}{b} pp (succ(succ min)) (AllElements-prepend-head min-p)) ]
            a ⊰ p ⊰ primeDivisors b    🝖-end
        )
        (\gt →
          primeDivisors(a ⋅ (p ⋅ b)) 🝖[ _permutes_ ]-[ {!congruence₁(primeDivisors) ?!} ]
          primeDivisors(p ⋅ (a ⋅ b)) 🝖[ _permutes_ ]-[ rec p gt (a ⋅ b) pp ⦃ {!!} ⦄ ]
          p ⊰ primeDivisors(a ⋅ b)   🝖[ _permutes_ ]-[ _permutes_.prepend prev ]
          p ⊰ a ⊰ primeDivisors b    🝖[ _permutes_ ]-[ _permutes_.swap ]
          a ⊰ p ⊰ primeDivisors b    🝖-end
        )
        ([≤][>]-dichotomy {a}{p})
    })
  )
  a
  b
-}

{-
primeDivisors-of-[⋅] : ⦃ Positive(a) ⦄ → ⦃ Positive(b) ⦄ → (primeDivisors(a ⋅ b) permutes ((primeDivisors a) ++ (primeDivisors b)))
primeDivisors-of-[⋅] {a} {b} ⦃ _ ⦄ ⦃ pos-b ⦄ = primeDivisors-intro(\a pda → ⦃ Positive(a) ⦄ → (primeDivisors(a ⋅ b) permutes (pda ++ (primeDivisors b))))
  (\ ⦃ ⦄)
  (sub₂(_≡_)(_permutes_) (symmetry(_≡_) (identityₗ(_++_)(∅))))
  (\{ {a@(𝐒(𝐒 _))} prev →
    let
      instance ld-pos = leastDivisor-positive{a} <>
      div-pos = [↔]-to-[→] ([⌊/⌋]-positive{a}) (divides-upper-limit(leastDivisor-correctness))
    in
      primeDivisors (a ⋅ b)                                                       🝖[ _permutes_ ]-[ {!!} ]
      primeDivisors(((leastDivisor a) ⋅ (a ⌊/⌋ leastDivisor a)) ⋅ b)              🝖[ _permutes_ ]-[ {!!} ]
      primeDivisors((leastDivisor a) ⋅ ((a ⌊/⌋ leastDivisor a) ⋅ b))              🝖[ _permutes_ ]-[ primeDivisors-of-[⋅]-prime {leastDivisor a}{(a ⌊/⌋ leastDivisor a) ⋅ b} ⦃ leastDivisor-prime{a}(succ(succ min)) ⦄ ⦃ [↔]-to-[→] [⋅]-positive ([∧]-intro div-pos pos-b) ⦄ ]
      leastDivisor a ⊰ (primeDivisors((a ⌊/⌋ leastDivisor a) ⋅ b))                🝖[ _permutes_ ]-[ congruence₁ ⦃ _ ⦄ ⦃ _ ⦄ (_⊰_ (leastDivisor a)) ⦃ permutes-prepend-function ⦄ (prev ⦃ div-pos ⦄) ]
      leastDivisor a ⊰ (primeDivisors((a ⌊/⌋ leastDivisor a)) ++ primeDivisors b) 🝖[ _permutes_ ]-[ {!!} ]
      (leastDivisor a ⊰ primeDivisors((a ⌊/⌋ leastDivisor a))) ++ primeDivisors b 🝖-end
    
  })
  {a}
-}
