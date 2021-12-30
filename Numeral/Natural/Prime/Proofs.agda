module Numeral.Natural.Prime.Proofs where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Data.Either as Either using ()
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Functional.Instance
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Logic.Predicate.Theorems
open import Numeral.Natural
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Prime
open import Numeral.Natural.Relation
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type

[0]-nonprime : ¬ Prime(0)
[0]-nonprime ()

[1]-nonprime : ¬ Prime(1)
[1]-nonprime ()

[0]-noncomposite : ¬ Composite(0)
[0]-noncomposite ()

[1]-noncomposite : ¬ Composite(1)
[1]-noncomposite ()

[2]-prime : Prime(2)
[2]-prime = intro p where
  p : PrimeProof
  p {0} _ = [∨]-introₗ [≡]-intro
  p {1} _ = [∨]-introᵣ [≡]-intro

[3]-prime : Prime(3)
[3]-prime = intro p where
  p : PrimeProof
  p {0} _ = [∨]-introₗ [≡]-intro
  p {1} (Div𝐒 ())
  p {2} _ = [∨]-introᵣ [≡]-intro

[4]-composite : Composite(4)
[4]-composite = intro 0 0

[5]-prime : Prime(5)
[5]-prime = intro p where
  p : PrimeProof
  p {0} _ = [∨]-introₗ [≡]-intro
  p {1} (Div𝐒 (Div𝐒 ()))
  p {2} (Div𝐒 ())
  p {3} (Div𝐒 ())
  p {4} _ = [∨]-introᵣ [≡]-intro

[6]-composite : Composite(6)
[6]-composite = Composite-intro 2 3

[7]-prime : Prime(7)
[7]-prime = intro p where
  p : PrimeProof
  p {0} _ = [∨]-introₗ [≡]-intro
  p {1} (Div𝐒 (Div𝐒 (Div𝐒 ())))
  p {2} (Div𝐒 (Div𝐒 ()))
  p {3} (Div𝐒 ())
  p {4} (Div𝐒 ())
  p {5} (Div𝐒 ())
  p {6} d = [∨]-introᵣ [≡]-intro

[8]-composite : Composite(8)
[8]-composite = Composite-intro 2 4

[9]-composite : Composite(9)
[9]-composite = Composite-intro 3 3

[10]-composite : Composite(10)
[10]-composite = Composite-intro 2 5

[11]-prime : Prime(11)
[11]-prime = intro p where
  p : PrimeProof
  p {0} _ = [∨]-introₗ [≡]-intro
  p {1} (Div𝐒 (Div𝐒 (Div𝐒 (Div𝐒 (Div𝐒 ())))))
  p {2} (Div𝐒 (Div𝐒 (Div𝐒 ())))
  p {3} (Div𝐒 (Div𝐒 ()))
  p {4} (Div𝐒 (Div𝐒 ()))
  p {5} (Div𝐒 ())
  p {6} (Div𝐒 ())
  p {7} (Div𝐒 ())
  p {8} (Div𝐒 ())
  p {9} (Div𝐒 ())
  p {10} d = [∨]-introᵣ [≡]-intro

prime-lower-bound : ∀{n} → Prime(n) → (n ≥ 2)
prime-lower-bound {𝐒(𝐒 _)} p = succ (succ min)

composite-lower-bound : ∀{n} → Composite(n) → (n ≥ 4)
composite-lower-bound {.(𝐒 (𝐒 a) ⋅ 𝐒 (𝐒 b))} (intro a b) = succ(succ(succ(succ min)))

prime-only-divisors : ∀{n} → Prime(n) → (∀{x} → (x ∣ n) → ((x ≡ 1) ∨ (x ≡ n)))
prime-only-divisors {𝐒 (𝐒 n)} (intro prime) {𝟎}   = [⊥]-elim ∘ [0]-divides-not
prime-only-divisors {𝐒 (𝐒 n)} (intro prime) {𝐒 x} = Either.map (congruence₁(𝐒)) (congruence₁(𝐒)) ∘ prime

prime-when-only-divisors : ∀{n} → (n ≥ 2) → (∀{x} → (x ∣ n) → ((x ≡ 1) ∨ (x ≡ n))) → Prime(n)
prime-when-only-divisors {𝐒(𝐒 n)} (succ _) proof = intro p where
  p : PrimeProof
  p {𝟎}   _ = [∨]-introₗ [≡]-intro
  p {𝐒 x}   = Either.map (injective(𝐒)) (injective(𝐒)) ∘ proof

prime-prime-divisor : ∀{a b} → Prime(a) → Prime(b) → (a ∣ b) → (a ≡ b)
prime-prime-divisor pa pb div with prime-only-divisors pb div
... | [∨]-introₗ [≡]-intro with () ← [1]-nonprime pa
... | [∨]-introᵣ ab = ab

module _ where
  open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)

  private variable a b n p : ℕ

  -- All prime numbers are prime factors of 0.
  [0]-primeFactors : PrimeFactor(0) ⊇ Prime
  [0]-primeFactors prime = intro where
    instance _ = prime
    instance _ = Div𝟎

  -- There are no prime factors of 1.
  [1]-primeFactors : PrimeFactor(1) ⊆ ∅ {Lvl.𝟎}
  [1]-primeFactors {𝐒 𝟎} (intro ⦃ () ⦄)
  [1]-primeFactors {𝐒 (𝐒 x)} (intro ⦃ factor = factor ⦄) with succ() ← divides-upper-limit factor

  -- The only prime factors of a prime number is itself.
  prime-primeFactors : ⦃ _ : Prime(p) ⦄ → (PrimeFactor(p) ≡ₛ (• p))
  prime-primeFactors {p}{x} = [↔]-intro (\{[≡]-intro → intro ⦃ factor = reflexivity(_∣_) ⦄}) (\{intro → symmetry(_≡_) (prime-prime-divisor infer infer infer)})

  -- When a number is a prime factor of itself, it is a prime number.
  -- A very obvious fact (it follows by definition).
  reflexive-primeFactor-is-prime : (n ∈ PrimeFactor(n)) → Prime(n)
  reflexive-primeFactor-is-prime intro = infer

  divisor-primeFactors : ∀{a b} → (a ∣ b) → (PrimeFactor(a) ⊆ PrimeFactor(b))
  divisor-primeFactors div (intro ⦃ p ⦄ ⦃ xa ⦄) = intro ⦃ p ⦄ ⦃ transitivity(_∣_) xa div ⦄

composite-existence : ∀{n} → Composite(n) ↔ ∃{Obj = ℕ ⨯ ℕ}(\(a , b) → (a + 2) ⋅ (b + 2) ≡ n)
composite-existence = [↔]-intro (\{([∃]-intro (a , b) ⦃ [≡]-intro ⦄) → intro a b}) \{(intro a b) → [∃]-intro (a , b) ⦃ [≡]-intro ⦄}

composite-existence-with-bound : ∀{n} → Composite(n) ↔ ∃{Obj = ℕ ⨯ ℕ}(\(a , b) → (a ≥ 2) ∧ (b ≥ 2) ∧ (a ⋅ b ≡ n))
composite-existence-with-bound =
  [↔]-transitivity composite-existence ([↔]-intro
    (\{
      ([∃]-intro (𝟎 , _) ⦃ [∧]-intro ([∧]-intro () _) _ ⦄) ;
      ([∃]-intro (𝐒 𝟎 , _) ⦃ [∧]-intro ([∧]-intro (succ()) _) _ ⦄) ;
      ([∃]-intro (𝐒(𝐒 _) , 𝐒 𝟎) ⦃ [∧]-intro ([∧]-intro _ (succ())) _ ⦄) ; 
      ([∃]-intro (𝐒(𝐒 a) , 𝐒(𝐒 b)) ⦃ [∧]-intro _ p ⦄) → [∃]-intro (a , b) ⦃ p ⦄
    })
    (\([∃]-intro (a , b) ⦃ p ⦄) → [∃]-intro (a + 2 , b + 2) ⦃ [∧]-intro ([∧]-intro (succ(succ min)) (succ(succ min))) p ⦄)
  )

prime-positive : ∀{p} → Prime(p) → Positive(p)
prime-positive {𝐒 p} _ = <>
