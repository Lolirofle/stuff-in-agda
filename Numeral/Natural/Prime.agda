module Numeral.Natural.Prime where

import Lvl
open import Data
open import Data.Boolean.Stmt
open import Data.Either as Either using ()
open import Data.Tuple as Tuple using ()
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Type

PrimeProof : {_ : ℕ} → Stmt{Lvl.𝟎}
PrimeProof{n} = (∀{x} → (𝐒(x) ∣ 𝐒(𝐒(n))) → ((x ≡ 𝟎) ∨ (x ≡ 𝐒(n))))

-- A prime number is a number `n` in which its only divisors are `{1,n}`.
data Prime : ℕ → Stmt{Lvl.𝟎} where
  intro : ∀{n} → PrimeProof{n} → Prime(𝐒(𝐒(n)))

-- A composite number is a number which are the product of two numbers greater than or equals 2.
data Composite : ℕ → Stmt{Lvl.𝟎} where
  intro : (a b : ℕ) → Composite(𝐒(𝐒(a)) ⋅ 𝐒(𝐒(b)))

Composite-intro : (a b : ℕ) → ⦃ _ : IsTrue(a ≥? 2) ⦄ ⦃ _ : IsTrue(b ≥? 2) ⦄ → Composite(a ⋅ b)
Composite-intro (𝐒(𝐒 a)) (𝐒(𝐒 b)) = intro a b

-- PrimeFactor(n)(p) means that `p` is a prime factor of `n`.
record PrimeFactor(n : ℕ) (p : ℕ) : Stmt{Lvl.𝟎} where
  constructor intro
  field
    ⦃ prime ⦄  : Prime(p)
    ⦃ factor ⦄ : (p ∣ n)

-- greater-prime-existence : ∀{p} → Prime(p) → ∃(p₂ ↦ Prime(p₂) ∧ (p₂ > p))

-- TODO: https://math.stackexchange.com/questions/2786458/a-formal-statement-of-the-fundamental-theorem-of-arithmetic
PrimeMultiset = Type{Lvl.𝟎}
PrimeMultiSet = ((p : ℕ) → ⦃ _ : Prime(p) ⦄ → ℕ)

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

prime-only-divisors : ∀{n} → ⦃ _ : Prime(n) ⦄ → (∀{x} → (x ∣ n) → ((x ≡ 1) ∨ (x ≡ n)))
prime-only-divisors {𝐒 (𝐒 n)} ⦃ intro prime ⦄ {𝟎}   = [⊥]-elim ∘ [0]-divides-not
prime-only-divisors {𝐒 (𝐒 n)} ⦃ intro prime ⦄ {𝐒 x} = Either.map2 ([≡]-with(𝐒)) ([≡]-with(𝐒)) ∘ prime

prime-when-only-divisors : ∀{n} → (n ≥ 2) → (∀{x} → (x ∣ n) → ((x ≡ 1) ∨ (x ≡ n))) → Prime(n)
prime-when-only-divisors {𝐒(𝐒 n)} [≤]-with-[𝐒] proof = intro p where
  p : PrimeProof
  p {𝟎}   _ = [∨]-introₗ [≡]-intro
  p {𝐒 x}   = Either.map2 (injective(𝐒)) (injective(𝐒)) ∘ proof

prime-composite-not : ∀{n} → Prime(n) → Composite(n) → ⊥
prime-composite-not {.(𝐒(𝐒(a)) ⋅ 𝐒(𝐒(b)))} p (intro a b) =
  Either.map1
    (\())
    ((\()) ∘ cancellationₗ(_+_) {x = a} ∘ injective(𝐒) ∘ injective(𝐒))
    (prime-only-divisors ⦃ p ⦄ {𝐒(𝐒(a))} (divides-with-[⋅]ₗ {c = 𝐒(𝐒(b))} divides-reflexivity))

-- TODO: Implement a primality test algorithm (e.g. brute forcing in the interval 2 up to √p, checking if the product of a pair in this interval is p). Using that, one can get (prime-or-composite : ∀{n} → Prime(𝐒(𝐒(n))) ∨ Composite(𝐒(𝐒(n)))) by boolean decidability if the algorithm is proven to be correct

-- prime-xor-composite : ∀{n} → Prime(𝐒(𝐒(n))) ⊕ Composite(𝐒(𝐒(n)))
-- prime-xor-composite {n} = [⊕]-or-not-both {!!} (Tuple.uncurry prime-composite-not)

-- TODO: Prove this by first proving that every natural number greater than 2 is a product of prime factors, and that (p ∣ a) means p is a prime factor of a. Then, (p is a prime factor of x ⋅ y) is the same as p is either a prime factor of x or of y. This will then follow
-- prime-divides-of-[⋅] : ∀{p} ⦃ _ : Prime(p) ⦄ → ∀{x y} → (p ∣ (x ⋅ y)) → ((p ∣ x) ∨ (p ∣ y))
-- prime-divides-of-[⋅] {𝐒(𝐒(p))} ⦃ intro prime ⦄ pxy = {!!}

module _ where
  open import Sets.PredicateSet renaming (_≡_ to _≡ₛ_)

  [0]-primeFactors : Prime ⊆ PrimeFactor(0)
  [0]-primeFactors prime = intro where
    instance _ = prime

  [1]-primeFactors : PrimeFactor(1) ⊆ ∅ {Lvl.𝟎}
  [1]-primeFactors {𝐒 𝟎} (intro ⦃ () ⦄)
  [1]-primeFactors {𝐒 (𝐒 x)} (intro ⦃ factor = factor ⦄) with [≤]-with-[𝐒] ⦃ ⦄ ← divides-upper-limit factor

  prime-primeFactors : ∀{p} ⦃ _ : Prime(p) ⦄ → (PrimeFactor(p) ≡ₛ (• p))
  prime-primeFactors {p}{x} = [↔]-intro (\{[≡]-intro → intro}) (\{(intro ⦃ prime ⦄ ⦃ factor ⦄) → [∨]-elim (\{[≡]-intro → [⊥]-elim ([1]-nonprime prime)}) (symmetry(_≡_)) (prime-only-divisors {p} factor)})

  {- -- TODO: When prime or composite is proven
  primefactor-self : ∀{n} → PrimeFactor(𝐒(𝐒(p)))(𝐒(𝐒(p)))
  PrimeFactor.prime primefactor-self = {!!}
  PrimeFactor.factor primefactor-self = {!!}
  -}
