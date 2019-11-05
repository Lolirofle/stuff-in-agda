module Functional.Repeat.Order where

open import Data
open import Data.Boolean.Stmt
open import Functional
open import Functional.Repeat hiding (_^_)
open import Functional.Repeat.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper hiding (_^_)
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals using () renaming (_≡_ to _≡ₑ_ ; [≡]-intro to [≡ₑ]-intro)
open import Sets.Setoid
open import Structure.Operator.Properties
open import Structure.Relator.Properties
open import Structure.Relator.Ordering
open import Syntax.Transitivity
open import Type

module _ {ℓ} {T : Type{ℓ}} ⦃ equiv-T : Equiv(T) ⦄ (_▫_ : T → T → T) ⦃ op : BinaryOperator(_▫_) ⦄ {id} ⦃ ident : Identity(_▫_)(id) ⦄ ⦃ assoc : Associativity(_▫_) ⦄ where
  _^_ : T → ℕ → T
  x ^ n = Functional.Repeat.repeatₗ(n)(_▫_)(id)(x)

  data FiniteOrder (x : T) : ℕ → Stmt{ℓ} where
    intro : ∀{n} → Weak.Properties.MinimumOf(_≤_)(n ↦ x ^ n ≡ id)(𝐒(n)) → FiniteOrder(x)(𝐒(n))

  Ord : T → Stmt{ℓ}
  Ord(x) = ∃(FiniteOrder(x))

  ord : (x : T) → ⦃ _ : Ord(x) ⦄ → ℕ
  ord(_) ⦃ [∃]-intro n ⦄ = n

  module _ {x : T} where
    finite-order-0 : ¬ FiniteOrder(x)(𝟎)
    finite-order-0 ()

    [^]-by-ord : ⦃ p : Ord(x) ⦄ → (x ^ ord(x) ⦃ p ⦄ ≡ id)
    [^]-by-ord ⦃ [∃]-intro (𝐒(_)) ⦃ intro p ⦄ ⦄ = Weak.Properties.MinimumOf.proof(p)

    ord-is-minimum : ⦃ p : Ord(x) ⦄ → ∀{n} → (x ^ n ≡ id) → (ord(x) ⦃ p ⦄ ≤ n)
    ord-is-minimum ⦃ [∃]-intro (𝐒(_)) ⦃ intro p ⦄ ⦄ proof = Weak.Properties.MinimumOf.minimum(p) ⦃ proof ⦄

    module _ where
      open import Relator.Equals.Proofs.Equivalence using ([≡]-to-equivalence)

      ord-non-zero : ⦃ p : Ord(x) ⦄ → (ord(x) ⦃ p ⦄ ≢ 𝟎)
      ord-non-zero ⦃ [∃]-intro 𝟎 ⦃ ⦄ ⦄ [≡ₑ]-intro

      test : ⦃ p : Ord(x) ⦄ → ord(x) ⦃ p ⦄ ≡ 0
      test ⦃ p ⦄ = [≤][0]ᵣ(ord-is-minimum ⦃ p ⦄ {0} (reflexivity(_≡_)))

      what : ⦃ p : Ord(x) ⦄ → ⊥
      what ⦃ p ⦄ = ord-non-zero ⦃ p ⦄ (test ⦃ p ⦄)

    [≤][<]-asymmetric-order : ∀{a b} → (a < b) → (b ≤ a) → ⊥

    ord-is-minimum-but-0 : ⦃ p : Ord(x) ⦄ → ∀{n} → (x ^ n ≡ id) → (n < ord(x) ⦃ p ⦄) → (n ≡ₑ 𝟎)
    ord-is-minimum-but-0 ⦃ p ⦄ {𝟎}   xnid nord = [≡ₑ]-intro
    ord-is-minimum-but-0 ⦃ p ⦄ {𝐒 n} xnid nord = [⊥]-elim([≤][<]-asymmetric-order nord (ord-is-minimum ⦃ p ⦄ xnid))

    [^]-by-add : ∀{a b} → ((x ^ a) ▫ (x ^ b) ≡ x ^ (a + b))
    [^]-by-add {a}{b} = repeatₗ-by-sum {X = T}{_▫_}{x}{id}{a}{b}

    [^]-by-product : ∀{a b} → ((((x ^ a)) ^ b) ≡ x ^ (a ⋅ b))
    [^]-by-product {a}{b} = repeatₗ-by-product {X = T}{_▫_}{x}{id}{a}{b}

    module _ {n} (n-id : (x ^ n ≡ id)) where
      [^]-by-id-add : ∀{a} → (x ^ (n + a)  ≡ x ^ a)
      [^]-by-id-add {a} =
        x ^ (n + a)       🝖-[ symmetry(_≡_) ([^]-by-add {n}{a}) ]
        (x ^ n) ▫ (x ^ a) 🝖-[ [≡]-with2ₗ(_▫_)(_) n-id ]
        id ▫ (x ^ a)      🝖-[ identityₗ(_▫_)(id) ]
        x ^ a             🝖-end

      [^]-by-id-multiple : ∀{a} → (x ^ (n ⋅ a) ≡ id)
      [^]-by-id-multiple {𝟎}    = repeatₗ-by-0 {X = T}{_▫_}{x}{id}
      [^]-by-id-multiple {𝐒(a)} =
        x ^ (n + (n ⋅ a))       🝖-[ symmetry(_≡_) ([^]-by-add {n}{n ⋅ a}) ]
        (x ^ n) ▫ (x ^ (n ⋅ a)) 🝖-[ [≡]-with2(_▫_) n-id ([^]-by-id-multiple {a}) ]
        id ▫ id                 🝖-[ identityₗ(_▫_)(id) ]
        id                      🝖-end

    -- [^]-equal-power : ⦃ p : Ord(x) ⦄ → ∀{a b} → (x ^ a ≡ x ^ b) ↔ (ord(x) ⦃ p ⦄ ∣ (a 𝄩 b))

    [^]-by-id-div : ⦃ p : Ord(x) ⦄ → ∀{n} → (x ^ n ≡ id) ↔ (ord(x) ⦃ p ⦄ ∣ n)
    [^]-by-id-div ⦃ p ⦄ {n} = [↔]-intro (l{n}) (r{n}) where
      l : ∀{n} → (x ^ n ≡ id) ← (ord(x) ⦃ p ⦄ ∣ n)
      l {.0}                  Div𝟎 = repeatₗ-by-0 {X = T}{_▫_}{x}{id}
      l {.(ord(x) ⦃ p ⦄ + n)} (Div𝐒 {_}{n} div) =
        x ^ (ord x ⦃ p ⦄ + n)       🝖-[ symmetry(_≡_) ([^]-by-add {ord(x) ⦃ p ⦄}{n}) ]
        (x ^ ord x ⦃ p ⦄) ▫ (x ^ n) 🝖-[ [≡]-with2(_▫_) ([^]-by-ord ⦃ p ⦄) (l{n} div) ]
        id ▫ id                     🝖-[ identityₗ(_▫_)(id) ]
        id                          🝖-end

      r : ∀{n} → (x ^ n ≡ id) → (ord(x) ⦃ p ⦄ ∣ n)
      r {n} xnid = divides-intro-alt {n ⌊/⌋₀ ord(x) ⦃ p ⦄} ⦃ {!!} ⦄ where
        open import Relator.Equals.Proofs.Equivalence using ([≡]-to-equivalence)

        instance ord-non-zero-comp : IsTrue(ord(x) ⦃ p ⦄ ≢? 𝟎)
        instance
          ord-n-ineq : ord(x) ⦃ p ⦄ ≤ n
          ord-n-ineq = ord-is-minimum ⦃ p ⦄ xnid

        [^]-functionᵣ : Function(x ^_)

        mod-is-id : x ^ (n mod ord(x) ⦃ p ⦄) ≡ id
        mod-is-id =
          x ^ (n mod ord(x) ⦃ p ⦄)                                                  🝖-[ symmetry(_≡_) (identityₗ(_▫_)(id)) ]
          id ▫ (x ^ (n mod ord(x) ⦃ p ⦄))                                           🝖-[ [≡]-with2ₗ(_▫_)(_) (symmetry(_≡_) ([^]-by-id-multiple {ord(x) ⦃ p ⦄} ([^]-by-ord ⦃ p ⦄) {n ⌊/⌋ ord(x) ⦃ p ⦄})) ]
          (x ^ ((ord(x) ⦃ p ⦄) ⋅ (n ⌊/⌋ ord(x) ⦃ p ⦄))) ▫ (x ^ (n mod ord(x) ⦃ p ⦄)) 🝖-[ [^]-by-add {(ord(x) ⦃ p ⦄) ⋅ (n ⌊/⌋ ord(x) ⦃ p ⦄)} {n mod ord(x) ⦃ p ⦄} ]
          x ^ (((ord(x) ⦃ p ⦄) ⋅ (n ⌊/⌋ ord(x) ⦃ p ⦄)) + (n mod ord(x) ⦃ p ⦄))       🝖-[ [≡]-with(x ^_) ⦃ [^]-functionᵣ ⦄ ([≡]-to-equivalence(division-remainder{n}{ord(x) ⦃ p ⦄})) ]
          x ^ n                                                                     🝖-[ xnid ]
          id                                                                        🝖-end
      {-(n ⌊/⌋ ord(x) ⦃ p ⦄) ⋅ (ord(x) ⦃ p ⦄)
      n

      {
        
      }
      n mod ord(x) ⦃ p ⦄ < ord(x) ⦃ p ⦄
      n mod ord(x) ⦃ p ⦄ ≡ 𝟎

      -}

{-
  module _ {id} ⦃ ident : Identity(_▫_)(id) ⦄ where
    open import Data.Boolean
    open import Data.Boolean.Stmt
    import      Functional.Repeat
    open import Logic.Computability
    open import Logic.Computability.Binary renaming (ComputablyDecidable to ComputablyDecidable2)
    open import Logic

    open import Numeral.Natural.Relation.Computability
    
    

-}
    {-
    boundedMinOr : ℕ → (ℕ → Bool) → ℕ → ℕ
    boundedMinOr 𝟎          p default = default
    boundedMinOr (𝐒(bound)) p default = if p(bound) then bound else (boundedMinOr bound p default)

    boundedMinOr-proof : ∀{p : ℕ → Bool}{bound default : ℕ} → IsTrue(p(default)) → IsTrue(p(boundedMinOr bound p default))

    min-by-bruteforce : ∀{ℓ}{P : ℕ → Stmt{ℓ}} → ⦃ comp : ComputablyDecidable(P) ⦄ → ⦃ e : ∃(P) ⦄ → ∃(Weak.Properties.MinimumOf(_≤_)(P))
    ∃.witness (min-by-bruteforce {P = P} ⦃ comp ⦄ ⦃ e ⦄) = boundedMinOr([∃]-witness(e)) (ComputablyDecidable.decide(comp)) ([∃]-witness(e))
    Weak.Properties.MinimumOf.proof (∃.proof min-by-bruteforce) {x} ⦃ x₁ ⦄ = {!!}

    ord : (x : T) → ⦃ e : FiniteOrder(x) ⦄ → ⦃ comp : ComputablyDecidable2{X = T}(_≡_) ⦄ → ℕ
    ord(x) ⦃ e ⦄ ⦃ comp ⦄ = Weak.minOf(_≤_)(n ↦ x ^ 𝐒(n) ≡ id) ⦃ min-by-bruteforce ⦃ {!!} ⦄ ⦃ e ⦄ ⦄
    -}
