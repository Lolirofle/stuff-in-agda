module Function.Iteration.Order where

open import Data
open import Data.Boolean.Stmt
open import Functional renaming (id to id-fn)
open import Function.Iteration hiding (_^_)
open import Function.Iteration.Proofs
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper hiding (_^_)
open import Numeral.Natural.Oper.Comparisons
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.Modulo
open import Numeral.Natural.Oper.Modulo.Proofs
open import Numeral.Natural.Relation.Divisibility
open import Numeral.Natural.Relation.Divisibility.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals using () renaming (_≡_ to _≡ₑ_ ; _≢_ to _≢ₑ_ ; [≡]-intro to [≡ₑ]-intro)
open import Sets.Setoid
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Operator.Proofs
open import Structure.Relator.Properties
open import Structure.Relator.Ordering
open import Syntax.Transitivity
open import Type
open import Type.Empty
open import Type.Size.Finite

module _ {ℓ} {T : Type{ℓ}} ⦃ equiv-T : Equiv(T) ⦄ (_▫_ : T → T → T) ⦃ op : BinaryOperator(_▫_) ⦄ {id} ⦃ ident : Identity(_▫_)(id) ⦄ ⦃ assoc : Associativity(_▫_) ⦄ where
  -- Operator alias for iterated application of an operator with an element.
  _^_ : T → ℕ → T
  x ^ n = Function.Iteration.repeatₗ(n)(_▫_)(id)(x)

  -- `FiniteOrder(x)(n)` means that the element `x` is of order `n`.
  -- It is finite in the sense that it is a number and not infinite.
  -- An element's order is the smallest positive integer power of x such that the result is the identity element.
  data FiniteOrder (x : T) : ℕ → Stmt{ℓ} where
    intro : ∀{n} → Weak.Properties.MinimumOf(_≤_)(n ↦ x ^ 𝐒(n) ≡ id)(n) → FiniteOrder(x)(𝐒(n))

  -- `Ord(x)` means that the element `x` has a finite order.
  Ord : T → Stmt{ℓ}
  Ord(x) = ∃(FiniteOrder(x))

  -- `ord(x)` is the order of x (when it is finite).
  ord : (x : T) → ⦃ _ : Ord(x) ⦄ → ℕ
  ord(_) ⦃ [∃]-intro n ⦄ = n

  module _ {x : T} where
    -- An order is never 0 by definition.
    finite-order-0 : ¬ FiniteOrder(x)(𝟎)
    finite-order-0 ()

    -- An element power its order is the identity element.
    [^]-by-ord : ⦃ p : Ord(x) ⦄ → (x ^ ord(x) ⦃ p ⦄ ≡ id)
    [^]-by-ord ⦃ [∃]-intro (𝐒(_)) ⦃ intro p ⦄ ⦄ = Weak.Properties.MinimumOf.proof(p)

    -- When an element power something is the identity element, then the power is either zero or greater/equal its order.
    ord-is-minimum : ⦃ p : Ord(x) ⦄ → ∀{n} → (x ^ n ≡ id) → (n ≡ₑ 𝟎) ∨ (ord(x) ⦃ p ⦄ ≤ n)
    ord-is-minimum ⦃ [∃]-intro (_)     ⦃ intro p ⦄ ⦄      {𝟎}   x0id  = [∨]-introₗ [≡ₑ]-intro
    ord-is-minimum ⦃ [∃]-intro .(𝐒 po) ⦃ intro {po} p ⦄ ⦄ {𝐒 n} xsnid = [∨]-introᵣ ([≤]-with-[𝐒] ⦃ Weak.Properties.MinimumOf.minimum(p) ⦃ xsnid ⦄ ⦄)

    -- When an element power something less than its order and it is the identity element, then the power is 0.
    ord-is-minimum-but-0 : ⦃ p : Ord(x) ⦄ → ∀{n} → (x ^ n ≡ id) → (n < ord(x) ⦃ p ⦄) → (n ≡ₑ 𝟎)
    ord-is-minimum-but-0 ⦃ p ⦄ {𝟎}    _    _    = [≡ₑ]-intro
    ord-is-minimum-but-0 ⦃ p ⦄ {𝐒(n)} xnid nord with ord-is-minimum ⦃ p ⦄ {𝐒(n)} xnid
    ... | [∨]-introᵣ ordsn = [⊥]-elim([<]-to-[≱] nord (ordsn))

    -- An order is never 0.
    ord-non-zero : ⦃ p : Ord(x) ⦄ → (ord(x) ⦃ p ⦄ ≢ₑ 𝟎)
    ord-non-zero ⦃ [∃]-intro 𝟎 ⦃ ⦄ ⦄ [≡ₑ]-intro

    -- Iteration (_^_) distributes to the right.
    -- Can also be seen as iteration preserving from addition to the operation.
    [^]-by-add : ∀{a b} → ((x ^ a) ▫ (x ^ b) ≡ x ^ (a + b))
    [^]-by-add {a}{b} = repeatₗ-by-sum {X = T}{_▫_}{x}{id}{a}{b}

    -- Nested iterations can join to be a product.
    [^]-by-product : ∀{a b} → ((((x ^ a)) ^ b) ≡ x ^ (a ⋅ b))
    [^]-by-product {a}{b} = repeatₗ-by-product {X = T}{_▫_}{x}{id}{a}{b}

    -- When powering a difference yields the identity element, the powered elements are the same.
    [^]-by-distanceₗ : ∀{a b} → (x ^ a ≡ x ^ b) ← (x ^ (a 𝄩 b) ≡ id)
    [^]-by-distanceₗ {a}{b} = repeatₗ-by-distanceₗ {X = T}{_▫_}{x}{id}{a}{b}

    -- Theorems where `n` is a power which yields an identity element.
    module _ {n} (n-id : (x ^ n ≡ id)) where
      -- Adding something to `n` is only leaving the something behind.
      [^]-by-id-add : ∀{a} → (x ^ (n + a)  ≡ x ^ a)
      [^]-by-id-add {a} =
        x ^ (n + a)       🝖-[ symmetry(_≡_) ([^]-by-add {n}{a}) ]
        (x ^ n) ▫ (x ^ a) 🝖-[ [≡]-with2ₗ(_▫_)(_) n-id ]
        id ▫ (x ^ a)      🝖-[ identityₗ(_▫_)(id) ]
        x ^ a             🝖-end

      -- Multiplying something by `n` is still the identity element.
      [^]-by-id-multiple : ∀{a} → (x ^ (n ⋅ a) ≡ id)
      [^]-by-id-multiple {𝟎}    = repeatₗ-by-0 {X = T}{_▫_}{x}{id}
      [^]-by-id-multiple {𝐒(a)} =
        x ^ (n + (n ⋅ a))       🝖-[ symmetry(_≡_) ([^]-by-add {n}{n ⋅ a}) ]
        (x ^ n) ▫ (x ^ (n ⋅ a)) 🝖-[ [≡]-with2(_▫_) n-id ([^]-by-id-multiple {a}) ]
        id ▫ id                 🝖-[ identityₗ(_▫_)(id) ]
        id                      🝖-end

    -- A power yields an identity element only when it is a multiple of the order of the element.
    [^]-id-when-div : ⦃ p : Ord(x) ⦄ → ∀{n} → (x ^ n ≡ id) ↔ (ord(x) ⦃ p ⦄ ∣ n)
    [^]-id-when-div ⦃ p ⦄ {n} = [↔]-intro (l{n}) (r{n}) where
      l : ∀{n} → (x ^ n ≡ id) ← (ord(x) ⦃ p ⦄ ∣ n)
      l {.0}                  Div𝟎 = repeatₗ-by-0 {X = T}{_▫_}{x}{id}
      l {.(ord(x) ⦃ p ⦄ + n)} (Div𝐒 {_}{n} div) =
        x ^ (ord x ⦃ p ⦄ + n)       🝖-[ symmetry(_≡_) ([^]-by-add {ord(x) ⦃ p ⦄}{n}) ]
        (x ^ ord x ⦃ p ⦄) ▫ (x ^ n) 🝖-[ [≡]-with2(_▫_) ([^]-by-ord ⦃ p ⦄) (l{n} div) ]
        id ▫ id                     🝖-[ identityₗ(_▫_)(id) ]
        id                          🝖-end

      r : ∀{n} → (x ^ n ≡ id) → (ord(x) ⦃ p ⦄ ∣ n)
      r {𝟎}    _    = Div𝟎
      r {𝐒(n)} xnid = [↔]-to-[→] mod-divisibility mod-is-0 where
        open import Logic.Computability
        open import Numeral.Natural.Relation.Computability
        open import Relator.Equals.Proofs.Equivalence using ([≡]-to-equivalence)

        instance
          ord-non-zero-comp : IsTrue(ord(x) ⦃ p ⦄ ≢? 𝟎)
          ord-non-zero-comp = [↔]-to-[→] (ComputablyDecidable.proof-istrue([≢]-computable)) (ord-non-zero ⦃ p ⦄)

        instance
          ord-n-ineq : ord(x) ⦃ p ⦄ ≤ 𝐒(n)
          ord-n-ineq with ord-is-minimum ⦃ p ⦄ {𝐒(n)} xnid
          ord-n-ineq | [∨]-introₗ ()
          ord-n-ineq | [∨]-introᵣ proof      = proof

        mod-is-id : x ^ (𝐒(n) mod ord(x) ⦃ p ⦄) ≡ id
        mod-is-id =
          x ^ (𝐒(n) mod ord(x) ⦃ p ⦄)                                                      🝖-[ symmetry(_≡_) (identityₗ(_▫_)(id)) ]
          id ▫ (x ^ (𝐒(n) mod ord(x) ⦃ p ⦄))                                               🝖-[ [≡]-with2ₗ(_▫_)(_) (symmetry(_≡_) ([^]-by-id-multiple {ord(x) ⦃ p ⦄} ([^]-by-ord ⦃ p ⦄) {𝐒(n) ⌊/⌋ ord(x) ⦃ p ⦄})) ]
          (x ^ ((ord(x) ⦃ p ⦄) ⋅ (𝐒(n) ⌊/⌋ ord(x) ⦃ p ⦄))) ▫ (x ^ (𝐒(n) mod ord(x) ⦃ p ⦄)) 🝖-[ [^]-by-add {(ord(x) ⦃ p ⦄) ⋅ (𝐒(n) ⌊/⌋ ord(x) ⦃ p ⦄)} {𝐒(n) mod ord(x) ⦃ p ⦄} ]
          x ^ (((ord(x) ⦃ p ⦄) ⋅ (𝐒(n) ⌊/⌋ ord(x) ⦃ p ⦄)) + (𝐒(n) mod ord(x) ⦃ p ⦄))       🝖-[ [≡]-with(x ^_) ⦃ Relator.Equals.Proofs.Equivalence.[≡]-to-function ⦄ ([≡]-to-equivalence(division-remainder{𝐒(n)}{ord(x) ⦃ p ⦄})) ]
          x ^ 𝐒(n)                                                                         🝖-[ xnid ]
          id                                                                               🝖-end

        mod-is-0 : 𝐒(n) mod ord(x) ⦃ p ⦄ ≡ 𝟎
        mod-is-0 = ord-is-minimum-but-0 ⦃ p ⦄ mod-is-id mod-maxᵣ

    module _ {inv} ⦃ _ : InverseFunctionᵣ(_▫_)(inv) ⦄ where
      [^]-by-distanceᵣ : ∀{a b} → (x ^ a ≡ x ^ b) → (x ^ (a 𝄩 b) ≡ id)
      [^]-by-distanceᵣ {a}{b} = repeatₗ-by-distanceᵣ{X = T}{_▫_}{x}{id} ⦃ cancᵣ = One.cancellationᵣ-by-associativity-inverse ⦄ {a}{b}

      [^]-equal-[𝄩] : ⦃ p : Ord(x) ⦄ → ∀{a b} → (x ^ a ≡ x ^ b) ↔ (ord(x) ⦃ p ⦄ ∣ (a 𝄩 b))
      [^]-equal-[𝄩] ⦃ p ⦄ {a}{b} = [↔]-transitivity ([↔]-intro ([^]-by-distanceₗ{a}{b}) ([^]-by-distanceᵣ{a}{b})) ([^]-id-when-div ⦃ p ⦄)

      postulate [^]-cancellationₗ : ⦃ p : Ord(x) ⦄ → ∀{a b} → ⦃ a < ord(x) ⦃ p ⦄ ⦄ → ⦃ b < ord(x) ⦃ p ⦄ ⦄ → (x ^ a ≡ x ^ b) → (a ≡ₑ b)

  -- ord(x ^ n) ≡ ord(x) / gcd(n)(ord(x))
  -- (x ▫ y ≡ y ▫ x) → ord(x ▫ y) ∣ lcm(ord(x))(ord(y))
  -- (∀{x} → (ord(x) ≡ 2)) → Commutativity(_▫_)

  -- One element in the group can "generate" any element element in the group by repeated application of the operator.
  Generator : T → Stmt{ℓ}
  Generator(x) = Surjective(x ^_)

  -- A group is cyclic when there is an element that can generate it.
  Cyclic : Stmt{ℓ}
  Cyclic = ∃(Generator)

  {- TODO: Because the thing exists, there is finitely many. Search for the first one
  finite-order-from-dec-existence : ⦃ Decidable(_≡_) ⦄ → ∀{a} → ∃(n ↦ (a ^ 𝐒(n) ≡ id)) → Ord(a)
  finite-order-from-dec-existence {n} asnid = {!!}
  -- intro (Weak.Properties.intro ⦃ asnid ⦄ {!!})

  -- TODO: Assume decidable equality and use finite-order-from-dec-existence above. Existence should follow from finiteness
  finite-have-order : ⦃ Finite(T) ⦄ → ∀{a} → Ord(a)
  ∃.witness (finite-have-order ⦃ [∃]-intro size ⦃ fin-bij ⦄ ⦄) = size
  ∃.proof (finite-have-order ⦃ [∃]-intro 𝟎 ⦃ [∃]-intro fin-bij ⦄ ⦄ {a = a}) with fin-bij a
  ... | ()
  ∃.proof (finite-have-order ⦃ [∃]-intro (𝐒(size)) ⦃ fin-bij ⦄ ⦄) = intro {!!}
  -}


  postulate cyclic-commutative : ⦃ Cyclic ⦄ → Commutativity(_▫_)
  -- generator-order-size : ⦃ Finite(T) ⦄ → ∀{a} → ⦃ p : Ord(a) ⦄ → Generator(a) ↔ ((# T) ≡ₑ ord(a) ⦃ p ⦄)
  -- cyclic-order-size : ⦃ Finite(T) ⦄ → ⦃ Cyclic ⦄ ↔ ∃(a ↦ (# T) ≡ₑ ord(a))

  -- generator-of-power : Generator(a ^ k) ↔ Generator(a ^ gcd(ord(a))(k))
  -- order-of-power : ord(a ^ k) ∣ ord(a) / gcd(ord(a),k)

{-
  module _ {id} ⦃ ident : Identity(_▫_)(id) ⦄ where
    open import Data.Boolean
    open import Data.Boolean.Stmt
    import      Function.Iteration
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
