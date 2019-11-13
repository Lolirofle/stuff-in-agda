module Structure.OrderedField where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
import      Data.Either as Either
open import Functional
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural using (ℕ)
import      Numeral.Natural.Relation.Order as ℕ
open import Relator.Ordering
open import Sets.Setoid
open import Structure.Function.Ordering
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Group
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Weak.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

-- Theory defining the axioms of an ordered field (a field with a weak total order).
record OrderedField {ℓ₁ ℓ₂} {F : Type{ℓ₁}} ⦃ _ : Equiv(F) ⦄ (_+_ _⋅_ : F → F → F) (_≤_ : F → F → Stmt{ℓ₂}) : Type{ℓ₁ Lvl.⊔ Lvl.𝐒(ℓ₂)} where
  field
    ⦃ [+][⋅]-field ⦄ : Field(_+_)(_⋅_)

  open Field([+][⋅]-field) public
  open From-[≤][≡] (_≤_)(_≡_) public

  field
    ⦃ [≤]-totalOrder ⦄ : Weak.TotalOrder(_≤_)(_≡_)
    [≤][+]ₗ-preserve   : ∀{x y z} → (x ≤ y) → ((x + z) ≤ (y + z))
    [≤][⋅]-zero        : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))

    -- TODO: Usually these would hold because of [≡]-substitution, but now?
    [≡]-to-[≤] : ∀{x y} → (x ≡ y) → (x ≤ y)
    [≡]-to-[≥] : ∀{x y} → (x ≡ y) → (x ≥ y)


  record NonNegative (x : F) : Stmt{ℓ₂} where
    constructor intro
    field proof : (x ≥ 𝟎)

  record Positive (x : F) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : (x > 𝟎)

  ‖_‖ : F → F
  ‖ x ‖ = if Either.bool(converseTotal(_≤_){𝟎}{x}) then (− x) else x

  [−]-of-𝟎 : ((− 𝟎) ≡ 𝟎)
  [−]-of-𝟎 =
    − 𝟎       🝖-[ symmetry(_≡_) (identityₗ(_+_)(𝟎)) ]
    𝟎 + (− 𝟎) 🝖-[ inverseFunctionᵣ(_+_)(−_) ]
    𝟎         🝖-end

  [≤][+]ᵣ-preserve : ∀{x y z} → (y ≤ z) → ((x + y) ≤ (x + z))
  [≤][+]ᵣ-preserve {x}{y}{z} yz =
    x + y       🝖-[ [≡]-to-[≤] (commutativity(_+_)) ]
    y + x       🝖-[ [≤][+]ₗ-preserve yz ]
    z + x       🝖-[ [≡]-to-[≤] (commutativity(_+_)) ]
    x + z       🝖-end

  [≤]-flip-positive : ∀{x} → (𝟎 ≤ x) → ((− x) ≤ 𝟎)
  [≤]-flip-positive {x} p =
    − x       🝖-[ [≡]-to-[≤] (symmetry(_≡_) (identityₗ(_+_)(𝟎))) ]
    𝟎 + (− x) 🝖-[ [≤][+]ₗ-preserve p ]
    x + (− x) 🝖-[ [≡]-to-[≤] (inverseFunctionᵣ(_+_)(−_)) ]
    𝟎         🝖-end

  instance
    [+]-cancellationᵣ : Cancellationᵣ(_+_)
    [+]-cancellationᵣ = One.cancellationᵣ-by-associativity-inverse

  [−−]-elim : ∀{x} → (−(− x) ≡ x)
  [−−]-elim = One.double-inverse

  [≤]-with-[−] : ∀{x y} → (x ≤ y) → ((− y) ≤ (− x))
  [≤]-with-[−] {x}{y} xy = proof4 proof3 where
    proof0 : ∀{x y} → (𝟎 ≤ (y − x)) → (x ≤ y) -- TODO: Unused. Move somewhere else if neccessary
    proof0 {x}{y} 𝟎yx =
      x               🝖-[ [≡]-to-[≤] (symmetry(_≡_) (identityₗ(_+_)(𝟎))) ]
      𝟎 + x           🝖-[ [≤][+]ₗ-preserve 𝟎yx ]
      (y − x) + x     🝖-[ reflexivity(_≤_) ]
      (y + (− x)) + x 🝖-[ [≡]-to-[≤] (associativity(_+_)) ]
      y + ((− x) + x) 🝖-[ [≡]-to-[≤] ([≡]-with2ᵣ(_+_)(_) (inverseFunctionₗ(_+_)(−_))) ]
      y + 𝟎           🝖-[ [≡]-to-[≤] (identityᵣ(_+_)(𝟎)) ]
      y               🝖-end

    proof3 : (((− y) − (− x)) ≤ 𝟎)
    proof3 =
      (− y) − (− x) 🝖-[ [≡]-to-[≤] ([≡]-with2ᵣ(_+_)(_) [−−]-elim) ]
      (− y) + x     🝖-[ [≡]-to-[≤] (commutativity(_+_)) ]
      x − y         🝖-[ [≤][+]ₗ-preserve xy ]
      y − y         🝖-[ [≡]-to-[≤] (inverseFunctionᵣ(_+_)(−_)) ]
      𝟎             🝖-end

    proof4 : ∀{x y} → ((x − y) ≤ 𝟎) → (x ≤ y)
    proof4 {x}{y} xy𝟎 =
      x               🝖-[ [≡]-to-[≤] (symmetry(_≡_) (identityᵣ(_+_)(𝟎))) ]
      x + 𝟎           🝖-[ [≡]-to-[≤] (symmetry(_≡_) ([≡]-with2ᵣ(_+_)(_) (inverseFunctionₗ(_+_)(−_)))) ]
      x + ((− y) + y) 🝖-[ [≡]-to-[≤] (symmetry(_≡_) (associativity(_+_))) ]
      (x + (− y)) + y 🝖-[ reflexivity(_≤_) ]
      (x − y) + y     🝖-[ [≤][+]ₗ-preserve xy𝟎 ]
      𝟎 + y           🝖-[ [≡]-to-[≤] (identityₗ(_+_)(𝟎)) ]
      y               🝖-end

  [≤]-flip-negative : ∀{x} → (x ≤ 𝟎) → (𝟎 ≤ (− x))
  [≤]-flip-negative {x} p =
    𝟎   🝖-[ [≡]-to-[≤](symmetry(_≡_) [−]-of-𝟎) ]
    − 𝟎 🝖-[ [≤]-with-[−] {x}{𝟎} p ]
    − x 🝖-end

  abs-positive : ∀{x} → (‖ x ‖ ≥ 𝟎)
  abs-positive{x} = if-either-bool-intro {P = _≥ 𝟎} {x = x} {y = − x} id [≤]-flip-negative (converseTotal(_≤_){𝟎}{x})

  -- Distance
  _𝄩_ : F → F → F
  x 𝄩 y = ‖ x − y ‖

  instance
    postulate [𝄩]-commutativity : Commutativity(_𝄩_)

  postulate [𝄩]-triangle-inequality : ∀{x y z} → ((x 𝄩 z) ≤ ((x 𝄩 y) + (y 𝄩 z)))

  postulate [𝄩]-self : ∀{x y} → (x 𝄩 y ≡ 𝟎) ↔ (x ≡ y)
