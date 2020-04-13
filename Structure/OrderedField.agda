module Structure.OrderedField where

import      Lvl
open import Data.Boolean
open import Data.Boolean.Proofs
import      Data.Either as Either
open import Data.Tuple as Tuple
open import Functional
open import Logic
open import Logic.Classical
open import Logic.IntroInstances
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural using (ℕ)
import      Numeral.Natural.Relation.Order as ℕ
open import Relator.Ordering
import      Relator.Ordering.Proofs as OrderingProofs
open import Structure.Setoid
open import Structure.Function.Domain
open import Structure.Function.Ordering
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Group
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Operator
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
  open From-[≤] (_≤_) public

  field
    ⦃ [≤]-totalOrder ⦄ : Weak.TotalOrder(_≤_)(_≡_)
    [≤][+]ₗ-preserve   : ∀{x y z} → (x ≤ y) → ((x + z) ≤ (y + z))
    [≤][⋅]-zero        : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))

    -- TODO: Usually these would hold because of [≡]-substitution, but now?
    -- TODO: Make _≤_ respect the equivalence
    ⦃ [≡][≤]-sub ⦄ : (_≡_) ⊆₂ (_≤_)

  open OrderingProofs.From-[≤] (_≤_) public

  record NonNegative (x : F) : Stmt{ℓ₂} where
    constructor intro
    field proof : (x ≥ 𝟎)

  record Positive (x : F) : Stmt{ℓ₁ Lvl.⊔ ℓ₂} where
    constructor intro
    field proof : (x > 𝟎)

  -- TODO: Stuff provable in fields
  instance
    postulate [−]-binaryOperator : BinaryOperator(_−_)

  instance
    [+]-cancellationₗ : Cancellationₗ(_+_)
    [+]-cancellationₗ = One.cancellationₗ-by-associativity-inverse

  instance
    [+]-cancellationᵣ : Cancellationᵣ(_+_)
    [+]-cancellationᵣ = One.cancellationᵣ-by-associativity-inverse

  [−−]-elim : ∀{x} → (−(− x) ≡ x)
  [−−]-elim = One.double-inverse

  [+]-negation-distribution : ∀{x y} → (−(x + y) ≡ (− x) + (− y))
  [+]-negation-distribution = One.inverse-distribution 🝖 commutativity(_+_)

  [−]-negation-distribution : ∀{x y} → (−(x − y) ≡ y − x)
  [−]-negation-distribution = One.inverse-distribution 🝖 congruence₂ₗ(_−_)(_) [−−]-elim

  instance
    [−]-involution : Involution(−_)
    [−]-involution = intro [−−]-elim

  zero-when-redundant-addition : ∀{x} → (x ≡ x + x) → (x ≡ 𝟎)
  zero-when-redundant-addition {x} p = cancellationᵣ(_+_) $ symmetry(_≡_) $
    𝟎 + x 🝖-[ identityₗ(_+_)(𝟎) ]
    x     🝖-[ p ]
    x + x 🝖-end

  -- TODO: See abs-of-negation for a similiar proof
  postulate zero-when-equal-negation : ∀{x} → (− x ≡ x) → (x ≡ 𝟎)

  instance
    [⋅]-absorberₗ : Absorberₗ(_⋅_)(𝟎)
    Absorberₗ.proof [⋅]-absorberₗ {x} = zero-when-redundant-addition $
      𝟎 ⋅ x             🝖-[ congruence₂ₗ(_⋅_)(x) (identityₗ(_+_)(𝟎)) ]-sym
      (𝟎 + 𝟎) ⋅ x       🝖-[ distributivityᵣ(_⋅_)(_+_) ]
      (𝟎 ⋅ x) + (𝟎 ⋅ x) 🝖-end

  instance
    [⋅]-absorberᵣ : Absorberᵣ(_⋅_)(𝟎)
    [⋅]-absorberᵣ = [↔]-to-[→] One.absorber-equivalence-by-commutativity [⋅]-absorberₗ

  instance
     [+]-inversePropₗ : InversePropertyₗ(_+_)(−_)
     [+]-inversePropₗ = One.inverse-propertyₗ-by-groupₗ

  instance
     [+]-inversePropᵣ : InversePropertyᵣ(_+_)(−_)
     [+]-inversePropᵣ = One.inverse-propertyᵣ-by-groupᵣ

  instance
    [+][−]-inverseOperᵣ : InverseOperatorᵣ(_+_)(_−_)
    [+][−]-inverseOperᵣ = One.standard-inverse-operatorᵣ-by-involuting-inverse-propᵣ

  instance
    [−][+]-inverseOperᵣ : InverseOperatorᵣ(_−_)(_+_)
    [−][+]-inverseOperᵣ = One.standard-inverse-inverse-operatorᵣ-by-inverse-propᵣ

  -- TODO: Defined set subset of natural numbers and integers by using summation ∑. That is: (x ∈ ℕ) = ∃{Obj = ℕ}(n ↦ ∑(0 ‥ n) (const 𝟏))

  [−]-of-𝟎 : ((− 𝟎) ≡ 𝟎)
  [−]-of-𝟎 =
    − 𝟎       🝖-[ symmetry(_≡_) (identityₗ(_+_)(𝟎)) ]
    𝟎 + (− 𝟎) 🝖-[ inverseFunctionᵣ(_+_)(−_) ]
    𝟎         🝖-end

  [≤][+]ᵣ-preserve : ∀{x y z} → (y ≤ z) → ((x + y) ≤ (x + z))
  [≤][+]ᵣ-preserve {x}{y}{z} yz =
    x + y       🝖[ _≡_ ]-[ commutativity(_+_) ]-sub
    y + x       🝖[ _≤_ ]-[ [≤][+]ₗ-preserve yz ]
    z + x       🝖[ _≡_ ]-[ commutativity(_+_) ]-sub
    x + z       🝖-end

  [≤][+]-preserve : ∀{x₁ x₂ y₁ y₂} → (x₁ ≤ x₂) → (y₁ ≤ y₂) → ((x₁ + y₁) ≤ (x₂ + y₂))
  [≤][+]-preserve {x₁}{x₂}{y₁}{y₂} px py =
    x₁ + y₁ 🝖[ _≤_ ]-[ [≤][+]ₗ-preserve px ]
    x₂ + y₁ 🝖[ _≤_ ]-[ [≤][+]ᵣ-preserve py ]
    x₂ + y₂ 🝖[ _≤_ ]-end

  [≤]-flip-positive : ∀{x} → (𝟎 ≤ x) → ((− x) ≤ 𝟎)
  [≤]-flip-positive {x} p =
    − x       🝖-[ sub₂(_≡_)(_≤_) (symmetry(_≡_) (identityₗ(_+_)(𝟎))) ]
    𝟎 + (− x) 🝖-[ [≤][+]ₗ-preserve p ]
    x + (− x) 🝖-[ sub₂(_≡_)(_≤_) (inverseFunctionᵣ(_+_)(−_)) ]
    𝟎         🝖-end

  [≤]-with-[−] : ∀{x y} → (x ≤ y) → ((− y) ≤ (− x))
  [≤]-with-[−] {x}{y} xy = proof4 proof3 where
    proof0 : ∀{x y} → (𝟎 ≤ (y − x)) → (x ≤ y) -- TODO: Unused. Move somewhere else if neccessary
    proof0 {x}{y} 𝟎yx =
      x               🝖-[ sub₂(_≡_)(_≤_) (symmetry(_≡_) (identityₗ(_+_)(𝟎))) ]
      𝟎 + x           🝖-[ [≤][+]ₗ-preserve 𝟎yx ]
      (y − x) + x     🝖-[ reflexivity(_≤_) ]
      (y + (− x)) + x 🝖-[ sub₂(_≡_)(_≤_) (associativity(_+_)) ]
      y + ((− x) + x) 🝖-[ sub₂(_≡_)(_≤_) (congruence₂ᵣ(_+_)(_) (inverseFunctionₗ(_+_)(−_))) ]
      y + 𝟎           🝖-[ sub₂(_≡_)(_≤_) (identityᵣ(_+_)(𝟎)) ]
      y               🝖-end

    proof3 : (((− y) − (− x)) ≤ 𝟎)
    proof3 =
      (− y) − (− x) 🝖-[ sub₂(_≡_)(_≤_) (congruence₂ᵣ(_+_)(_) [−−]-elim) ]
      (− y) + x     🝖-[ sub₂(_≡_)(_≤_) (commutativity(_+_)) ]
      x − y         🝖-[ [≤][+]ₗ-preserve xy ]
      y − y         🝖-[ sub₂(_≡_)(_≤_) (inverseFunctionᵣ(_+_)(−_)) ]
      𝟎             🝖-end

    proof4 : ∀{x y} → ((x − y) ≤ 𝟎) → (x ≤ y)
    proof4 {x}{y} xy𝟎 =
      x               🝖-[ sub₂(_≡_)(_≤_) (symmetry(_≡_) (identityᵣ(_+_)(𝟎))) ]
      x + 𝟎           🝖-[ sub₂(_≡_)(_≤_) (symmetry(_≡_) (congruence₂ᵣ(_+_)(_) (inverseFunctionₗ(_+_)(−_)))) ]
      x + ((− y) + y) 🝖-[ sub₂(_≡_)(_≤_) (symmetry(_≡_) (associativity(_+_))) ]
      (x + (− y)) + y 🝖-[ reflexivity(_≤_) ]
      (x − y) + y     🝖-[ [≤][+]ₗ-preserve xy𝟎 ]
      𝟎 + y           🝖-[ sub₂(_≡_)(_≤_) (identityₗ(_+_)(𝟎)) ]
      y               🝖-end

  [≤]-flip-negative : ∀{x} → (x ≤ 𝟎) ↔ (𝟎 ≤ (− x))
  [≤]-flip-negative {x} = [↔]-intro l r where
    r = \p →
      𝟎   🝖-[ sub₂(_≡_)(_≤_) (symmetry(_≡_) [−]-of-𝟎) ]
      − 𝟎 🝖-[ [≤]-with-[−] {x}{𝟎} p ]
      − x 🝖-end

    l = \p →
      x      🝖-[ sub₂(_≡_)(_≤_) (symmetry(_≡_) (involution(−_))) ]
      −(− x) 🝖-[ [≤]-with-[−] p ]
      − 𝟎    🝖-[ sub₂(_≡_)(_≤_) [−]-of-𝟎 ]
      𝟎      🝖-end

  [≤][−]ₗ-preserve : ∀{x y z} → (x ≤ y) → ((x − z) ≤ (y − z))
  [≤][−]ₗ-preserve = [≤][+]ₗ-preserve

  [≤][−]ᵣ-preserve : ∀{x y z} → (z ≤ y) → ((x − y) ≤ (x − z))
  [≤][−]ᵣ-preserve = [≤][+]ᵣ-preserve ∘ [≤]-with-[−]

  [≤][+]-withoutᵣ : ∀{x₁ x₂ y} → ((x₁ + y) ≤ (x₂ + y)) → (x₁ ≤ x₂)
  [≤][+]-withoutᵣ {x₁}{x₂}{y} p =
    x₁           🝖[ _≡_ ]-[ symmetry(_≡_) (inverseOperᵣ(_−_)(_+_)) ]-sub
    (x₁ + y) − y 🝖[ _≤_ ]-[ [≤][−]ₗ-preserve p ]
    (x₂ + y) − y 🝖[ _≡_ ]-[ inverseOperᵣ(_−_)(_+_) ]-sub
    x₂           🝖-end

  [≤][+]-withoutₗ : ∀{x y₁ y₂} → ((x + y₁) ≤ (x + y₂)) → (y₁ ≤ y₂)
  [≤][+]-withoutₗ {x}{y₁}{y₂} p =
    y₁               🝖[ _≡_ ]-[ symmetry(_≡_) (inversePropₗ(_+_)(−_)) ]-sub
    (− x) + (x + y₁) 🝖[ _≤_ ]-[ [≤][+]ᵣ-preserve p ]
    (− x) + (x + y₂) 🝖[ _≡_ ]-[ inversePropₗ(_+_)(−_) ]-sub
    y₂               🝖-end

  [<][+]-preserveₗ : ∀{x₁ x₂ y} → (x₁ < x₂) → ((x₁ + y) < (x₂ + y))
  [<][+]-preserveₗ {x₁}{x₂}{y} px p = px ([≤][+]-withoutᵣ p)

  [<][+]-preserveᵣ : ∀{x y₁ y₂} → (y₁ < y₂) → ((x + y₁) < (x + y₂))
  [<][+]-preserveᵣ {x₁}{x₂}{y} px p = px ([≤][+]-withoutₗ p)

  [<][+]-preserve : ∀{x₁ x₂ y₁ y₂} → (x₁ < x₂) → (y₁ < y₂) → ((x₁ + y₁) < (x₂ + y₂))
  [<][+]-preserve {x₁}{x₂}{y₁}{y₂} px py =
    x₁ + y₁ 🝖[ _<_ ]-[ [<][+]-preserveₗ px ]
    x₂ + y₁ 🝖-semiend
    x₂ + y₂ 🝖[ _<_ ]-end-from-[ [<][+]-preserveᵣ py ]
  
  postulate [<][+]-preserve-subₗ : ∀{x₁ x₂ y₁ y₂} → (x₁ ≤ x₂) → (y₁ < y₂) → ((x₁ + y₁) < (x₂ + y₂))
  postulate [<][+]-preserve-subᵣ : ∀{x₁ x₂ y₁ y₂} → (x₁ < x₂) → (y₁ ≤ y₂) → ((x₁ + y₁) < (x₂ + y₂))
