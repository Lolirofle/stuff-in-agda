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
open import Structure.Setoid.WithLvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Ordering
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Group
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Weak.Properties
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₗ ℓₑ : Lvl.Level
private variable F : Type{ℓ}

-- TODO: Generalize so that this not neccessarily needs to be a ring
record Ordered ⦃ equiv : Equiv{ℓₑ}(F) ⦄ (_+_ _⋅_ : F → F → F) ⦃ ring : Ring(_+_)(_⋅_) ⦄ (_≤_ : F → F → Stmt{ℓₗ}) : Type{Lvl.of(F) Lvl.⊔ ℓₗ Lvl.⊔ ℓₑ} where
  open From-[≤] (_≤_) public
  open Ring(ring)

  field
    ⦃ [≤]-totalOrder ⦄    : Weak.TotalOrder(_≤_)(_≡_)
    [≤][+]ₗ-preserve      : ∀{x y z} → (x ≤ y) → ((x + z) ≤ (y + z))
    [≤][⋅]-zero           : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))
    ⦃ [≤]-binaryRelator ⦄ : BinaryRelator(_≤_)

  -- TODO: Move this to Structure.Relator.Order or something
  instance
    [≡][≤]-sub : (_≡_) ⊆₂ (_≤_)
    _⊆₂_.proof [≡][≤]-sub p = substitute₂ᵣ(_≤_) p (reflexivity(_≤_))

  open Weak.TotalOrder([≤]-totalOrder) public
  open OrderingProofs.From-[≤] (_≤_) public

  record NonNegative (x : F) : Stmt{ℓₗ} where
    constructor intro
    field proof : (x ≥ 𝟎)

  record Positive (x : F) : Stmt{ℓₗ} where
    constructor intro
    field proof : (x > 𝟎)

  -- TODO: Stuff provable in fields
  instance
    [−]-binaryOperator : BinaryOperator(_−_)
    BinaryOperator.congruence [−]-binaryOperator {x₁}{y₁}{x₂}{y₂} xy1 xy2 =
      (x₁ − x₂)     🝖[ _≡_ ]-[]
      (x₁ + (− x₂)) 🝖[ _≡_ ]-[ congruence₂(_+_) xy1 (congruence₁(−_) xy2) ]
      (y₁ + (− y₂)) 🝖[ _≡_ ]-[]
      (y₁ − y₂)     🝖-end

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
    Absorberᵣ.proof [⋅]-absorberᵣ {x} = zero-when-redundant-addition $
      x ⋅ 𝟎             🝖-[ congruence₂ᵣ(_⋅_)(x) (identityₗ(_+_)(𝟎)) ]-sym
      x ⋅ (𝟎 + 𝟎)       🝖-[ distributivityₗ(_⋅_)(_+_) ]
      (x ⋅ 𝟎) + (x ⋅ 𝟎) 🝖-end

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

  [−]-is-𝟎 : ∀{x} → ((− x) ≡ 𝟎) ↔ (x ≡ 𝟎)
  [−]-is-𝟎 = [↔]-intro (p ↦ congruence₁(−_) p 🝖 [−]-of-𝟎) (p ↦ symmetry(_≡_) [−−]-elim 🝖 congruence₁(−_) p 🝖 [−]-of-𝟎)

  module _ ⦃ unity : Unity(_+_)(_⋅_) ⦄ where
    open import Type.Properties.MereProposition
    open import Type.Properties.Singleton
    open import Type.Properties.Singleton.Proofs

    open Unity(unity)

    singleton-when-identities-equal : (𝟎 ≡ 𝟏) ↔ IsUnit(F)
    singleton-when-identities-equal = [↔]-intro l r where
      l : (𝟎 ≡ 𝟏) ← IsUnit(F)
      l p = uniqueness(_) ⦃ inst = unit-is-prop ⦃ proof = p ⦄ ⦄

      r : (𝟎 ≡ 𝟏) → IsUnit(F)
      IsUnit.unit       (r oi)     = 𝟎
      IsUnit.uniqueness (r oi) {x} =
        x     🝖[ _≡_ ]-[ identityᵣ(_⋅_)(𝟏) ]-sym
        x ⋅ 𝟏 🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(x) oi ]-sym
        x ⋅ 𝟎 🝖[ _≡_ ]-[ absorberᵣ(_⋅_)(𝟎) ]
        𝟎     🝖-end

    [⋅]ₗ-of-[−1] : ∀{x} → ((− 𝟏) ⋅ x ≡ − x)
    [⋅]ₗ-of-[−1] {x} = One.unique-inverseᵣ-by-id $
      x + ((− 𝟏) ⋅ x)       🝖-[ congruence₂ₗ(_+_)(_) (identityₗ(_⋅_)(𝟏)) ]-sym
      (𝟏 ⋅ x) + ((− 𝟏) ⋅ x) 🝖-[ distributivityᵣ(_⋅_)(_+_) ]-sym
      (𝟏 + (− 𝟏)) ⋅ x       🝖-[ congruence₂ₗ(_⋅_)(x) (inverseFunctionᵣ(_+_)(−_)) ]
      𝟎 ⋅ x                 🝖-[ absorberₗ(_⋅_)(𝟎) ]
      𝟎                     🝖-end

    [⋅]ᵣ-of-[−1] : ∀{x} → (x ⋅ (− 𝟏) ≡ − x)
    [⋅]ᵣ-of-[−1] {x} = One.unique-inverseₗ-by-id $
      (x ⋅ (− 𝟏)) + x       🝖-[ congruence₂ᵣ(_+_)(_) (identityᵣ(_⋅_)(𝟏)) ]-sym
      (x ⋅ (− 𝟏)) + (x ⋅ 𝟏) 🝖-[ distributivityₗ(_⋅_)(_+_) ]-sym
      x ⋅ ((− 𝟏) + 𝟏)       🝖-[ congruence₂ᵣ(_⋅_)(x) (inverseFunctionₗ(_+_)(−_)) ]
      x ⋅ 𝟎                 🝖-[ absorberᵣ(_⋅_)(𝟎) ]
      𝟎                     🝖-end

    [⋅]ₗ-of-[−] : ∀{x y} → ((− x) ⋅ y ≡ −(x ⋅ y))
    [⋅]ₗ-of-[−] {x}{y} =
      ((− x) ⋅ y)       🝖-[ congruence₂ₗ(_⋅_)(y) [⋅]ₗ-of-[−1] ]-sym
      (((− 𝟏) ⋅ x) ⋅ y) 🝖-[ associativity(_⋅_) ]
      ((− 𝟏) ⋅ (x ⋅ y)) 🝖-[ [⋅]ₗ-of-[−1] ]
      (−(x ⋅ y))        🝖-end

    [⋅]ᵣ-of-[−] : ∀{x y} → (x ⋅ (− y) ≡ −(x ⋅ y))
    [⋅]ᵣ-of-[−] {x}{y} =
      (x ⋅ (− y))       🝖-[ congruence₂ᵣ(_⋅_)(x) [⋅]ᵣ-of-[−1] ]-sym
      (x ⋅ (y ⋅ (− 𝟏))) 🝖-[ associativity(_⋅_) ]-sym
      ((x ⋅ y) ⋅ (− 𝟏)) 🝖-[ [⋅]ᵣ-of-[−1] ]
      (−(x ⋅ y))        🝖-end

    [⋅]-of-[−] : ∀{x y} → ((− x) ⋅ (− y) ≡ x ⋅ y)
    [⋅]-of-[−] {x}{y} =
      ((− x) ⋅ (− y)) 🝖[ _≡_ ]-[ [⋅]ᵣ-of-[−] ]
      −((− x) ⋅ y)    🝖[ _≡_ ]-[ congruence₁(−_) [⋅]ₗ-of-[−] ]
      −(−(x ⋅ y))     🝖[ _≡_ ]-[ [−−]-elim ]
      (x ⋅ y)         🝖-end

  [≤][+]ᵣ-preserve : ∀{x y z} → (y ≤ z) → ((x + y) ≤ (x + z))
  [≤][+]ᵣ-preserve {x}{y}{z} yz =
    x + y 🝖[ _≡_ ]-[ commutativity(_+_) ]-sub
    y + x 🝖[ _≤_ ]-[ [≤][+]ₗ-preserve yz ]
    z + x 🝖[ _≡_ ]-[ commutativity(_+_) ]-sub
    x + z 🝖-end

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

-- Theory defining the axioms of an ordered field (a field with a weak total order).
record OrderedField ⦃ equiv : Equiv{ℓₑ}(F) ⦄ (_+_ _⋅_ : F → F → F) (_≤_ : F → F → Stmt{ℓₗ}) : Type{Lvl.of(F) Lvl.⊔ ℓₗ Lvl.⊔ ℓₑ} where
  field
    ⦃ [+][⋅]-field ⦄ : Field(_+_)(_⋅_)
    ⦃ ordered ⦄      : Ordered(_+_)(_⋅_)(_≤_)

  open Field([+][⋅]-field) public
  open Ordered(ordered) public
