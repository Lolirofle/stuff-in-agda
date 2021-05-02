module Structure.Operator.Ring.Proofs where

import      Data.Tuple as Tuple
open import Functional
open import Logic.IntroInstances
open import Logic.Propositional
import      Lvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.Operator
open import Structure.Operator.Proofs
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Implication
open import Syntax.Transitivity
open import Type.Properties.MereProposition
open import Type.Properties.Singleton
open import Type.Properties.Singleton.Proofs
open import Type

private variable ℓ ℓₑ : Lvl.Level
private variable T : Type{ℓ}
private variable _+_ _⋅_ : T → T → T

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ rg : Rg{T = T}(_+_)(_⋅_) ⦄ where
  open Rg(rg)

  [⋅]-absorberₗ-by-cancellationᵣ : ⦃ canc : Cancellationᵣ(_+_) ⦄ → Absorberₗ(_⋅_)(𝟎)
  Absorberₗ.proof [⋅]-absorberₗ-by-cancellationᵣ {x} = One.zero-when-redundant-addition $
    𝟎 ⋅ x             🝖-[ congruence₂ₗ(_⋅_)(x) (identityₗ(_+_)(𝟎)) ]-sym
    (𝟎 + 𝟎) ⋅ x       🝖-[ distributivityᵣ(_⋅_)(_+_) ]
    (𝟎 ⋅ x) + (𝟎 ⋅ x) 🝖-end

  [⋅]-absorberᵣ-by-cancellationᵣ : ⦃ canc : Cancellationᵣ(_+_) ⦄ → Absorberᵣ(_⋅_)(𝟎)
  Absorberᵣ.proof [⋅]-absorberᵣ-by-cancellationᵣ {x} = One.zero-when-redundant-addition $
    x ⋅ 𝟎             🝖-[ congruence₂ᵣ(_⋅_)(x) (identityₗ(_+_)(𝟎)) ]-sym
    x ⋅ (𝟎 + 𝟎)       🝖-[ distributivityₗ(_⋅_)(_+_) ]
    (x ⋅ 𝟎) + (x ⋅ 𝟎) 🝖-end

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ rng : Rng{T = T}(_+_)(_⋅_) ⦄ where
  open Rng(rng)

  instance
    [+]-cancellationₗ : Cancellationₗ(_+_)
    [+]-cancellationₗ = One.cancellationₗ-by-associativity-inverse

  instance
    [+]-cancellationᵣ : Cancellationᵣ(_+_)
    [+]-cancellationᵣ = One.cancellationᵣ-by-associativity-inverse

  instance
    [⋅]-absorberₗ : Absorberₗ(_⋅_)(𝟎)
    [⋅]-absorberₗ = [⋅]-absorberₗ-by-cancellationᵣ

  instance
    [⋅]-absorberᵣ : Absorberᵣ(_⋅_)(𝟎)
    [⋅]-absorberᵣ = [⋅]-absorberᵣ-by-cancellationᵣ

  -- TODO: Stuff provable in groups
  [−]-binaryOperator : BinaryOperator(_−_)
  BinaryOperator.congruence [−]-binaryOperator {x₁}{y₁}{x₂}{y₂} xy1 xy2 =
    (x₁ − x₂)     🝖[ _≡_ ]-[]
    (x₁ + (− x₂)) 🝖[ _≡_ ]-[ congruence₂(_+_) xy1 (congruence₁(−_) xy2) ]
    (y₁ + (− y₂)) 🝖[ _≡_ ]-[]
    (y₁ − y₂)     🝖-end

  instance
    [−]-involution : Involution(−_)
    [−]-involution = intro One.double-inverse

  [+]-negation-distribution : ∀{x y} → (−(x + y) ≡ (− x) + (− y))
  [+]-negation-distribution = One.inverse-distribution 🝖 commutativity(_+_)

  [−]-negation-distribution : ∀{x y} → (−(x − y) ≡ y − x)
  [−]-negation-distribution = One.inverse-distribution 🝖 congruence₂ₗ(_−_) ⦃ [−]-binaryOperator ⦄ (_) (involution(−_))

  -- TODO: See abs-of-negation for a similiar proof
  postulate zero-when-equal-negation : ∀{x} → (− x ≡ x) → (x ≡ 𝟎)

  instance
    [+]-inversePropₗ : InversePropertyₗ(_+_)(−_)
    [+]-inversePropₗ = One.inverse-propertyₗ-by-groupₗ

  instance
    [+]-inversePropᵣ : InversePropertyᵣ(_+_)(−_)
    [+]-inversePropᵣ = One.inverse-propertyᵣ-by-groupᵣ

  [+][−]-inverseOperᵣ : InverseOperatorᵣ(_+_)(_−_)
  [+][−]-inverseOperᵣ = One.standard-inverse-inverse-operatorᵣ-by-inverse-propᵣ ⦃ inverPropᵣ = [+]-inversePropᵣ ⦄

  [−][+]-inverseOperᵣ : InverseOperatorᵣ(_−_)(_+_)
  [−][+]-inverseOperᵣ = One.standard-inverse-operatorᵣ-by-involuting-inverse-propᵣ ⦃ inverPropᵣ = [+]-inversePropᵣ ⦄

  -- TODO: Defined set subset of natural numbers and integers by using summation ∑. That is: (x ∈ ℕ) = ∃{Obj = ℕ}(n ↦ ∑(0 ‥ n) (const 𝟏))

  [−]-of-𝟎 : ((− 𝟎) ≡ 𝟎)
  [−]-of-𝟎 =
    − 𝟎       🝖-[ symmetry(_≡_) (identityₗ(_+_)(𝟎)) ]
    𝟎 + (− 𝟎) 🝖-[ inverseFunctionᵣ(_+_)(−_) ]
    𝟎         🝖-end

  [−]-is-𝟎 : ∀{x} → ((− x) ≡ 𝟎) ↔ (x ≡ 𝟎)
  [−]-is-𝟎 = [↔]-intro (p ↦ congruence₁(−_) p 🝖 [−]-of-𝟎) (p ↦ symmetry(_≡_) (involution(−_)) 🝖 congruence₁(−_) p 🝖 [−]-of-𝟎)

  [−]-difference-is-𝟎 : ∀{x y} → ((x − y) ≡ 𝟎) ↔ (x ≡ y)
  [−]-difference-is-𝟎 {x}{y} = [↔]-intro l r where
    l =
      (x     ≡ y    ) ⇒-[ congruence₂ᵣ(_−_) ⦃ [−]-binaryOperator ⦄ (x) ]
      (x − x ≡ x − y) ⇒-[ symmetry(_≡_) ]
      (x − y ≡ x − x) ⇒-[ _🝖 inverseFunctionᵣ(_+_)(−_) ]
      (x − y ≡ 𝟎    ) ⇒-end

    r =
      (x − y           ≡ 𝟎    ) ⇒-[]
      (x + (− y)       ≡ 𝟎    ) ⇒-[ congruence₂ₗ(_+_)(y) ]
      ((x + (− y)) + y ≡ 𝟎 + y) ⇒-[ symmetry(_≡_) (associativity(_+_)) 🝖_ ]
      (x + ((− y) + y) ≡ 𝟎 + y) ⇒-[ congruence₂ᵣ(_+_)(x) (symmetry(_≡_) (inverseFunctionₗ(_+_)(−_))) 🝖_ ]
      (x + 𝟎           ≡ 𝟎 + y) ⇒-[ (\p → symmetry(_≡_) (identityᵣ(_+_)(𝟎)) 🝖 p 🝖 identityₗ(_+_)(𝟎)) ]
      (x               ≡ y    ) ⇒-end

  -- Alternative proof using (− 𝟏):
  --   [⋅]ₗ-of-[−] {x}{y} =
  --     ((− x) ⋅ y)       🝖-[ congruence₂ₗ(_⋅_)(y) [⋅]ₗ-of-[−1] ]-sym
  --     (((− 𝟏) ⋅ x) ⋅ y) 🝖-[ associativity(_⋅_) ]
  --     ((− 𝟏) ⋅ (x ⋅ y)) 🝖-[ [⋅]ₗ-of-[−1] ]
  --     (−(x ⋅ y))        🝖-end
  [⋅]ₗ-of-[−] : ∀{x y} → ((− x) ⋅ y ≡ −(x ⋅ y))
  [⋅]ₗ-of-[−] {x}{y} = One.unique-inverseᵣ-by-id $
    (x ⋅ y) + ((− x) ⋅ y) 🝖-[ distributivityᵣ(_⋅_)(_+_) ]-sym
    (x + (− x)) ⋅ y       🝖-[ congruence₂ₗ(_⋅_)(y) (inverseFunctionᵣ(_+_)(−_)) ]
    𝟎 ⋅ y                 🝖-[ absorberₗ(_⋅_)(𝟎) ]
    𝟎                     🝖-end

  -- Alternative proof using (− 𝟏):
  --   [⋅]ᵣ-of-[−] {x}{y} =
  --     (x ⋅ (− y))       🝖-[ congruence₂ᵣ(_⋅_)(x) [⋅]ᵣ-of-[−1] ]-sym
  --     (x ⋅ (y ⋅ (− 𝟏))) 🝖-[ associativity(_⋅_) ]-sym
  --     ((x ⋅ y) ⋅ (− 𝟏)) 🝖-[ [⋅]ᵣ-of-[−1] ]
  --     (−(x ⋅ y))        🝖-end
  [⋅]ᵣ-of-[−] : ∀{x y} → (x ⋅ (− y) ≡ −(x ⋅ y))
  [⋅]ᵣ-of-[−] {x}{y} = One.unique-inverseᵣ-by-id $
    (x ⋅ y) + (x ⋅ (− y)) 🝖-[ distributivityₗ(_⋅_)(_+_) ]-sym
    x ⋅ (y + (− y))       🝖-[ congruence₂ᵣ(_⋅_)(x) (inverseFunctionᵣ(_+_)(−_)) ]
    x ⋅ 𝟎                 🝖-[ absorberᵣ(_⋅_)(𝟎) ]
    𝟎                     🝖-end

  [⋅]-of-[−] : ∀{x y} → ((− x) ⋅ (− y) ≡ x ⋅ y)
  [⋅]-of-[−] {x}{y} =
    ((− x) ⋅ (− y)) 🝖[ _≡_ ]-[ [⋅]ᵣ-of-[−] ]
    −((− x) ⋅ y)    🝖[ _≡_ ]-[ congruence₁(−_) [⋅]ₗ-of-[−] ]
    −(−(x ⋅ y))     🝖[ _≡_ ]-[ involution(−_) ]
    (x ⋅ y)         🝖-end

  [⋅][−]-distributivityₗ : Distributivityₗ(_⋅_)(_−_)
  Distributivityₗ.proof [⋅][−]-distributivityₗ {x}{y}{z} =
    (x ⋅ (y − z))           🝖[ _≡_ ]-[]
    (x ⋅ (y + (− z)))       🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) ]
    ((x ⋅ y) + (x ⋅ (− z))) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x ⋅ y) [⋅]ᵣ-of-[−] ]
    ((x ⋅ y) + (−(x ⋅ z)))  🝖[ _≡_ ]-[]
    ((x ⋅ y) − (x ⋅ z))     🝖-end

  [⋅][−]-distributivityᵣ : Distributivityᵣ(_⋅_)(_−_)
  Distributivityᵣ.proof [⋅][−]-distributivityᵣ {x}{y}{z} =
    ((x − y) ⋅ z)           🝖[ _≡_ ]-[]
    ((x + (− y)) ⋅ z)       🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) ]
    ((x ⋅ z) + ((− y) ⋅ z)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_+_)(x ⋅ z) [⋅]ₗ-of-[−] ]
    ((x ⋅ z) + (−(y ⋅ z)))  🝖[ _≡_ ]-[]
    ((x ⋅ z) − (y ⋅ z))     🝖-end

  module _ ⦃ unity : Unity(_+_)(_⋅_) ⦄ where
    open import Type.Properties.MereProposition
    open import Type.Properties.Singleton
    open import Type.Properties.Singleton.Proofs

    open Unity(unity)

    singleton-when-identities-equal : (𝟎 ≡ 𝟏) ↔ IsUnit(T)
    singleton-when-identities-equal = [↔]-intro l r where
      l : (𝟎 ≡ 𝟏) ← IsUnit(T)
      l p = uniqueness(_) ⦃ inst = unit-is-prop ⦃ proof = p ⦄ ⦄

      r : (𝟎 ≡ 𝟏) → IsUnit(T)
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
