module Structure.Operator.Ring.Proofs where

import      Data.Tuple as Tuple
open import Functional
open import Logic.IntroInstances
open import Logic.Predicate
open import Logic.Propositional
import      Lvl
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Operator.Properties
open import Structure.Operator.Ring
open import Structure.Operator
open import Structure.Operator.InverseOperatorFromFunction.Proofs
open import Structure.Operator.Proofs
open import Structure.Operator.Proofs.Util
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Implication
open import Syntax.Transitivity
open import Type.Properties.MereProposition
open import Type.Properties.Singleton
open import Type.Properties.Singleton.Proofs
open import Type

private variable ℓ ℓₑ ℓₙ₀ : Lvl.Level
private variable T : Type{ℓ}
private variable _+_ _⋅_ : T → T → T

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ rg : Rg{T = T}(_+_)(_⋅_){ℓₙ₀} ⦄ where
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

  module _ ⦃ unity : Unity(_+_)(_⋅_) ⦄ where
    open Unity(unity)

    -- TODO: The following is contained in the proof below: [2⋅][+]-preserving : (x+y)² = x²+y²

    [+]-commutativity-by-cancellation-unity : ⦃ cancₗ : Cancellationₗ(_+_) ⦄ → ⦃ cancᵣ : Cancellationᵣ(_+_) ⦄ → Commutativity(_+_)
    Commutativity.proof [+]-commutativity-by-cancellation-unity {x}{y} = cancellationᵣ(_+_) {y} $ cancellationₗ(_+_) {x} $
      x + ((x + y) + y)                         🝖[ _≡_ ]-[ One.associate4-231-222 ]
      (x + x) + (y + y)                         🝖[ _≡_ ]-[ congruence₂(_+_) (congruence₂(_+_) (identityₗ(_⋅_)(𝟏)) (identityₗ(_⋅_)(𝟏))) (congruence₂(_+_) (identityₗ(_⋅_)(𝟏)) (identityₗ(_⋅_)(𝟏))) ]-sym
      ((𝟏 ⋅ x) + (𝟏 ⋅ x)) + ((𝟏 ⋅ y) + (𝟏 ⋅ y)) 🝖[ _≡_ ]-[ congruence₂(_+_) (distributivityᵣ(_⋅_)(_+_)) (distributivityᵣ(_⋅_)(_+_)) ]-sym
      ((𝟏 + 𝟏) ⋅ x) + ((𝟏 + 𝟏) ⋅ y)             🝖[ _≡_ ]-[ distributivityₗ(_⋅_)(_+_) ]-sym
      (𝟏 + 𝟏) ⋅ (x + y)                         🝖[ _≡_ ]-[ distributivityᵣ(_⋅_)(_+_) ]
      (𝟏 ⋅ (x + y)) + (𝟏 ⋅ (x + y))             🝖[ _≡_ ]-[ congruence₂(_+_) (identityₗ(_⋅_)(𝟏)) (identityₗ(_⋅_)(𝟏)) ]
      (x + y) + (x + y)                         🝖[ _≡_ ]-[ One.associate4-231-222 ]-sym
      x + ((y + x) + y)                         🝖-end

    module _ ⦃ ident : DistinctIdentities ⦄ ⦃ canc : Cancellationᵣ(_+_) ⦄ where
      [𝟎]-zero-divisorₗ : ZeroDivisorₗ(𝟎)
      [𝟎]-zero-divisorₗ = [∃]-intro 𝟏 ⦃ [∧]-intro ident (absorberₗ(_⋅_)(𝟎) ⦃ [⋅]-absorberₗ-by-cancellationᵣ ⦄) ⦄

      [𝟎]-zero-divisorᵣ : ZeroDivisorᵣ(𝟎)
      [𝟎]-zero-divisorᵣ = [∃]-intro 𝟏 ⦃ [∧]-intro ident (absorberᵣ(_⋅_)(𝟎) ⦃ [⋅]-absorberᵣ-by-cancellationᵣ ⦄) ⦄

      [𝟎]-zero-divisor : ZeroDivisor(𝟎)
      [𝟎]-zero-divisor = [∃]-intro 𝟏 ⦃ [∧]-intro ident ([∧]-intro (absorberₗ(_⋅_)(𝟎) ⦃ [⋅]-absorberₗ-by-cancellationᵣ ⦄) (absorberᵣ(_⋅_)(𝟎) ⦃ [⋅]-absorberᵣ-by-cancellationᵣ ⦄)) ⦄

    module _ ⦃ division : Division(_+_)(_⋅_) ⦄ where
      open Division(division)

      [⋅]-cancellationₗ : ∀{x y z} ⦃ nonzero : NonZero(x) ⦄ → (x ⋅ y ≡ x ⋅ z) → (y ≡ z)
      [⋅]-cancellationₗ {x}{y}{z} xyxz =
        y               🝖[ _≡_ ]-[ identityₗ(_⋅_)(𝟏) ]-sym
        𝟏 ⋅ y           🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(y) [⋅]-inverseᵣ ]-sym
        ((⅟ x) ⋅ x) ⋅ y 🝖[ _≡_ ]-[ associativity(_⋅_) ]
        (⅟ x) ⋅ (x ⋅ y) 🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(⅟ x) xyxz ]
        (⅟ x) ⋅ (x ⋅ z) 🝖[ _≡_ ]-[ associativity(_⋅_) ]-sym
        ((⅟ x) ⋅ x) ⋅ z 🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(z) [⋅]-inverseᵣ ]
        𝟏 ⋅ z           🝖[ _≡_ ]-[ identityₗ(_⋅_)(𝟏) ]
        z               🝖-end

      [⋅]-cancellationᵣ : ∀{x y z} ⦃ nonzero : NonZero(z) ⦄ → (x ⋅ z ≡ y ⋅ z) → (x ≡ y)
      [⋅]-cancellationᵣ {x}{y}{z} xzyz =
        x               🝖[ _≡_ ]-[ identityᵣ(_⋅_)(𝟏) ]-sym
        x ⋅ 𝟏           🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(x) [⋅]-inverseₗ ]-sym
        x ⋅ (z ⋅ (⅟ z)) 🝖[ _≡_ ]-[ associativity(_⋅_) ]-sym
        (x ⋅ z) ⋅ (⅟ z) 🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(⅟ z) xzyz ]
        (y ⋅ z) ⋅ (⅟ z) 🝖[ _≡_ ]-[ associativity(_⋅_) ]
        y ⋅ (z ⋅ (⅟ z)) 🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(y) [⋅]-inverseₗ ]
        y ⋅ 𝟏           🝖[ _≡_ ]-[ identityᵣ(_⋅_)(𝟏) ]
        y               🝖-end

      [⋅][/]-inverseOperᵣ : ∀{x y} ⦃ nonzero : NonZero(y) ⦄ → ((x ⋅ y) / y ≡ x)
      [⋅][/]-inverseOperᵣ {x}{y} =
        ((x ⋅ y) / y)     🝖[ _≡_ ]-[]
        ((x ⋅ y) ⋅ (⅟ y)) 🝖[ _≡_ ]-[ associativity(_⋅_) ]
        x ⋅ (y ⋅ (⅟ y))   🝖[ _≡_ ]-[ congruence₂ᵣ(_⋅_)(x) [⋅]-inverseₗ ]
        x ⋅ 𝟏             🝖[ _≡_ ]-[ identityᵣ(_⋅_)(𝟏) ]
        x                 🝖-end

      [swap⋅][/]-inverseOperᵣ : ⦃ comm : Commutativity(_⋅_) ⦄ → ∀{x y} ⦃ nonzero : NonZero(x) ⦄ → ((x ⋅ y) / x ≡ y)
      [swap⋅][/]-inverseOperᵣ {x}{y} =
        ((x ⋅ y) / x)     🝖[ _≡_ ]-[ congruence₂ₗ(_⋅_)(⅟ x) (commutativity(_⋅_)) ]
        ((y ⋅ x) / x)     🝖[ _≡_ ]-[ [⋅][/]-inverseOperᵣ ]
        y                 🝖-end

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ rng : Rng{T = T}(_+_)(_⋅_){ℓₙ₀} ⦄ where
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

  [−]-binaryOperator : BinaryOperator(_−_)
  [−]-binaryOperator = invOpᵣ-binaryOperator

  instance
    [−]-involution : Involution(−_)
    [−]-involution = intro One.double-inverse

  [+]-negation-distribution-commuted : ∀{x y} → (−(x + y) ≡ (− y) − x)
  [+]-negation-distribution-commuted = One.inverse-distribution

  [+]-negation-distribution : ⦃ comm : Commutativity(_+_) ⦄ → ∀{x y} → (−(x + y) ≡ (− x) + (− y))
  [+]-negation-distribution = [+]-negation-distribution-commuted 🝖 commutativity(_+_)

  [−]-negation-distribution : ∀{x y} → (−(x − y) ≡ y − x)
  [−]-negation-distribution = One.inverse-distribution 🝖 congruence₂ₗ(_−_) ⦃ [−]-binaryOperator ⦄ (_) (involution(−_))

  -- TODO: Use abs-of-negation when ordered. Otherwise, assume multiplicative cancellation first. −x=x is x+x=0 which means x is its own inverse
  -- zero-when-equal-negation : ∀{x} → (− x ≡ x) → (x ≡ 𝟎)

  instance
    [+]-inversePropₗ : InversePropertyₗ(_+_)(−_)
    [+]-inversePropₗ = One.inverse-propertyₗ-by-groupₗ

  instance
    [+]-inversePropᵣ : InversePropertyᵣ(_+_)(−_)
    [+]-inversePropᵣ = One.inverse-propertyᵣ-by-groupᵣ

  [+][−]-inverseOperᵣ : InverseOperatorᵣ(_+_)(_−_)
  [+][−]-inverseOperᵣ = inverse-inverse-operatorᵣ-by-inverse-propᵣ ⦃ inverPropᵣ = [+]-inversePropᵣ ⦄

  [−][+]-inverseOperᵣ : InverseOperatorᵣ(_−_)(_+_)
  [−][+]-inverseOperᵣ = inverse-operatorᵣ-by-involuting-inverse-propᵣ ⦃ inverPropᵣ = [+]-inversePropᵣ ⦄

  [−][swap+]-inverseOperᵣ : ⦃ comm : Commutativity(_+_) ⦄ → InverseOperatorᵣ(_−_)(swap(_+_))
  [−][swap+]-inverseOperᵣ = intro (commutativity(_+_) 🝖 inverseOperᵣ(_−_)(_+_) ⦃ [−][+]-inverseOperᵣ ⦄)

  [swap+][−]-inverseOperᵣ : ⦃ comm : Commutativity(_+_) ⦄ → InverseOperatorᵣ(swap(_+_))(_−_)
  [swap+][−]-inverseOperᵣ = intro (congruence₂ₗ(_+_)(− _) (commutativity(_+_)) 🝖 inverseOperᵣ(_+_)(_−_) ⦃ [+][−]-inverseOperᵣ ⦄)

  [−]-of-𝟎 : ((− 𝟎) ≡ 𝟎)
  [−]-of-𝟎 = One.inv-of-id

  [−]-is-𝟎 : ∀{x} → ((− x) ≡ 𝟎) ↔ (x ≡ 𝟎)
  [−]-is-𝟎 = One.inv-is-id

  [−]-difference-is-𝟎 : ∀{x y} → ((x − y) ≡ 𝟎) ↔ (x ≡ y)
  [−]-difference-is-𝟎 = One.equality-zero

  -- Alternative proof using (− 𝟏):
  --   [⋅]ₗ-of-[−] {x}{y} =
  --     ((− x) ⋅ y)       🝖-[ congruence₂ₗ(_⋅_)(y) [⋅]ₗ-of-[−1] ]-sym
  --     (((− 𝟏) ⋅ x) ⋅ y) 🝖-[ associativity(_⋅_) ]
  --     ((− 𝟏) ⋅ (x ⋅ y)) 🝖-[ [⋅]ₗ-of-[−1] ]
  --     (−(x ⋅ y))        🝖-end
  [⋅]ₗ-of-[−] : ∀{x y} → ((− x) ⋅ y ≡ −(x ⋅ y))
  [⋅]ₗ-of-[−] {x}{y} = OneTypeTwoOp.distributeₗ-inv

  -- Alternative proof using (− 𝟏):
  --   [⋅]ᵣ-of-[−] {x}{y} =
  --     (x ⋅ (− y))       🝖-[ congruence₂ᵣ(_⋅_)(x) [⋅]ᵣ-of-[−1] ]-sym
  --     (x ⋅ (y ⋅ (− 𝟏))) 🝖-[ associativity(_⋅_) ]-sym
  --     ((x ⋅ y) ⋅ (− 𝟏)) 🝖-[ [⋅]ᵣ-of-[−1] ]
  --     (−(x ⋅ y))        🝖-end
  [⋅]ᵣ-of-[−] : ∀{x y} → (x ⋅ (− y) ≡ −(x ⋅ y))
  [⋅]ᵣ-of-[−] {x}{y} = OneTypeTwoOp.distributeᵣ-inv

  [⋅]-of-[−] : ∀{x y} → ((− x) ⋅ (− y) ≡ x ⋅ y)
  [⋅]-of-[−] {x}{y} = OneTypeTwoOp.op-on-inv-cancel

  [⋅][−]-distributivityₗ : Distributivityₗ(_⋅_)(_−_)
  [⋅][−]-distributivityₗ = invᵣ-distributivityₗ

  [⋅][−]-distributivityᵣ : Distributivityᵣ(_⋅_)(_−_)
  [⋅][−]-distributivityᵣ = invᵣ-distributivityᵣ

  module _ ⦃ unity : Unity(_+_)(_⋅_) ⦄ where
    open import Type.Properties.MereProposition
    open import Type.Properties.Singleton
    open import Type.Properties.Singleton.Proofs

    open Unity(unity)

    [+]-commutativity : Commutativity(_+_)
    [+]-commutativity = [+]-commutativity-by-cancellation-unity

    -- The ring is a trivial ring when its identities are equal.
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

    [⋅]-cancellationₗ-on-regular-divisor : ∀{x y z} ⦃ div : RegularDivisorₗ(x) ⦄ → (x ⋅ y ≡ x ⋅ z) → (y ≡ z)
    [⋅]-cancellationₗ-on-regular-divisor {x}{y}{z} ⦃ intro div ⦄ =
      (x ⋅ y             ≡ x ⋅ z) ⇒-[ [↔]-to-[←] [−]-difference-is-𝟎 ]
      ((x ⋅ y) − (x ⋅ z) ≡ 𝟎    ) ⇒-[ distributivityₗ(_⋅_)(_−_) ⦃ [⋅][−]-distributivityₗ ⦄ 🝖_ ]
      (x ⋅ (y − z)       ≡ 𝟎    ) ⇒-[ div ]
      (y − z             ≡ 𝟎    ) ⇒-[ [↔]-to-[→] [−]-difference-is-𝟎 ]
      (y                 ≡ z    ) ⇒-end

    [⋅]-cancellationᵣ-on-regular-divisor : ∀{x y z} ⦃ div : RegularDivisorᵣ(z) ⦄ → (x ⋅ z ≡ y ⋅ z) → (x ≡ y)
    [⋅]-cancellationᵣ-on-regular-divisor {x}{y}{z} ⦃ intro div ⦄ =
      (x ⋅ z             ≡ y ⋅ z) ⇒-[ [↔]-to-[←] [−]-difference-is-𝟎 ]
      ((x ⋅ z) − (y ⋅ z) ≡ 𝟎    ) ⇒-[ distributivityᵣ(_⋅_)(_−_) ⦃ [⋅][−]-distributivityᵣ ⦄ 🝖_ ]
      ((x − y) ⋅ z       ≡ 𝟎    ) ⇒-[ div ]
      (x − y             ≡ 𝟎    ) ⇒-[ [↔]-to-[→] [−]-difference-is-𝟎 ]
      (x                 ≡ y    ) ⇒-end

    regular-zero-divisorₗ-not : ∀{x} → RegularDivisorₗ(x) → ZeroDivisorₗ(x) → ⊥
    regular-zero-divisorₗ-not (intro div) ([∃]-intro y ⦃ [∧]-intro ny0 xy0 ⦄) = [↔]-to-[→] nonZero ny0(div xy0)

    regular-zero-divisorᵣ-not : ∀{x} → RegularDivisorᵣ(x) → ZeroDivisorᵣ(x) → ⊥
    regular-zero-divisorᵣ-not (intro div) ([∃]-intro y ⦃ [∧]-intro ny0 yx0 ⦄) = [↔]-to-[→] nonZero ny0(div yx0)

    module _ ⦃ ident : DistinctIdentities ⦄ where
      regular-divisorₗ-non-zero-sub : ∀{x} → RegularDivisorₗ(x) → NonZero(x)
      regular-divisorₗ-non-zero-sub (intro div) = [↔]-to-[←] nonZero \x0 → [↔]-to-[→] nonZero ident(div(congruence₂ₗ(_⋅_)(𝟏) x0 🝖 absorberₗ(_⋅_)(𝟎)))

      regular-divisorᵣ-non-zero-sub : ∀{x} → RegularDivisorᵣ(x) → NonZero(x)
      regular-divisorᵣ-non-zero-sub (intro div) = [↔]-to-[←] nonZero \x0 → [↔]-to-[→] nonZero ident(div(congruence₂ᵣ(_⋅_)(𝟏) x0 🝖 absorberᵣ(_⋅_)(𝟎)))
