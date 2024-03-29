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
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Ordering
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Group
open import Structure.Operator.Proofs
open import Structure.Operator.Properties
open import Structure.Operator.Ring.Proofs
open import Structure.Operator.Ring
open import Structure.Operator
open import Structure.Relator
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Weak.Properties
open import Structure.Relator.Properties
open import Structure.Relator.Proofs
open import Syntax.Implication
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₗ ℓₑ ℓₙ₀ : Lvl.Level
private variable F : Type{ℓ}
private variable _+_ _⋅_ : F → F → F
private variable _≤_ : F → F → Stmt{ℓₗ}

-- TODO: Generalize so that this does not neccessarily need a rng. See linearly ordered groups and partially ordered groups. See also ordered semigroups and monoids where the property is called "compatible".
record Ordered ⦃ equiv : Equiv{ℓₑ}(F) ⦄ (_+_ _⋅_ : F → F → F) ⦃ rng : Rng(_+_)(_⋅_){ℓₙ₀} ⦄ ⦃ comm : Commutativity(_+_) ⦄ (_≤_ : F → F → Stmt{ℓₗ}) : Type{Lvl.of(F) Lvl.⊔ ℓₗ Lvl.⊔ ℓₑ} where
  open From-[≤](_≤_) public
  open Rng(rng)

  field
    ⦃ [≤]-totalOrder ⦄        : Weak.TotalOrder(_≤_)
    [≤][+]ₗ-preserve          : ∀{x y z} → (x ≤ y) → ((x + z) ≤ (y + z))
    [≤][⋅]-preserve-positive  : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))

  open Weak.TotalOrder([≤]-totalOrder)
    renaming(
      relator      to [≤]-relator ;
      reflexivity  to [≤]-reflexivity ;
      antisymmetry to [≤]-antisymmetry ;
      transitivity to [≤]-transitivity ;
      totality     to [≤]-totality
    ) public
  open OrderingProofs.From-[≤].ByTotalOrder (_≤_) ⦃ equiv ⦄ ⦃ [≤]-totalOrder ⦄ public

  record NonNegative (x : F) : Stmt{ℓₗ} where
    constructor intro
    field proof : (x ≥ 𝟎)

  record Positive (x : F) : Stmt{ℓₗ} where
    constructor intro
    field proof : (x > 𝟎)

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

  [≤]-flip-positive : ∀{x} → (𝟎 ≤ x) ↔ ((− x) ≤ 𝟎)
  [≤]-flip-positive {x} = [↔]-intro l r where
    l = \p →
      𝟎         🝖[ _≡_ ]-[ symmetry(_≡_) (inverseFunctionᵣ(_+_)(−_)) ]-sub
      x + (− x) 🝖[ _≤_ ]-[ [≤][+]ᵣ-preserve p ]
      x + 𝟎     🝖[ _≡_ ]-[ identityᵣ(_+_)(𝟎) ]-sub
      x         🝖-end
    r = \p →
      − x       🝖[ _≡_ ]-[ symmetry(_≡_) (identityₗ(_+_)(𝟎)) ]-sub
      𝟎 + (− x) 🝖[ _≤_ ]-[ [≤][+]ₗ-preserve p ]
      x + (− x) 🝖[ _≡_ ]-[ inverseFunctionᵣ(_+_)(−_) ]-sub
      𝟎         🝖-end

  [≤]-non-negative-difference : ∀{x y} → (𝟎 ≤ (y − x)) → (x ≤ y)
  [≤]-non-negative-difference {x}{y} 𝟎yx =
    x               🝖[ _≡_ ]-[ symmetry(_≡_) (identityₗ(_+_)(𝟎)) ]-sub
    𝟎 + x           🝖[ _≤_ ]-[ [≤][+]ₗ-preserve 𝟎yx ]
    (y − x) + x     🝖[ _≤_ ]-[]
    (y + (− x)) + x 🝖[ _≡_ ]-[ associativity(_+_) ]-sub
    y + ((− x) + x) 🝖[ _≡_ ]-[ congruence₂-₂(_+_)(_) (inverseFunctionₗ(_+_)(−_)) ]-sub
    y + 𝟎           🝖[ _≡_ ]-[ identityᵣ(_+_)(𝟎) ]-sub
    y               🝖-end

  postulate [<]-positive-difference : ∀{x y} → (𝟎 < (y − x)) ↔ (x < y)

  [≤]-non-positive-difference : ∀{x y} → ((x − y) ≤ 𝟎) → (x ≤ y)
  [≤]-non-positive-difference {x}{y} xy𝟎 =
    x               🝖[ _≡_ ]-[ symmetry(_≡_) (identityᵣ(_+_)(𝟎)) ]-sub
    x + 𝟎           🝖[ _≡_ ]-[ symmetry(_≡_) (congruence₂-₂(_+_)(_) (inverseFunctionₗ(_+_)(−_))) ]-sub
    x + ((− y) + y) 🝖[ _≡_ ]-[ symmetry(_≡_) (associativity(_+_)) ]-sub
    (x + (− y)) + y 🝖[ _≤_ ]-[]
    (x − y) + y     🝖[ _≤_ ]-[ [≤][+]ₗ-preserve xy𝟎 ]
    𝟎 + y           🝖[ _≡_ ]-[ identityₗ(_+_)(𝟎) ]-sub
    y               🝖-end

  [≤]-with-[−] : ∀{x y} → (x ≤ y) → ((− y) ≤ (− x))
  [≤]-with-[−] {x}{y} xy = [≤]-non-positive-difference proof3 where
    proof3 : (((− y) − (− x)) ≤ 𝟎)
    proof3 =
      (− y) − (− x) 🝖[ _≡_ ]-[ congruence₂-₂(_+_)(_) (involution(−_)) ]-sub
      (− y) + x     🝖[ _≡_ ]-[ commutativity(_+_) ]-sub
      x − y         🝖[ _≤_ ]-[ [≤][+]ₗ-preserve xy ]
      y − y         🝖[ _≡_ ]-[ inverseFunctionᵣ(_+_)(−_) ]-sub
      𝟎             🝖-end

  [≤]-flip-negative : ∀{x} → (x ≤ 𝟎) ↔ (𝟎 ≤ (− x))
  [≤]-flip-negative {x} = [↔]-intro l r where
    r = \p →
      𝟎   🝖[ _≡_ ]-[ symmetry(_≡_) [−]-of-𝟎 ]-sub
      − 𝟎 🝖[ _≤_ ]-[ [≤]-with-[−] {x}{𝟎} p ]
      − x 🝖-end

    l = \p →
      x      🝖[ _≡_ ]-[ symmetry(_≡_) (involution(−_)) ]-sub
      −(− x) 🝖[ _≤_ ]-[ [≤]-with-[−] p ]
      − 𝟎    🝖[ _≡_ ]-[ [−]-of-𝟎 ]-sub
      𝟎      🝖-end

  [≤][−]ₗ-preserve : ∀{x y z} → (x ≤ y) → ((x − z) ≤ (y − z))
  [≤][−]ₗ-preserve = [≤][+]ₗ-preserve

  [≤][−]ᵣ-preserve : ∀{x y z} → (z ≤ y) → ((x − y) ≤ (x − z))
  [≤][−]ᵣ-preserve = [≤][+]ᵣ-preserve ∘ [≤]-with-[−]

  [≤][+]-withoutᵣ : ∀{x₁ x₂ y} → ((x₁ + y) ≤ (x₂ + y)) → (x₁ ≤ x₂)
  [≤][+]-withoutᵣ {x₁}{x₂}{y} p =
    x₁           🝖[ _≡_ ]-[ symmetry(_≡_) (inverseOperᵣ(_+_)(_−_)) ]-sub
    (x₁ + y) − y 🝖[ _≤_ ]-[ [≤][−]ₗ-preserve p ]
    (x₂ + y) − y 🝖[ _≡_ ]-[ inverseOperᵣ(_+_)(_−_) ]-sub
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

  [<][+]-preserve-subₗ : ∀{x₁ x₂ y₁ y₂} → (x₁ ≤ x₂) → (y₁ < y₂) → ((x₁ + y₁) < (x₂ + y₂))
  [<][+]-preserve-subₗ {x₁}{x₂}{y₁}{y₂} px py =
    x₁ + y₁ 🝖[ _≤_ ]-[ [≤][+]ₗ-preserve px ]-sub
    x₂ + y₁ 🝖-semiend
    x₂ + y₂ 🝖[ _<_ ]-end-from-[ [<][+]-preserveᵣ py ]

  [<][+]-preserve-subᵣ : ∀{x₁ x₂ y₁ y₂} → (x₁ < x₂) → (y₁ ≤ y₂) → ((x₁ + y₁) < (x₂ + y₂))
  [<][+]-preserve-subᵣ {x₁}{x₂}{y₁}{y₂} px py =
    x₁ + y₁ 🝖[ _≤_ ]-[ [≤][+]ᵣ-preserve py ]-sub
    x₁ + y₂ 🝖-semiend
    x₂ + y₂ 🝖[ _<_ ]-end-from-[ [<][+]-preserveₗ px ]

  [≤][⋅]-antipreserve-negative  : ∀{x y} → (𝟎 ≥ x) → (𝟎 ≥ y) → (𝟎 ≤ (x ⋅ y))
  [≤][⋅]-antipreserve-negative {x}{y} px py =
    • (
      px ⇒
      (x ≤ 𝟎)     ⇒-[ [↔]-to-[→] [≤]-flip-negative ]
      (𝟎 ≤ (− x)) ⇒-end
    )
    • (
      py ⇒
      (y ≤ 𝟎)     ⇒-[ [↔]-to-[→] [≤]-flip-negative ]
      (𝟎 ≤ (− y)) ⇒-end
    )
    ⇒₂-[ [≤][⋅]-preserve-positive ]
    (𝟎 ≤ ((− x) ⋅ (− y))) ⇒-[ Functional.swap(subtransitivityᵣ(_≤_)(_≡_)) [⋅]-of-[−] ]
    (𝟎 ≤ (x ⋅ y))         ⇒-end

  [≤]-positive-by-self-negativity : ∀{x} → (𝟎 ≤ x) ↔ ((− x) ≤ x)
  [≤]-positive-by-self-negativity {x} = [↔]-intro
    (p ↦ [∨]-elim id (neg ↦ [↔]-to-[→] [≤]-flip-negative neg 🝖 p) (converseTotal(_≤_) {𝟎}{x}))
    (p ↦ [↔]-to-[→] [≤]-flip-positive p 🝖 p)

  module _ ⦃ unity : Unity(_+_)(_⋅_) ⦄ where
    open Unity(unity)

    [≤]-identities : 𝟎 ≤ 𝟏
    [≤]-identities = [∨]-elim id (io ↦ subtransitivityᵣ(_≤_)(_≡_) ([≤][⋅]-antipreserve-negative io io) (identityᵣ(_⋅_)(𝟏))) (converseTotal(_≤_) {𝟎}{𝟏})

    module _ ⦃ distinct-identities : NonZero(𝟏) ⦄ where
      [<]-identities : 𝟎 < 𝟏
      [<]-identities = [≤][≢]-to-[<] [≤]-identities ([↔]-to-[→] nonZero distinct-identities ∘ symmetry(_≡_))

open import Functional.Instance
open import Structure.Relator.Ordering.Proofs

-- Theory defining the axioms of an ordered field (a field with a weak total order).
record OrderedField ⦃ equiv : Equiv{ℓₑ}(F) ⦄ (_+_ _⋅_ : F → F → F) (_≤_ : F → F → Stmt{ℓₗ}) : Type{Lvl.of(F) Lvl.⊔ ℓₗ Lvl.⊔ ℓₑ Lvl.⊔ Lvl.𝐒(ℓₙ₀)} where
  field ⦃ [+][⋅]-field ⦄ : Field(_+_)(_⋅_){ℓₙ₀}
  open Field([+][⋅]-field) public
  field ⦃ ordered ⦄ : Ordered(_+_)(_⋅_)(_≤_)
  open Ordered(ordered) public
