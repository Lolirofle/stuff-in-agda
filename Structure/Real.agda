module Structure.Real where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid
open import Structure.Operator.Field
open import Structure.Operator.Monoid
open import Structure.Operator.Group
open import Structure.Relator.Ordering
open        Structure.Relator.Ordering.Weak.Properties
open import Type

-- Theory defining the axioms of ℝ
record RealTheory {ℓ₁ ℓ₂} {R : Type{ℓ₁}} ⦃ _ : Equiv(R) ⦄ (_+_ _⋅_ : R → R → R) (_≤_ : R → R → Stmt{ℓ₂}) : Type{ℓ₁ Lvl.⊔ Lvl.𝐒(ℓ₂)} where
  field
    instance ⦃ [+][⋅]-field ⦄ : Field(_+_)(_⋅_)

  𝟎 : R
  𝟎 = Monoid.id (Field.[+]-monoid([+][⋅]-field))

  𝟏 : R
  𝟏 = Monoid.id (Field.[⋅]-monoid([+][⋅]-field))

  field
    instance ⦃ [≤]-totalOrder ⦄ : Weak.TotalOrder(_≤_)(_≡_)
    [+][≤]-preserve    : ∀{x y} → (x ≤ y) → ∀{z} → ((x + z) ≤ (y + z))
    [⋅][≤]-preserve    : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))
    supremum-existence : ∀{P : R → Stmt{ℓ₂}} → ∃(P) → ∃(UpperBoundOf(_≤_)(P)) → ∃(SupremumOf(_≤_)(P))

  −_ : R → R
  −_ = Group.inv (Field.[+]-group([+][⋅]-field))

  _−_ : R → R → R
  x − y = x + (− y)

  postulate ⅟_ : (x : R) → ⦃ _ : (x ≢ 𝟎) ⦄ → R -- TODO

  _/_ : R → (y : R) → ⦃ _ : (y ≢ 𝟎) ⦄ → R
  _/_ x y ⦃ proof ⦄ = x ⋅ (⅟_ y ⦃ proof ⦄)
