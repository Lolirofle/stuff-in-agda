module Structure.Real {ℓₗ} {ℓₒ} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Logic.Predicate{ℓₗ}{ℓₒ}
open import Sets.PredicateSet.Filter{ℓₗ}{ℓₒ}
open import Sets.Setoid{ℓₗ}
open import Structure.Operator.Field{ℓₗ}{ℓₒ}
open import Structure.Operator.Monoid{ℓₗ}{ℓₒ}
open import Structure.Operator.Group{ℓₗ}{ℓₒ}
import      Structure.Relator.Ordering
open        Structure.Relator.Ordering{ℓₗ}{ℓₒ}
open        Structure.Relator.Ordering.Weak.Properties{ℓₗ}{ℓₒ}
open import Type{ℓₒ}
open import Type using () renaming (Type to TypeN)

-- Theory defining the axioms of ℝ
record RealTheory {R : Type} (_+_ _⋅_ : R → R → R) (_≤_ : R → R → Stmt) ⦃ _ : Equiv(R) ⦄ : TypeN{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  field
    instance ⦃ [+][⋅]-field ⦄ : Field(_+_)(_⋅_)

  𝟎 : R
  𝟎 = Monoid.id(Group.monoid(Field.[+]-group([+][⋅]-field)))

  𝟏 : R
  𝟏 = Monoid.id(MultGroup.monoid(Field.[⋅]-group([+][⋅]-field)))

  𝟏 : R
  𝟏 = Monoid.id(MultGroup.monoid(Field.[⋅]-group([+][⋅]-field)))

  field
    [≤]-totalOrder     : Weak.TotalOrder(_≤_)(_≡_)
    [+][≤]-preserve    : ∀{x y} → (x ≤ y) → ∀{z} → ((x + z) ≤ (y + z))
    [⋅][≤]-preserve    : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))
    supremum-existence : ∀{P : R → Stmt} → ∃(P) → ∃(UpperBoundOf(_≤_)(P)) → ∃(SupremumOf(_≤_)(P))
