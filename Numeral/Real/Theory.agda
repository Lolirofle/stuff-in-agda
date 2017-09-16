module Numeral.Real.Theory {ℓ₁} {ℓ₂} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Structure.Operator.Field{ℓ₁}{ℓ₂}
open import Structure.Operator.Group{ℓ₁}{ℓ₂}
import      Structure.Relator.Ordering
open        Structure.Relator.Ordering{ℓ₁}{ℓ₂}
open        Structure.Relator.Ordering.Weak.Properties{ℓ₁}{ℓ₂}
open import Sets.Subset{ℓ₁}{ℓ₂}
open import Type{ℓ₂}
open import Type using () renaming (Type to TypeN)

-- Theory defining the axioms of ℝ
record RealTheory {R : Type} (_+_ _⋅_ : R → R → R) (_≤_ _≡_ : R → R → Stmt) : TypeN{Lvl.𝐒(ℓ₁ Lvl.⊔ ℓ₂)} where
  field
    [+][⋅]-field      : Field(_+_)(_⋅_)

  𝟎 : R
  𝟎 = Group.id(Field.[+]-group([+][⋅]-field))

  𝟏 : R
  𝟏 = Group.id(Field.[⋅]-group([+][⋅]-field))

  field
    [≤]-totalOrder    : Weak.TotalOrder(_≤_)(_≡_)
    [+][≤]-preserve   : ∀{x y} → (x ≤ y) → ∀{z} → ((x + z) ≤ (y + z))
    [⋅][≤]-preserve   : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))
    dedekind-complete : ∀{P : R → Stmt} → Subset(P) → ∃(u ↦ UpperBound(_≤_)(P)(u)) → Supremum(_≤_)(P)
