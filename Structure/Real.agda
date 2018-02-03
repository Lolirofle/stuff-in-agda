module Structure.Real {ℓₗ} {ℓₒ} where

import      Lvl
open import Functional
open import Logic.Propositional{ℓₗ Lvl.⊔ ℓₒ}
open import Logic.Predicate{ℓₗ}{ℓₒ}
open import Structure.Operator.Field{ℓₗ}{ℓₒ}
open import Structure.Operator.Monoid{ℓₗ}{ℓₒ}
open import Structure.Operator.Group{ℓₗ}{ℓₒ}
import      Structure.Relator.Ordering
open        Structure.Relator.Ordering{ℓₗ}{ℓₒ}
-- import      Structure.Relator.Ordering.Subsets
-- open        Structure.Relator.Ordering.Subsets.Weak{ℓₗ}{ℓₒ}{ℓₗₒ}
open        Structure.Relator.Ordering.Weak.Properties{ℓₗ}{ℓₒ}
open import Sets.Subset{ℓₗ}{ℓₒ}
open import Type{ℓₒ}
open import Type using () renaming (Type to TypeN)

-- Theory defining the axioms of ℝ
record RealTheory {R : Type} (_+_ _⋅_ : R → R → R) (_≤_ _≡_ : R → R → Stmt) : TypeN{Lvl.𝐒(ℓₗ Lvl.⊔ ℓₒ)} where
  field
    [+][⋅]-field : Field(_+_)(_⋅_)

  𝟎 : R
  𝟎 = Monoid.id(Group.monoid(Field.[+]-group([+][⋅]-field)))

  𝟏 : R
  𝟏 = Monoid.id(MultGroup.monoid(Field.[⋅]-group([+][⋅]-field)))

  field
    [≤]-totalOrder    : Weak.TotalOrder(_≤_)(_≡_)
    [+][≤]-preserve   : ∀{x y} → (x ≤ y) → ∀{z} → ((x + z) ≤ (y + z))
    [⋅][≤]-preserve   : ∀{x y} → (𝟎 ≤ x) → (𝟎 ≤ y) → (𝟎 ≤ (x ⋅ y))
    -- dedekind-complete : ∀{P : R → Stmt} → Subset(P) → ∃(u ↦ UpperBound(_≤_)(P)(u)) → Supremum(_≤_)(P)
-- TODO: Use Bolzano–Weierstrass theorem or Monotone convergence theorem as an axiom instead?
-- CauchySequence(f) = ∀{a : ℕ → ℕ}{k m n} → (m > a(k)) → (n > a(k)) → (− ε < f(m) − f(n))∧(f(m) − f(n) < ε)
