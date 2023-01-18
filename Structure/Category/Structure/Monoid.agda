open import Structure.Setoid
open import Structure.Category
open import Type

module Structure.Category.Structure.Monoid
  {ℓₒ ℓₘ ℓₑ}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(Morphism x y) ⦄
  (cat : Category(Morphism))
  where

open import Logic.Predicate
open import Structure.Categorical.Properties
open import Structure.Operator.Monoid
open import Structure.Operator.Properties

open Category(cat)

-- A monoid constructed from a category for a specific object.
monoid : ∀{x} → Monoid(_∘_ {x = x})
Monoid.binaryOperator     monoid = binaryOperator
Monoid.associativity      monoid = intro(Morphism.associativity(_∘_))
Monoid.identity-existence monoid =
  [∃]-intro id ⦃ intro
    ⦃ left  = intro(Morphism.identityₗ(_∘_)(id)) ⦄
    ⦃ right = intro(Morphism.identityᵣ(_∘_)(id)) ⦄
  ⦄
