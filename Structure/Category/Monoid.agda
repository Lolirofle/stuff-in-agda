open import Structure.Setoid
open import Structure.Category
open import Type

module Structure.Category.Monoid
  {ℓₒ ℓₘ}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄
  (cat : Category(Morphism))
  where

open import Logic.Predicate
open import Structure.Categorical.Properties
open import Structure.Operator.Monoid
open import Structure.Operator.Properties

open Category(cat)

-- A monoid constructed from a category for a specific object.
monoid : ∀{x} → Monoid(_∘_ {x = x})
Monoid.binary-operator monoid = binaryOperator
Associativity.proof (Monoid.associativity monoid) = Morphism.associativity(_∘_)
∃.witness (Monoid.identity-existence monoid) = id
Identityₗ.proof (Identity.left  (∃.proof (Monoid.identity-existence monoid))) = Morphism.identityₗ(_∘_)(id)
Identityᵣ.proof (Identity.right (∃.proof (Monoid.identity-existence monoid))) = Morphism.identityᵣ(_∘_)(id)
