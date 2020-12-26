module Structure.Category.Equiv where

import      Lvl
open import Structure.Setoid
open import Structure.Category

-- TODO: https://en.wikipedia.org/wiki/Equivalence_of_categories

module _ {ℓₒ ℓₘ : Lvl.Level} {Obj : Type{ℓₒ}} (Morphism : Obj → Obj → Type{ℓₘ}) ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄ where
  Category-equiv : Equiv(Category(Morphism))
  Category-equiv 
