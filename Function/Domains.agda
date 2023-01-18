module Function.Domains where

open import Functional
open import Logic.Predicate
import      Lvl
open import Structure.Setoid
open import Syntax.Function
open import Type

private variable ℓₒ₁ ℓₒ₂ ℓₑ₁ ℓₑ₂ : Lvl.Level

module _ {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where
  -- The partial domain of a function
  -- Note: This is the same as the domain because all functions are total (or at least supposed to be)
  ⊷ : (X → Y) → Type
  ⊷ _ = X

module _ {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} ⦃ equiv-Y : Equiv{ℓₑ₂}(Y) ⦄ where
  -- The set of objects satisfying (Fiber f(y)) is the objects mapped to y in the mapping f (the fiber of the element y under the map f).
  -- Fiber(f) is similar to the inverse image or the preimage of f when their argument is a singleton set.
  Fiber : (X → Y) → Y → X → Type
  Fiber f(y) x = (f(x) ≡ y)

  -- The set of objects satisfying (Image f) is the objects that the mapping f point to (the image of the map f).
  Image : (X → Y) → Y → Type
  Image f = ∃ ∘ (Fiber f)
