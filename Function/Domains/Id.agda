module Function.Domains.Id where

import      Lvl
open import Functional using (_∘_)
open import Type
open import Type.Dependent

private variable ℓₒ₁ ℓₒ₂ ℓₑ₁ ℓₑ₂ : Lvl.Level

module _ {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where
  data Image (f : X → Y) : Y → Type{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    intro : (x : X) → Image f (f(x))

  -- The image/range of a function.
  -- Represents the "set" of values of a function.
  -- Note: An element of Y and a proof that this element is the value of the function f is included so that (⊶ f) does not become injective when f is not.
  -- Note: A construction of this implies that X is non-empty.
  ⊶ : (X → Y) → Type{ℓₒ₁ Lvl.⊔ ℓₒ₂}
  ⊶ = Σ(Y) ∘ Image

  -- Represents the "set" of objects pointing to the value y of the function f.
  -- ∃(Fiber f(y)) is also called "the fiber of the element y under the map f".
  -- Fiber(f) is similar to the inverse image or the preimage of f when their argument is a singleton set.
  data Fiber (f : X → Y) : Y → X → Type{ℓₒ₁ Lvl.⊔ ℓₒ₂} where
    intro : (x : X) → Fiber f (f(x)) x
