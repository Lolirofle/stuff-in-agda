import      Lvl
open import Type

module Type.Functions {ℓₗ : Lvl.Level}{ℓₒ₁}{ℓₒ₂} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where

open import Functional.Domains
open import Type.Empty
open import Type.Unit

record Bijective (f : X → Y) : Type{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂} where
  constructor intro
  field
    proof : ∀{y} → IsUnit{ℓₗ Lvl.⊔ ℓₒ₁} (Unmap {ℓₗ}{X = X}{Y = Y} f(y))

record Injective (f : X → Y) : Type{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂} where
  constructor intro
  field
    proof : ∀{y} → IsProp{ℓₗ Lvl.⊔ ℓₒ₁} (Unmap {ℓₗ}{X = X}{Y = Y} f(y))

record Surjective (f : X → Y) : Type{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂} where
  constructor intro
  field
    proof : ∀{y} → ◊(Unmap {ℓₗ}{X = X}{Y = Y} f(y))
