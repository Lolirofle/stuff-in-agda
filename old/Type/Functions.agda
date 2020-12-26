import      Lvl
open import Type

module Type.Functions {ℓₗ : Lvl.Level}{ℓₒ₁}{ℓₒ₂} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where

open import Function.Domains
open import Type.Properties.Empty
open import Type.Properties.Singleton

record Bijective (f : X → Y) : Type{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂} where
  constructor intro
  field
    proof : ∀{y} → IsUnit{ℓₗ Lvl.⊔ ℓₒ₁} (Unapply {ℓₗ}{X = X}{Y = Y} f(y))

record Injective (f : X → Y) : Type{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂} where
  constructor intro
  field
    proof : ∀{y} → MereProposition{ℓₗ Lvl.⊔ ℓₒ₁} (Unapply {ℓₗ}{X = X}{Y = Y} f(y))

record Surjective (f : X → Y) : Type{ℓₗ Lvl.⊔ ℓₒ₁ Lvl.⊔ ℓₒ₂} where
  constructor intro
  field
    proof : ∀{y} → ◊(Unapply {ℓₗ}{X = X}{Y = Y} f(y))
