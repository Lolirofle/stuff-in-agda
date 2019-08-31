import      Lvl
open import Type

module Type.Functions.Inverse {ℓₗ : Lvl.Level}{ℓₒ₁}{ℓₒ₂} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where

open import Functional.Domains
open import Type.Functions {ℓₗ}{ℓₒ₁}{ℓₒ₂} {X}{Y}
open import Type.Empty
open import Type.Unit {ℓₒ₁}{ℓₒ₂}

inv : (f : X → Y) → ⦃ _ : Bijective(f) ⦄ → (Y → X)
inv f ⦃ Bijective.intro(proof) ⦄ (y) with proof{y}
... | IsUnit.intro (Unapply.intro x) _ = x

invᵣ : (f : X → Y) → ⦃ _ : Surjective(f) ⦄ → (Y → X)
invᵣ f ⦃ Surjective.intro(proof) ⦄ (y) with proof{y}
... | ◊.intro ⦃ Unapply.intro x ⦄ = x
