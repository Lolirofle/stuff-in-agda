import      Lvl
open import Type

module Type.Functions.Inverse {ℓₗ : Lvl.Level}{ℓₒ₁}{ℓₒ₂} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where

open import Function.Domains
open import Type.Functions {ℓₗ}{ℓₒ₁}{ℓₒ₂} {X}{Y}
open import Type.Properties.Empty
open import Type.Properties.Singleton {ℓₒ₁}{ℓₒ₂}

inv : (f : X → Y) → ⦃ _ : Bijective(f) ⦄ → (Y → X)
inv f ⦃ Bijective.intro(proof) ⦄ (y) with proof{y}
... | IsUnit.intro (Unapply.intro x) _ = x

invᵣ : (f : X → Y) → ⦃ _ : Surjective(f) ⦄ → (Y → X)
invᵣ f ⦃ Surjective.intro(proof) ⦄ (y) with proof{y}
... | ◊.intro ⦃ Unapply.intro x ⦄ = x
