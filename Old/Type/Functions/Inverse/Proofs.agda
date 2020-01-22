import      Lvl
open import Type

module Type.Functions.Inverse.Proofs {ℓₗ : Lvl.Level}{ℓₒ₁}{ℓₒ₂} {X : Type{ℓₒ₁}} {Y : Type{ℓₒ₂}} where

open import Function.Domains
open import Relator.Equals
open import Type.Functions {ℓₗ}
open import Type.Functions.Inverse {ℓₗ}
open import Type.Empty
open import Type.Unit {ℓₒ₁}{ℓₒ₂}

postulate inv-bijective : ∀{f : X → Y} → ⦃ proof : Bijective(f) ⦄ → Bijective(inv f)
-- inv-bijective {f} ⦃ Bijective.intro(proof) ⦄

private
  _≡₁_ = _≡_ {ℓₗ Lvl.⊔ ℓₒ₁}

invᵣ-is-inverseᵣ : (f : X → Y) → ⦃ _ : Surjective(f) ⦄ → ∀{y} → (f(invᵣ f(y)) ≡ y)
invᵣ-is-inverseᵣ f ⦃ Surjective.intro(proof) ⦄ {y} with proof{y}
... | ◊.intro ⦃ Unapply.intro _ ⦃ out ⦄ ⦄ = out



inv-is-inverseᵣ : (f : X → Y) → ⦃ _ : Bijective(f) ⦄ → ∀{y} → (f(inv f(y)) ≡ y)
inv-is-inverseᵣ f ⦃ Bijective.intro(proof) ⦄ {y} with proof{y}
... | IsUnit.intro (Unapply.intro _ ⦃ out ⦄) _ = out

inv-is-inverseₗ : (f : X → Y) → ⦃ _ : Bijective(f) ⦄ → ∀{x} → (inv f(f(x)) ≡₁ x)
inv-is-inverseₗ f ⦃ Bijective.intro(proof) ⦄ {x} with proof{f(x)}
... | IsUnit.intro _ uniqueness with uniqueness {Unapply.intro x ⦃ [≡]-intro ⦄}
...   | [≡]-intro = [≡]-intro
