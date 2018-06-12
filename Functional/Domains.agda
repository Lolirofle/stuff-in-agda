module Functional.Domains where

import      Lvl
open import Functional
open import Logic.Predicate
open import Relator.Equals
open import Type

-- The partial domain of a function
-- Note: This is the same as the domain because all functions are total (or at least supposed to be)
⊷_ : ∀{ℓ₁ ℓ₂} {A : Type{ℓ₁}}{B : Type{ℓ₂}} → (A → B) → Type{ℓ₁}
⊷_ {_}{_} {A}{_} _ = A

-- The image/range of a function (TODO: This is defined somewhere else too. And some theorems are proven there. Move it here)
data ⊶_ {ℓₗ ℓ₁ ℓ₂} {X : Type{ℓ₁}} {Y : Type{ℓ₂}} (f : X → Y) : Type{ℓₗ Lvl.⊔ ℓ₁ Lvl.⊔ ℓ₂} where
  [⊶]-intro : (y : Y) → .⦃ _ : ∃{ℓₗ}(x ↦ f(x) ≡ y) ⦄ → (⊶ f)
