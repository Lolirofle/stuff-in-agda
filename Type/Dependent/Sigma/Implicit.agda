module Type.Dependent.Sigma.Implicit where

import      Lvl
open import Type.Dependent.Sigma as Sigma hiding (intro)
open import Type

ℰ : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}} → (B : A → Type{ℓ₂}) → Type
ℰ B = Σ _ B
module ℰ {ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : A → Type{ℓ₂}} = Σ{ℓ₁}{ℓ₂}{A}{B}
pattern intro {a} b = Sigma.intro a b
