module Type.Dependent.Sigma.Instance where

import      Lvl
open import Type.Dependent.Sigma as Sigma hiding (intro)
open import Type

⅀ : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}} → (B : A → Type{ℓ₂}) → Type
⅀ B = Σ _ B
module ⅀ {ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : A → Type{ℓ₂}} = Σ{ℓ₁}{ℓ₂}{A}{B}

intro : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : A → Type{ℓ₂}} → (a : A) → ⦃ right : B(a) ⦄ → ⅀ B
intro a ⦃ b ⦄ = Sigma.intro a b

{-
instance
  rightInstance : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : A → Type{ℓ₂}} → ⦃ inst : ⅀ B ⦄ → B(⅀.left inst)
  rightInstance ⦃ inst ⦄ = Σ.right inst
-}

{-
import      Lvl
open import Type

record ⅀ {ℓ₁ ℓ₂} {A : Type{ℓ₁}} (B : A → Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  eta-equality
  constructor intro
  field
    left      : A
    ⦃ right ⦄ : B(left)
-}
