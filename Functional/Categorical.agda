module Functional.Categorical where

import      Lvl
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A B C : Type{ℓ}
private variable a₁ a₂ : A
private variable b₁ b₂ : B

module _ (_▫₁_ : A → B → Type{ℓ₁}) (_▫₂_ : A → B → Type{ℓ₂}) where
  on₂ : ((a₁ ▫₂ a₂) → (b₁ ▫₂ b₂) → C) → (∀{x y} → (x ▫₁ y) → (x ▫₂ y)) → ((a₁ ▫₁ a₂) → (b₁ ▫₁ b₂) → C)
  on₂ f g x y = f (g x) (g y)
