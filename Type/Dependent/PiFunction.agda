module Type.Dependent.PiFunction where

import      Lvl
open import Type

Π : ∀{ℓ₁ ℓ₂} → (A : Type{ℓ₁}) → (B : A → Type{ℓ₂}) → Type
Π A B = (a : A) → B(a)
