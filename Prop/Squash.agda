{-# OPTIONS --prop #-}
module Prop.Squash where

open import Prop
open import Type

data Squash {ℓ} (T : Type{ℓ}) : Prop{ℓ} where
  intro : T → Squash(T)

elim : ∀{ℓ₁ ℓ₂} (T : Type{ℓ₁}) (P : Prop{ℓ₂}) → (T → P) → (Squash(T) → P)
elim _ _ f (intro x) = f x
