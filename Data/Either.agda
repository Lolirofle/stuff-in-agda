module Data.Either where

import      Lvl
open import Type

infixl 100 _‖_

data _‖_ {ℓ₁}{ℓ₂} (T₁ : Type{ℓ₁}) (T₂ : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  instance
    Left : T₁ → (T₁ ‖ T₂)
    Right : T₂ → (T₁ ‖ T₂)
{-# FOREIGN GHC type AgdaEither ℓ₁ ℓ₂ = Either #-}
{-# COMPILE GHC _‖_ = data AgdaEither (Left | Right) #-}

swap : ∀{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ ‖ T₂) → (T₂ ‖ T₁)
swap (Left t) = Right t
swap (Right t) = Left t

map1 : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → (A → C) → (B → C) → (A ‖ B) → C
map1 fa _ (Left  a) = fa(a)
map1 _ fb (Right b) = fb(b)

map2 : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄}{A₁ : Type{ℓ₁}}{A₂ : Type{ℓ₂}}{B₁ : Type{ℓ₃}}{B₂ : Type{ℓ₄}} → (A₁ → A₂) → (B₁ → B₂) → (A₁ ‖ B₁) → (A₂ ‖ B₂)
map2 fa _ (Left  a) = Left (fa(a))
map2 _ fb (Right b) = Right(fb(b))
