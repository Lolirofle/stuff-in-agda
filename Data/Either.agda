module Data.Either where

import      Lvl
open import Data.Boolean
open import Functional using (id)
open import Type

infixl 100 _‖_

data _‖_ {ℓ₁}{ℓ₂} (T₁ : Type{ℓ₁}) (T₂ : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  instance
    Left  : T₁ → (T₁ ‖ T₂)
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

mapLeft : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → (A → C) → (A ‖ B) → (C ‖ B)
mapLeft f = map2 f id

mapRight : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → (B → C) → (A ‖ B) → (A ‖ C)
mapRight f = map2 id f

bool : ∀{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ ‖ T₂) → Bool
bool(Left  _) = 𝐹
bool(Right _) = 𝑇
