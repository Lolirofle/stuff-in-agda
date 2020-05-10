module Data.Either where

import      Lvl
open import Data.Boolean
open import Functional using (id)
open import Type

infixl 100 _‖_

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable A B C A₁ A₂ B₁ B₂ : Type{ℓ}

data _‖_ (A : Type{ℓ₁}) (B : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  instance
    Left  : A → (A ‖ B)
    Right : B → (A ‖ B)
{-# FOREIGN GHC type AgdaEither ℓ₁ ℓ₂ = Either #-}
{-# COMPILE GHC _‖_ = data AgdaEither (Left | Right) #-}

swap : (A ‖ B) → (B ‖ A)
swap (Left t) = Right t
swap (Right t) = Left t

map1 : let _ = A ; _ = B ; _ = C in (A → C) → (B → C) → (A ‖ B) → C
map1 fa _ (Left  a) = fa(a)
map1 _ fb (Right b) = fb(b)

extract : (A ‖ A) → A
extract = map1 id id

map2 : (A₁ → A₂) → (B₁ → B₂) → (A₁ ‖ B₁) → (A₂ ‖ B₂)
map2 fa _ (Left  a) = Left (fa(a))
map2 _ fb (Right b) = Right(fb(b))

mapLeft : let _ = A ; _ = B ; _ = C in (A → C) → (A ‖ B) → (C ‖ B)
mapLeft f = map2 f id

mapRight : let _ = A ; _ = B ; _ = C in (B → C) → (A ‖ B) → (A ‖ C)
mapRight f = map2 id f

isLeft : (A ‖ B) → Bool
isLeft(Left  _) = 𝑇
isLeft(Right _) = 𝐹

isRight : (A ‖ B) → Bool
isRight(Left  _) = 𝐹
isRight(Right _) = 𝑇
