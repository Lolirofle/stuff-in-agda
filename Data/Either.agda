module Data.Either where

import      Lvl
open import Data.Boolean using (Bool ; 𝑇 ; 𝐹)
open import Functional using (id ; _∘_ ; const)
open import Type

infixr 100 _‖_

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable A B C A₁ A₂ B₁ B₂ : Type{ℓ}

data _‖_ (A : Type{ℓ₁}) (B : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  Left  : A → (A ‖ B)
  Right : B → (A ‖ B)
{-# FOREIGN GHC type AgdaEither ℓ₁ ℓ₂ = Either #-}
{-# COMPILE GHC _‖_ = data AgdaEither (Left | Right) #-}

elim : (P : (A ‖ B) → Type{ℓ}) → ((a : A) → P(Left a)) → ((b : B) → P(Right b)) → ((e : (A ‖ B)) → P(e))
elim _ fa _ (Left  a) = fa(a)
elim _ _ fb (Right b) = fb(b)

map1 : let _ = A ; _ = B ; _ = C in (A → C) → (B → C) → (A ‖ B) → C
map1 = elim _

-- Alternative implementation:
--   swap (Left t) = Right t
--   swap (Right t) = Left t
swap : (A ‖ B) → (B ‖ A)
swap = map1 Right Left

extract : (A ‖ A) → A
extract = map1 id id

map : (A₁ → A₂) → (B₁ → B₂) → (A₁ ‖ B₁) → (A₂ ‖ B₂)
map fa fb = map1 (Left ∘ fa) (Right ∘ fb)

mapLeft : let _ = A₁ ; _ = A₂ ; _ = B in (A₁ → A₂) → (A₁ ‖ B) → (A₂ ‖ B)
mapLeft f = map f id

mapRight : let _ = A ; _ = B₁ ; _ = B₂ in (B₁ → B₂) → (A ‖ B₁) → (A ‖ B₂)
mapRight f = map id f

-- Alternative implementation:
--   isLeft = map1 (const 𝑇) (const 𝐹)
isLeft : (A ‖ B) → Bool
isLeft (Left  _) = 𝑇
isLeft (Right _) = 𝐹

-- Alternative implementation:
--   isRight = map1 (const 𝐹) (const 𝑇)
isRight : (A ‖ B) → Bool
isRight (Left  _) = 𝐹
isRight (Right _) = 𝑇

associateLeft : (A ‖ (B ‖ C)) → ((A ‖ B) ‖ C)
associateLeft (Left x)         = Left(Left x)
associateLeft (Right(Left y))  = Left(Right y)
associateLeft (Right(Right z)) = Right z

associateRight : ((A ‖ B) ‖ C) → (A ‖ (B ‖ C))
associateRight (Left(Left x))  = Left x
associateRight (Left(Right y)) = Right(Left y)
associateRight (Right z)       = Right(Right z)
