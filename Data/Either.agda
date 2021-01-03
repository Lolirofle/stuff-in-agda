module Data.Either where

import      Lvl
open import Data.Boolean using (Bool ; 𝑇 ; 𝐹)
open import Functional using (id ; _∘_)
open import Type

infixr 100 _‖_

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Lvl.Level
private variable A B C A₁ A₂ B₁ B₂ : Type{ℓ}

data _‖_ (A : Type{ℓ₁}) (B : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
  Left  : A → (A ‖ B)
  Right : B → (A ‖ B)
{-# FOREIGN GHC type AgdaEither ℓ₁ ℓ₂ = Either #-}
{-# COMPILE GHC _‖_ = data AgdaEither (Left | Right) #-}

elim : ∀{P : (A ‖ B) → Type{ℓ}} → ((a : A) → P(Left a)) → ((b : B) → P(Right b)) → ((e : (A ‖ B)) → P(e))
elim fa _ (Left  a) = fa(a)
elim _ fb (Right b) = fb(b)

map1 : let _ = A ; _ = B ; _ = C in (A → C) → (B → C) → (A ‖ B) → C
map1 = elim

swap : (A ‖ B) → (B ‖ A)
swap (Left t) = Right t
swap (Right t) = Left t

extract : (A ‖ A) → A
extract = map1 id id

map : (A₁ → A₂) → (B₁ → B₂) → (A₁ ‖ B₁) → (A₂ ‖ B₂)
map fa fb = map1 (Left ∘ fa) (Right ∘ fb)

mapLeft : let _ = A₁ ; _ = A₂ ; _ = B in (A₁ → A₂) → (A₁ ‖ B) → (A₂ ‖ B)
mapLeft f = map f id

mapRight : let _ = A ; _ = B₁ ; _ = B₂ in (B₁ → B₂) → (A ‖ B₁) → (A ‖ B₂)
mapRight f = map id f

isLeft : (A ‖ B) → Bool
isLeft(Left  _) = 𝑇
isLeft(Right _) = 𝐹

isRight : (A ‖ B) → Bool
isRight(Left  _) = 𝐹
isRight(Right _) = 𝑇
