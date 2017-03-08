module Data where

open import Type

------------------------------------------
-- Tuple

infixl 2 _⨯_ _,_
data _⨯_ (X : Type) (Y : Type) : Type where
  _,_ : X → Y → (X ⨯ Y)

module Tuple where
  curry : {T₁ T₂ T₃ : Type} → ((T₁ ⨯ T₂) → T₃) → (T₁ → T₂ → T₃)
  curry f x₁ x₂ = f(x₁ , x₂)

  uncurry : {T₁ T₂ T₃ : Type} → (T₁ → T₂ → T₃) → ((T₁ ⨯ T₂) → T₃)
  uncurry f (x₁ , x₂) = f x₁ x₂

  swap : {T₁ T₂ : Type} → (T₁ ⨯ T₂) → (T₂ ⨯ T₁)
  swap(x , y) = (y , x)

  left : {T₁ T₂ : Type} → (T₁ ⨯ T₂) → T₁
  left(x , _) = x

  right : {T₁ T₂ : Type} → (T₁ ⨯ T₂) → T₂
  right(_ , y) = y

------------------------------------------
-- Either

infixl 1 _‖_
data _‖_ (T₁ : Type) (T₂ : Type) : Type where
  Left : T₁ → (T₁ ‖ T₂)
  Right : T₂ → (T₁ ‖ T₂)

module Either where
  swap : ∀ {T₁ T₂} → (T₁ ‖ T₂) → (T₂ ‖ T₁)
  swap (Left t) = Right t
  swap (Right t) = Left t

------------------------------------------
-- Option

Option : Type → Type
Option T = (Unit ‖ T)

pattern Some x = Right x

pattern None = Left unit

module Option where
  map : ∀ {T₁ T₂} → (T₁ → T₂) → (Option T₁) → (Option T₂)
  map f (Right x) = Some(f(x))
  map f (Left unit) = None
