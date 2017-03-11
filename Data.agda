module Data where

open import Type

------------------------------------------
-- Tuple

module Tuple where
  infixl 200 _⨯_ _,_

  data _⨯_ {n} (X : TypeN n) (Y : TypeN n) : TypeN n where
    _,_ : X → Y → (X ⨯ Y)

  curry : ∀ {n} → {T₁ T₂ T₃ : TypeN n} → ((T₁ ⨯ T₂) → T₃) → (T₁ → T₂ → T₃)
  curry f x₁ x₂ = f(x₁ , x₂)

  uncurry : ∀ {n} → {T₁ T₂ T₃ : TypeN n} → (T₁ → T₂ → T₃) → ((T₁ ⨯ T₂) → T₃)
  uncurry f (x₁ , x₂) = f x₁ x₂

  swap : ∀ {n} → {T₁ T₂ : TypeN n} → (T₁ ⨯ T₂) → (T₂ ⨯ T₁)
  swap(x , y) = (y , x)

  left : ∀ {n} → {T₁ T₂ : TypeN n} → (T₁ ⨯ T₂) → T₁
  left(x , _) = x

  right : ∀ {n} → {T₁ T₂ : TypeN n} → (T₁ ⨯ T₂) → T₂
  right(_ , y) = y

  ◅ = left
  ▻ = right

open Tuple  using (_⨯_ ; _,_) public

------------------------------------------
-- Either

module Either where
  infixl 100 _‖_

  data _‖_ {n} (T₁ : TypeN n) (T₂ : TypeN n) : TypeN n where
    Left : T₁ → (T₁ ‖ T₂)
    Right : T₂ → (T₁ ‖ T₂)

  swap : ∀ {n} → {T₁ T₂ : TypeN n} → (T₁ ‖ T₂) → (T₂ ‖ T₁)
  swap (Left t) = Right t
  swap (Right t) = Left t

  map : ∀ {n} → {A₁ A₂ B₁ B₂ : TypeN n} → (A₁ → A₂) → (B₁ → B₂) → (A₁ ‖ B₁) → (A₂ ‖ B₂)
  map fa _ (Left  a) = Left (fa(a))
  map _ fb (Right b) = Right(fb(b))

open Either using (_‖_) public

------------------------------------------
-- Option

module Option where
  Option : ∀ {n} → (TypeN n) → (TypeN n)
  Option T = (Unit ‖ T)

  pattern Some x = Either.Right x
  pattern None   = Either.Left  unit

  map : ∀ {n} → {T₁ T₂ : TypeN n} → (T₁ → T₂) → (Option T₁) → (Option T₂)
  map f (Some x) = Some(f(x))
  map f (None  ) = None

open Option using (Option) public
