module Data where

open import Type

------------------------------------------
-- Tuple

module Tuple where
  infixl 200 _⨯_ _,_

  data _⨯_ {n} (X : TypeN n) (Y : TypeN n) : TypeN n where
    _,_ : X → Y → (X ⨯ Y)

  curry : ∀{n}{T₁ T₂ T₃ : TypeN n} → ((T₁ ⨯ T₂) → T₃) → (T₁ → T₂ → T₃)
  curry f x₁ x₂ = f(x₁ , x₂)

  uncurry : ∀{n}{T₁ T₂ T₃ : TypeN n} → (T₁ → T₂ → T₃) → ((T₁ ⨯ T₂) → T₃)
  uncurry f (x₁ , x₂) = f x₁ x₂

  swap : ∀{n}{T₁ T₂ : TypeN n} → (T₁ ⨯ T₂) → (T₂ ⨯ T₁)
  swap(x , y) = (y , x)

  left : ∀{n}{T₁ T₂ : TypeN n} → (T₁ ⨯ T₂) → T₁
  left(x , _) = x

  right : ∀{n}{T₁ T₂ : TypeN n} → (T₁ ⨯ T₂) → T₂
  right(_ , y) = y

  ◅ = left
  ▻ = right

  module Raise where
    open import Numeral.Natural

    _^_ : ∀{n} → (TypeN n) → ℕ → (TypeN n)
    _^_ type 0      = Unit
    _^_ type (𝐒(0)) = type
    _^_ type (𝐒(n)) = (type ^ n) ⨯ type
  open Raise using (_^_) public
open Tuple using (_⨯_ ; _,_) public

------------------------------------------
-- Either

module Either where
  infixl 100 _‖_

  data _‖_ {n} (T₁ : TypeN n) (T₂ : TypeN n) : TypeN n where
    Left : T₁ → (T₁ ‖ T₂)
    Right : T₂ → (T₁ ‖ T₂)

  swap : ∀{n}{T₁ T₂ : TypeN n} → (T₁ ‖ T₂) → (T₂ ‖ T₁)
  swap (Left t) = Right t
  swap (Right t) = Left t

  map : ∀{n}{A₁ A₂ B₁ B₂ : TypeN n} → (A₁ → A₂) → (B₁ → B₂) → (A₁ ‖ B₁) → (A₂ ‖ B₂)
  map fa _ (Left  a) = Left (fa(a))
  map _ fb (Right b) = Right(fb(b))
open Either using (_‖_) public

------------------------------------------
-- Option

module Option where
  Option : ∀{n} → (TypeN n) → (TypeN n)
  Option T = (Unit ‖ T)

  pattern Some x = Either.Right x
  pattern None   = Either.Left  unit

  map : ∀{n}{T₁ T₂ : TypeN n} → (T₁ → T₂) → (Option T₁) → (Option T₂)
  map f (Some x) = Some(f(x))
  map f (None  ) = None

  _or_ : ∀{n}{T : TypeN n} → (Option T) → T → T
  _or_ (Some x) _   = x
  _or_ None default = default

  _nor_ : ∀{n}{T : TypeN n} → (Option T) → (Option T) → (Option T)
  _nor_ (Some x) _  = (Some x)
  _nor_ None option = option

  _andThen_ : ∀{n}{T : TypeN n} → (Option T) → (T → (Option T)) → (Option T)
  _andThen_ None _ = None
  _andThen_ (Some x) optF = optF x
open Option using (Option) public
