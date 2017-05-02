module Data where

import      Level as Lvl
open import Type

------------------------------------------
-- Tuple

module Tuple where
  infixl 200 _⨯_ _,_

  data _⨯_ {lvl₁}{lvl₂} (X : Type{lvl₁}) (Y : Type{lvl₂}) : Type{lvl₁ Lvl.⊔ lvl₂} where
    _,_ : X → Y → (X ⨯ Y)

  module _ {lvl₁ lvl₂ lvl₃} {T₁ : Type{lvl₁}} {T₂ : Type{lvl₂}} {T₃ : Type{lvl₃}} where
    curry : ((T₁ ⨯ T₂) → T₃) → (T₁ → T₂ → T₃)
    curry f x₁ x₂ = f(x₁ , x₂)

    uncurry : (T₁ → T₂ → T₃) → ((T₁ ⨯ T₂) → T₃)
    uncurry f (x₁ , x₂) = f x₁ x₂

  module _ {lvl₁ lvl₂} {T₁ : Type{lvl₁}} {T₂ : Type{lvl₂}} where
    swap : (T₁ ⨯ T₂) → (T₂ ⨯ T₁)
    swap(x , y) = (y , x)

    left : (T₁ ⨯ T₂) → T₁ -- TODO: Can this be made to a pattern?
    left(x , _) = x

    right : (T₁ ⨯ T₂) → T₂
    right(_ , y) = y

    ◅ = left
    ▻ = right

  module Raiseₗ where
    open import Numeral.Natural
    open import Numeral.Natural.Oper using (_−₀_)

    _^_ : ∀{lvl} → Type{lvl} → ℕ → Type{lvl}
    _^_ type 0      = Unit
    _^_ type (𝐒(0)) = type
    _^_ type (𝐒(n)) = (type ^ n) ⨯ type

    nth : ∀{n : ℕ}{lvl}{T : Type{lvl}} → ℕ → (T ^ (𝐒(n))) → T
    nth {n}{_}{T} i tuple = nth'{n}(n −₀ i)(tuple) where
      nth' : ∀{n : ℕ} → ℕ → (T ^ (𝐒(n))) → T
      nth' {𝟎}          _ x     = x
      nth' {𝐒(_)} 𝟎      (_ , last) = last
      nth' {𝐒(n)} (𝐒(i)) (rest , _) = nth'{n}(i)(rest)

    map : ∀{n : ℕ}{lvl₁ lvl₂}{T₁ : Type{lvl₁}}{T₂ : Type{lvl₂}} → (T₁ → T₂) → (T₁ ^ n) → (T₂ ^ n)
    map {𝟎}       f _ = unit
    map {𝐒(𝟎)}    f single        = f(single)
    map {𝐒(𝐒(n))} f (rest , last) = (map{𝐒(n)}(f)(rest) , f(last))

  module Raiseᵣ where
    open import Numeral.Natural

    _^_ : ∀{lvl} → Type{lvl} → ℕ → Type{lvl}
    _^_ type 0      = Unit
    _^_ type (𝐒(0)) = type
    _^_ type (𝐒(n)) = type ⨯ (type ^ n)

    nth : ∀{n : ℕ}{lvl}{T : Type{lvl}} → ℕ → (T ^ (𝐒(n))) → T
    nth {𝟎}    _      x          = x
    nth {𝐒(_)} 𝟎      (init , _) = init
    nth {𝐒(n)} (𝐒(i)) (_ , rest) = nth{n}(i)(rest)

    map : ∀{n : ℕ}{lvl₁ lvl₂}{T₁ : Type{lvl₁}}{T₂ : Type{lvl₂}} → (T₁ → T₂) → (T₁ ^ n) → (T₂ ^ n)
    map {𝟎}       f _ = unit
    map {𝐒(𝟎)}    f single        = f(single)
    map {𝐒(𝐒(n))} f (init , rest) = (f(init) , map{𝐒(n)}(f)(rest))

  module Raise where
    open Raiseₗ public
  open Raise using (_^_) public

open Tuple using (_⨯_ ; _,_) public

------------------------------------------
-- Either

module Either where
  infixl 100 _‖_

  data _‖_ {lvl₁}{lvl₂} (T₁ : Type{lvl₁}) (T₂ : Type{lvl₂}) : Type{lvl₁ Lvl.⊔ lvl₂} where
    Left : T₁ → (T₁ ‖ T₂)
    Right : T₂ → (T₁ ‖ T₂)

  swap : ∀{lvl₁ lvl₂}{T₁ : Type{lvl₁}}{T₂ : Type{lvl₂}} → (T₁ ‖ T₂) → (T₂ ‖ T₁)
  swap (Left t) = Right t
  swap (Right t) = Left t

  map : ∀{lvl₁ lvl₂ lvl₃ lvl₄}{A₁ : Type{lvl₁}}{A₂ : Type{lvl₂}}{B₁ : Type{lvl₃}}{B₂ : Type{lvl₄}} → (A₁ → A₂) → (B₁ → B₂) → (A₁ ‖ B₁) → (A₂ ‖ B₂)
  map fa _ (Left  a) = Left (fa(a))
  map _ fb (Right b) = Right(fb(b))
open Either using (_‖_) public

------------------------------------------
-- Option

module Option where
  Option : ∀{lvl} → Type{lvl} → Type{lvl}
  Option {lvl} T = (Unit{lvl} ‖ T)

  pattern Some x = Either.Right x
  pattern None   = Either.Left  unit

  map : ∀{lvl₁ lvl₂}{T₁ : Type{lvl₁}}{T₂ : Type{lvl₂}} → (T₁ → T₂) → Option(T₁) → Option(T₂)
  map f (Some x) = Some(f(x))
  map f (None  ) = None

  _or_ : ∀{lvl}{T : Type{lvl}} → Option(T) → T → T
  _or_ (Some x) _   = x
  _or_ None default = default

  _nor_ : ∀{lvl}{T : Type{lvl}} → Option(T) → Option(T) → Option(T)
  _nor_ (Some x) _  = (Some x)
  _nor_ None option = option

  _andThen_ : ∀{lvl}{T : Type{lvl}} → Option(T) → (T → Option(T)) → Option(T)
  _andThen_ None _ = None
  _andThen_ (Some x) optF = optF x
open Option using (Option) public
