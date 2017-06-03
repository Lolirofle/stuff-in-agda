module Data where

import      Level as Lvl
open import Type

-- The empty type which cannot be constructed
data Empty {ℓ} : Type{ℓ} where

-- Empty function
empty-fn : ∀{ℓ}{T : Type{ℓ}} → Empty{ℓ} → T
empty-fn ()

-- The unit type which can only be constructed in one way
record Unit {ℓ} : Type{ℓ} where
  constructor <>
open Unit public

{-# BUILTIN UNIT Unit #-}
{-# COMPILED_DATA Unit () () #-}

------------------------------------------
-- Tuple

module Tuple where
  infixl 200 _⨯_ _,_ -- TODO: Raiseᵣ gives the opposite: infixr

  -- Definition of a 2-tuple
  data _⨯_ {ℓ₁}{ℓ₂} (X : Type{ℓ₁}) (Y : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
    _,_ : X → Y → (X ⨯ Y)

  module _ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} {T₃ : Type{ℓ₃}} where
    -- Curries a function taking a 2-tuple, transforming it to a function returning a function instead
    curry : ((T₁ ⨯ T₂) → T₃) → (T₁ → T₂ → T₃)
    curry f x₁ x₂ = f(x₁ , x₂)

    -- Uncurries a function taking a function, transforming it to a function taking a 2-tuple instead
    uncurry : (T₁ → T₂ → T₃) → ((T₁ ⨯ T₂) → T₃)
    uncurry f (x₁ , x₂) = f x₁ x₂

  module _ {ℓ₁ ℓ₂} {T₁ : Type{ℓ₁}} {T₂ : Type{ℓ₂}} where
    -- Swaps the left and right elements of a 2-tuple
    swap : (T₁ ⨯ T₂) → (T₂ ⨯ T₁)
    swap(x , y) = (y , x)

    -- Returns the left element of a 2-tuple
    left : (T₁ ⨯ T₂) → T₁ -- TODO: Can this be made to a pattern?
    left(x , _) = x

    -- Returns the right element of a 2-tuple
    right : (T₁ ⨯ T₂) → T₂
    right(_ , y) = y

    ◅ = left
    ▻ = right

  module Raiseₗ where
    open import Numeral.Natural
    open import Numeral.Natural.Oper using (_−₀_)

    -- A tuple with the same type of elements a specified number of times
    _^_ : ∀{ℓ} → Type{ℓ} → ℕ → Type{ℓ}
    _^_ type 0      = Unit
    _^_ type (𝐒(0)) = type
    _^_ type (𝐒(n)) = (type ^ n) ⨯ type

    -- Returns the nth element of a tuple
    nth : ∀{n : ℕ}{ℓ}{T : Type{ℓ}} → ℕ → (T ^ (𝐒(n))) → T
    nth {n}{_}{T} i tuple = nth'{n}(n −₀ i)(tuple) where
      nth' : ∀{n : ℕ} → ℕ → (T ^ (𝐒(n))) → T
      nth' {𝟎}          _ x     = x
      nth' {𝐒(_)} 𝟎      (_ , last) = last
      nth' {𝐒(n)} (𝐒(i)) (rest , _) = nth'{n}(i)(rest)

    -- Applies a function for every element in a tuple
    map : ∀{n : ℕ}{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ → T₂) → (T₁ ^ n) → (T₂ ^ n)
    map {𝟎}       f _ = <>
    map {𝐒(𝟎)}    f single        = f(single)
    map {𝐒(𝐒(n))} f (rest , last) = (map{𝐒(n)}(f)(rest) , f(last))

    -- Returns a element repeated a specified number of times in a tuple
    repeat : ∀{ℓ}{T : Type{ℓ}} → (n : _) → T → (T ^ n)
    repeat(𝟎)       _ = <>
    repeat(𝐒(𝟎))    x = x
    repeat(𝐒(𝐒(n))) x = (repeat(𝐒(n)) x , x)

    -- Returns a multivariate function from a singlevariate function
    lift : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (n : _) → (A → B) → ((A ^ n) → (B ^ n))
    lift(𝟎)       f(_)  = <>
    lift(𝐒(𝟎))    f(x)  = f(x)
    lift(𝐒(𝐒(n))) f(rest , last) = (lift(𝐒(n)) f(rest) , f(last))

    -- TODO: Is this necessary?
    -- _[⨯∘⨯]_ : ∀{n : ℕ}{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → ((B ^ n) → C) → (A → B) → ((A ^ n) → C)
    -- _[⨯∘⨯]_ {n} fs g xs = fs(lift(n)(g)(xs))

  module Raiseᵣ where
    open import Numeral.Natural

    _^_ : ∀{ℓ} → Type{ℓ} → ℕ → Type{ℓ}
    _^_ type 0      = Unit
    _^_ type (𝐒(0)) = type
    _^_ type (𝐒(n)) = type ⨯ (type ^ n)

    nth : ∀{n : ℕ}{ℓ}{T : Type{ℓ}} → ℕ → (T ^ (𝐒(n))) → T
    nth {𝟎}    _      x          = x
    nth {𝐒(_)} 𝟎      (init , _) = init
    nth {𝐒(n)} (𝐒(i)) (_ , rest) = nth{n}(i)(rest)

    map : ∀{n : ℕ}{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ → T₂) → (T₁ ^ n) → (T₂ ^ n)
    map {𝟎}       f _ = <>
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

  data _‖_ {ℓ₁}{ℓ₂} (T₁ : Type{ℓ₁}) (T₂ : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
    Left : T₁ → (T₁ ‖ T₂)
    Right : T₂ → (T₁ ‖ T₂)

  swap : ∀{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ ‖ T₂) → (T₂ ‖ T₁)
  swap (Left t) = Right t
  swap (Right t) = Left t

  map : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄}{A₁ : Type{ℓ₁}}{A₂ : Type{ℓ₂}}{B₁ : Type{ℓ₃}}{B₂ : Type{ℓ₄}} → (A₁ → A₂) → (B₁ → B₂) → (A₁ ‖ B₁) → (A₂ ‖ B₂)
  map fa _ (Left  a) = Left (fa(a))
  map _ fb (Right b) = Right(fb(b))
open Either using (_‖_) public

------------------------------------------
-- Option

module Option where
  Option : ∀{ℓ} → Type{ℓ} → Type{ℓ}
  Option {ℓ} T = (Unit{ℓ} ‖ T)

  pattern Some x = Either.Right x
  pattern None   = Either.Left  <>

  map : ∀{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ → T₂) → Option(T₁) → Option(T₂)
  map f (Some x) = Some(f(x))
  map f (None  ) = None

  _or_ : ∀{ℓ}{T : Type{ℓ}} → Option(T) → T → T
  _or_ (Some x) _   = x
  _or_ None default = default

  _nor_ : ∀{ℓ}{T : Type{ℓ}} → Option(T) → Option(T) → Option(T)
  _nor_ (Some x) _  = (Some x)
  _nor_ None option = option

  _andThen_ : ∀{ℓ}{T : Type{ℓ}} → Option(T) → (T → Option(T)) → Option(T)
  _andThen_ None _ = None
  _andThen_ (Some x) optF = optF x
open Option using (Option) public
