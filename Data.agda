module Data where

import      Lvl
open import Type

-- The empty type which cannot be constructed
data Empty {ℓ} : Type{ℓ} where

-- Empty function
empty : ∀{ℓ₁ ℓ₂}{T : Type{ℓ₁}} → Empty{ℓ₂} → T
empty ()

-- The unit type which can only be constructed in one way
record Unit {ℓ} : Type{ℓ} where
  constructor <>
open Unit public

{-# BUILTIN UNIT Unit #-}
{-# FOREIGN GHC type AgdaUnit ℓ = () #-}
{-# COMPILE GHC Unit = data AgdaUnit (()) #-}

------------------------------------------
-- Tuple

module Tuple where
  infixl 200 _⨯_ _,_ -- TODO: Raiseᵣ gives the opposite: infixr

  -- Definition of a 2-tuple
  record _⨯_ {ℓ₁}{ℓ₂} (X : Type{ℓ₁}) (Y : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
    instance constructor _,_
    field
      left  : X
      right : Y
  open _⨯_ public

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

  module Raiseₗ where
    open import Numeral.Natural
    open import Numeral.Natural.Oper using (_−₀_)

    -- A tuple with the same type of elements a specified number of times
    _^_ : ∀{ℓ} → Type{ℓ} → ℕ → Type{ℓ}
    _^_ type 0      = Unit
    _^_ type (𝐒(0)) = type
    _^_ type (𝐒(n)) = (type ^ n) ⨯ type

    -- Returns the nth element of a tuple
    index : ∀{n : ℕ}{ℓ}{T : Type{ℓ}} → ℕ → (T ^ (𝐒(n))) → T
    index {n}{_}{T} i tuple = index'{n}(n −₀ i)(tuple) where
      index' : ∀{n : ℕ} → ℕ → (T ^ (𝐒(n))) → T
      index' {𝟎}          _ x     = x
      index' {𝐒(_)} 𝟎      (_ , last) = last
      index' {𝐒(n)} (𝐒(i)) (rest , _) = index'{n}(i)(rest)

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

    -- TODO: Transpose
    -- (((1,2),3),((4,5),6),((7,8),9))
    -- (((1,2),3),((4,7),(8,5),(6,9)))
    -- (((1,(4,7)),(2,(8,5)),(3,(6,9))))

  module Raiseᵣ where
    open import Numeral.Natural

    _^_ : ∀{ℓ} → Type{ℓ} → ℕ → Type{ℓ}
    _^_ type 0      = Unit
    _^_ type 1      = type
    _^_ type (𝐒(n)) = type ⨯ (type ^ n)

    map : ∀{n : ℕ}{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ → T₂) → (T₁ ^ n) → (T₂ ^ n)
    map {0}       f _ = <>
    map {1}       f single        = f(single)
    map {𝐒(𝐒(n))} f (init , rest) = (f(init) , map{𝐒(n)}(f)(rest))

    combine : ∀{n : ℕ}{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ ^ n) → (T₂ ^ n) → ((T₁ ⨯ T₂) ^ n)
    combine {0}       <>        <>        = <>
    combine {1}       a         b         = (a , b)
    combine {𝐒(𝐒(n))} (ah , at) (bh , bt) = ((ah , bh) , combine {𝐒(n)} (at) (bt))

    -- Returns a element repeated a specified number of times in a tuple
    repeat : ∀{ℓ}{T : Type{ℓ}} → (n : _) → T → (T ^ n)
    repeat(0)       _ = <>
    repeat(1)       x = x
    repeat(𝐒(𝐒(n))) x = (x , repeat(𝐒(n)) x)

    -- Returns a multivariate function from a singlevariate function
    lift : ∀{ℓ₁ ℓ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}} → (n : _) → (A → B) → ((A ^ n) → (B ^ n))
    lift(0)       f(_)  = <>
    lift(1)       f(x)  = f(x)
    lift(𝐒(𝐒(n))) f(first , rest) = (f(first) , lift(𝐒(n)) f(rest))

    module _ {ℓ} {T : Type{ℓ}} where
      head : ∀{n : ℕ} → (T ^ (𝐒(n))) → T
      head {𝟎}    x       = x
      head {𝐒(_)} (x , _) = x

      tail : ∀{n : ℕ} → (T ^ (𝐒(n))) → (T ^ n)
      tail {𝟎}    _       = <>
      tail {𝐒(_)} (_ , x) = x

      singleton : ∀{n : ℕ} → T → (T ^ 1)
      singleton(x) = x

      index : ∀{n : ℕ} → ℕ → (T ^ (𝐒(n))) → T
      index {𝟎}    _      x          = x
      index {𝐒(_)} 𝟎      (init , _) = init
      index {𝐒(n)} (𝐒(i)) (_ , rest) = index{n}(i)(rest)

      transpose : ∀{m n : ℕ} → ((T ^ m) ^ n) → ((T ^ n) ^ m)
      transpose {0}       {_}       _       = <>
      transpose {𝐒(𝐒(n))} {0}       <>      = (<> , transpose {𝐒(n)}{0} <>)
      transpose {1}       {_}       x       = x
      transpose {_}       {1}       x       = x
      transpose {𝐒(𝐒(m))} {𝐒(𝐒(n))} (h , t) = combine{𝐒(𝐒(m))} h (transpose {𝐒(𝐒(m))} {𝐒(n)} t)
        -- transpose ((1,(2,3)),((4,(5,6)),(7,(8,9))))
        -- combine (1,(2,3)) (transpose((4,(5,6)),(7,(8,9))))
        -- combine (1,(2,3)) (combine(4,(5,6)) (transpose(7,(8,9))))
        -- combine (1,(2,3)) (combine(4,(5,6)) (combine 7 (8,9)))
        -- combine (1,(2,3)) (combine(4,(5,6)) (7,(8,9)))
        -- combine (1,(2,3)) ((4,7),((5,8),(6,9)))
        -- ((1,(4,7)),((2,(5,8)),(3,(6,9))))

        -- ((1,(2,3)),(4,(5,6)),(7,(8,9)))
        -- (((1,4),(2,5),(3,6)),(7,(8,9)))
        -- (((1,(4,7)),(2,(5,8)),(3,(6,9))))

  module Raise where
    open Raiseₗ public
  open Raise using (_^_) public

open Tuple using (_⨯_ ; _,_) public

------------------------------------------
-- Either

module Either where
  infixl 100 _‖_

  data _‖_ {ℓ₁}{ℓ₂} (T₁ : Type{ℓ₁}) (T₂ : Type{ℓ₂}) : Type{ℓ₁ Lvl.⊔ ℓ₂} where
    instance
      Left : T₁ → (T₁ ‖ T₂)
      Right : T₂ → (T₁ ‖ T₂)
  {-# FOREIGN GHC type AgdaEither ℓ₁ ℓ₂ = Either #-}
  {-# COMPILE GHC _‖_ = data AgdaEither (Left | Right) #-}

  instance
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
