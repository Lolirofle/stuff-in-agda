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
  instance constructor <>
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

  swap : ∀{ℓ₁ ℓ₂}{T₁ : Type{ℓ₁}}{T₂ : Type{ℓ₂}} → (T₁ ‖ T₂) → (T₂ ‖ T₁)
  swap (Left t) = Right t
  swap (Right t) = Left t

  map1 : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{C : Type{ℓ₃}} → (A → C) → (B → C) → (A ‖ B) → C
  map1 fa _ (Left  a) = fa(a)
  map1 _ fb (Right b) = fb(b)

  map2 : ∀{ℓ₁ ℓ₂ ℓ₃ ℓ₄}{A₁ : Type{ℓ₁}}{A₂ : Type{ℓ₂}}{B₁ : Type{ℓ₃}}{B₂ : Type{ℓ₄}} → (A₁ → A₂) → (B₁ → B₂) → (A₁ ‖ B₁) → (A₂ ‖ B₂)
  map2 fa _ (Left  a) = Left (fa(a))
  map2 _ fb (Right b) = Right(fb(b))
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

  _default_ : ∀{ℓ}{T : Type{ℓ}} → Option(T) → T → T
  _default_ (Some x) _   = x
  _default_ None     def = def

  module Same where
    _orₗ_ : ∀{ℓ}{T : Type{ℓ}} → Option(T) → Option(T) → Option(T)
    _orₗ_ (Some x) (Some y)  = Some(x)
    _orₗ_ (Some x) None      = Some(x)
    _orₗ_ None     (Some y)  = Some(y)
    _orₗ_ None     None      = None

    _orᵣ_ : ∀{ℓ}{T : Type{ℓ}} → Option(T) → Option(T) → Option(T)
    _orᵣ_ (Some x) (Some y)  = Some(y)
    _orᵣ_ (Some x) None      = Some(x)
    _orᵣ_ None     (Some y)  = Some(y)
    _orᵣ_ None     None      = None

    _andThen_ : ∀{ℓ}{T : Type{ℓ}} → Option(T) → (T → Option(T)) → Option(T)
    _andThen_ None _ = None
    _andThen_ (Some x) optF = optF x

  module Different where
    _orₗ_ : ∀{ℓ}{T₁ T₂ : Type{ℓ}} → Option(T₁) → Option(T₂) → Option(T₁ ‖ T₂)
    _orₗ_ (Some x) (Some y)  = Some(Either.Left(x))
    _orₗ_ (Some x) None      = Some(Either.Left(x))
    _orₗ_ None     (Some y)  = Some(Either.Right(y))
    _orₗ_ None     None      = None

    _orᵣ_ : ∀{ℓ}{T₁ T₂ : Type{ℓ}} → Option(T₁) → Option(T₂) → Option(T₁ ‖ T₂)
    _orᵣ_ (Some x) (Some y)  = Some(Either.Right(y))
    _orᵣ_ (Some x) None      = Some(Either.Left(x))
    _orᵣ_ None     (Some y)  = Some(Either.Right(y))
    _orᵣ_ None     None      = None

    _and_ : ∀{ℓ}{T : Type{ℓ}} → Option(T) → Option(T) → Option(T ⨯ T)
    _and_ (Some x) (Some y)  = Some(x , y)
    _and_ _        _         = None
open Option using (Option) public
