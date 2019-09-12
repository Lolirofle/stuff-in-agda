module Data.Option where

import      Lvl
open import Data
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Type

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
  {-# CATCHALL #-}
  _and_ _        _         = None
