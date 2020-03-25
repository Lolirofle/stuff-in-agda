module Data.Option where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Type

private variable ℓ : Lvl.Level
private variable T T₁ T₂ : Type{ℓ}

Option : Type{ℓ} → Type{ℓ}
Option {ℓ} T = (Unit{ℓ} ‖ T)

pattern Some x = Either.Right x
pattern None   = Either.Left  <>

map : (T₁ → T₂) → Option(T₁) → Option(T₂)
map f (Some x) = Some(f(x))
map f (None  ) = None

_or_ : Option(T) → T → T
_or_ (Some x) _   = x
_or_ None     def = def

isSome : Option(T) → Bool
isSome = Either.isRight

isNone : Option(T) → Bool
isNone = Either.isLeft

module Same where
  _orₗ_ : Option(T) → Option(T) → Option(T)
  _orₗ_ (Some x) (Some y)  = Some(x)
  _orₗ_ (Some x) None      = Some(x)
  _orₗ_ None     (Some y)  = Some(y)
  _orₗ_ None     None      = None

  _orᵣ_ : Option(T) → Option(T) → Option(T)
  _orᵣ_ (Some x) (Some y)  = Some(y)
  _orᵣ_ (Some x) None      = Some(x)
  _orᵣ_ None     (Some y)  = Some(y)
  _orᵣ_ None     None      = None

  _andThen_ : Option(T) → (T → Option(T)) → Option(T)
  _andThen_ None _ = None
  _andThen_ (Some x) optF = optF x

module Different where
  _orₗ_ : Option(T₁) → Option(T₂) → Option(T₁ ‖ T₂)
  _orₗ_ (Some x) (Some y)  = Some(Either.Left(x))
  _orₗ_ (Some x) None      = Some(Either.Left(x))
  _orₗ_ None     (Some y)  = Some(Either.Right(y))
  _orₗ_ None     None      = None

  _orᵣ_ : Option(T₁) → Option(T₂) → Option(T₁ ‖ T₂)
  _orᵣ_ (Some x) (Some y)  = Some(Either.Right(y))
  _orᵣ_ (Some x) None      = Some(Either.Left(x))
  _orᵣ_ None     (Some y)  = Some(Either.Right(y))
  _orᵣ_ None     None      = None

  _and_ : Option(T) → Option(T) → Option(T ⨯ T)
  _and_ (Some x) (Some y)  = Some(x , y)
  {-# CATCHALL #-}
  _and_ _        _         = None
