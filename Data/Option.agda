module Data.Option where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Type

private variable ℓ : Lvl.Level
private variable T T₁ T₂ T₃ : Type{ℓ}

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

_andThen_ : Option(T₁) → (T₁ → Option(T₂)) → Option(T₂)
_andThen_ None     _ = None
_andThen_ (Some x) f = f(x)

and-combine : (T₁ → T₂ → T₃) → (Option(T₁) → Option(T₂) → Option(T₃))
and-combine (_▫_) (Some x) (Some y)  = Some(x ▫ y)
{-# CATCHALL #-}
and-combine _ _ _ = None

or-combine : (T₁ → T₂ → T₃) → (T₁ → T₃) → (T₂ → T₃) → (Option(T₁) → Option(T₂) → Option(T₃))
or-combine(_▫_) l r None     None     = None
or-combine(_▫_) l r None     (Some y) = Some(r(y))
or-combine(_▫_) l r (Some x) None     = Some(l(x))
or-combine(_▫_) l r (Some x) (Some y) = Some(x ▫ y)

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

  _andₗ_ : Option(T) → Option(T) → Option(T)
  _andₗ_ (Some x) (Some y)  = Some(x)
  {-# CATCHALL #-}
  _andₗ_ _        _         = None

  _andᵣ_ : Option(T) → Option(T) → Option(T)
  _andᵣ_ (Some x) (Some y)  = Some(y)
  {-# CATCHALL #-}
  _andᵣ_ _        _         = None

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

  _and_ : Option(T₁) → Option(T₂) → Option(T₁ ⨯ T₂)
  _and_ (Some x) (Some y)  = Some(x , y)
  {-# CATCHALL #-}
  _and_ _        _         = None
