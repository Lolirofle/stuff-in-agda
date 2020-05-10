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

-- Applies a function to the inner value of the option container.
-- A functor map for options.
map : (T₁ → T₂) → Option(T₁) → Option(T₂)
map = Either.map2 \{<> → <>}

-- Either the value inside the option container or the default value when it is none.
-- The option eliminator.
_or_ : Option(T) → T → T
_or_ (Some x) _   = x
_or_ None     def = def

-- If the option have a value (is Some).
isSome : Option(T) → Bool
isSome = Either.isRight

-- If the option have no value (is None).
isNone : Option(T) → Bool
isNone = Either.isLeft

-- Passes the inner value of the option to an option-valued function.
-- A monadic bind for options.
_andThen_ : Option(T₁) → (T₁ → Option(T₂)) → Option(T₂)
_andThen_ None     _ = None
_andThen_ (Some x) f = f(x)

-- Combines options of different types by applying the specified binary operator when both options have a value, and none otherwise.
and-combine : (T₁ → T₂ → T₃) → (Option(T₁) → Option(T₂) → Option(T₃))
and-combine (_▫_) (Some x) (Some y)  = Some(x ▫ y)
{-# CATCHALL #-}
and-combine _ _ _ = None

-- Combines options of different types by applying the specified binary operator when both options have a value, and the side functions when only the respective sides have a value. None otherwise.
or-combine : (T₁ → T₂ → T₃) → (T₁ → T₃) → (T₂ → T₃) → (Option(T₁) → Option(T₂) → Option(T₃))
or-combine(_▫_) l r None     None     = None
or-combine(_▫_) l r None     (Some y) = Some(r(y))
or-combine(_▫_) l r (Some x) None     = Some(l(x))
or-combine(_▫_) l r (Some x) (Some y) = Some(x ▫ y)

module Same where
  _orₗ_ : Option(T) → Option(T) → Option(T)
  _orₗ_ = or-combine(\x y → x) (\x → x) (\x → x)

  _orᵣ_ : Option(T) → Option(T) → Option(T)
  _orᵣ_ = or-combine(\x y → y) (\x → x) (\x → x)

  _andₗ_ : Option(T) → Option(T) → Option(T)
  _andₗ_ = and-combine(\x y → x)

  _andᵣ_ : Option(T) → Option(T) → Option(T)
  _andᵣ_ = and-combine(\x y → y)

module Different where
  _orₗ_ : Option(T₁) → Option(T₂) → Option(T₁ ‖ T₂)
  _orₗ_ = or-combine(\x y → Either.Left(x)) Either.Left Either.Right

  _orᵣ_ : Option(T₁) → Option(T₂) → Option(T₁ ‖ T₂)
  _orᵣ_ = or-combine(\x y → Either.Right(y)) Either.Left Either.Right

  _and_ : Option(T₁) → Option(T₂) → Option(T₁ ⨯ T₂)
  _and_ = and-combine(_,_)
