module Functional.NonNormalizing where

import      Lvl
open import Functional
open import Relator.Equals
open import Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable P : T → Type{ℓ}
private variable _▫_ : A → B → C
private variable f : A → B
private variable x y z : T

abstract
  idₙₙ : T → T
  idₙₙ = id

  idₙₙ-def : idₙₙ x ≡ id x
  idₙₙ-def = [≡]-intro

abstract
  swapₙₙ : (A → B → C) → (B → A → C)
  swapₙₙ = swap

  swapₙₙ-def : swapₙₙ(_▫_) x y ≡ swap(_▫_) x y
  swapₙₙ-def = [≡]-intro

abstract
  _$ₙₙ_ : (A → B) → A → B
  _$ₙₙ_ = _$_
  infixr 0 _$ₙₙ_

  [$ₙₙ]-def : (f $ₙₙ x) ≡ (f $ x)
  [$ₙₙ]-def = [≡]-intro

abstract
  ∀ₙₙ : (T → Type{ℓ}) → Type{Lvl.of(T) Lvl.⊔ ℓ}
  ∀ₙₙ P = ∀{x} → P(x)

  [∀ₙₙ]-def : (∀ₙₙ P) ≡ (∀{x} → P(x))
  [∀ₙₙ]-def = [≡]-intro
