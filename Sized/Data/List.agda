{-# OPTIONS --sized-types #-}

module Sized.Data.List where

import      Lvl
open import Lang.Size
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A A₁ A₂ B B₁ B₂ Result : Type{ℓ}
private variable s s₁ s₂ : Size

data List(s : Size){ℓ} (T : Type{ℓ}) : Type{ℓ} where
  ∅   : List(s)(T) -- An empty list
  _⊰_ : ∀{sₛ : <ˢⁱᶻᵉ s} → T → List(sₛ)(T) → List(s)(T) -- Cons
infixr 1000 _⊰_

tail : List(s)(T) → List(s)(T)
tail ∅       = ∅
tail (_ ⊰ l) = l

{-
-- TODO: Size problems. See notes in Lang.Size.
_++_ : List(s)(T) → List(s)(T) → List(s)(T)
_++_         ∅                   b = b
_++_ {s = s} (_⊰_ {sₛ = sₛ} x a) b = _⊰_ {s = s}{sₛ = sₛ} x (_++_ {s = sₛ} a b)
infixl 1000 _++_
-}
