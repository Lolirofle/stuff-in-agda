{-# OPTIONS --sized-types #-}

module Sized.Data.List where

import      Lvl
open import Lang.Size
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A A₁ A₂ B B₁ B₂ Result : Type{ℓ}
private variable s : Size

-- infixl 1000 _++_
infixr 1000 _⊰_

data List {s}{ℓ} (T : Type{ℓ}) : Type{ℓ} where
  ∅   : List{s = s} (T) -- An empty list
  _⊰_ : ∀{sₛ : <ˢⁱᶻᵉ s} → T → List{s = sₛ} (T) → List{s = s} (T) -- Cons

tail : List{s}(T) → List{s}(T)
tail ∅       = ∅
tail (_ ⊰ l) = l

{-
-- TODO: Size problems. See notes in Lang.Size.
_++_ : ∀{s₁ s₂} → List{s = s₁}(T) → List{s = s₂}(T) → List{s = s₁ ⊔ˢⁱᶻᵉ s₂}(T)
_++_                    ∅                   b = b
_++_ {s₁ = s₁}{s₂ = s₂} (_⊰_ {sₛ = sₛ} x a) b = _⊰_ {s = s₁ ⊔ˢⁱᶻᵉ s₂}{sₛ = sₛ ⊔ˢⁱᶻᵉ s₂} x (_++_ {s₁ = sₛ}{s₂ = s₂} a b)
-}
