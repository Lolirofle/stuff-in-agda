{-# OPTIONS --sized-types #-}

module Sized.Data.List where

import      Lvl
open import Lang.Size
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A A₁ A₂ B B₁ B₂ Result : Type{ℓ}
private variable s sₛ s₁ s₂ : Size

data List{ℓ} (T : Type{ℓ}) : Size → Type{ℓ} where
  ∅   : List(T) (s) -- An empty list
  _⊰_ : T → List(T) s → List(T) (𝐒ˢⁱᶻᵉ(s)) -- Cons
infixr 1000 _⊰_

tail : List(T) s → List(T) s
tail ∅       = ∅
tail (_ ⊰ l) = l

{-
-- TODO: Size problems.
_++_ : List(T) s₁ → List(T) s₂ → List(T) s₁
∅ ++ ∅ = ∅
∅ {sₛ} ++ (x ⊰ b) = x ⊰ _++_ {s₁ = sₛ} {!x ⊰ ∅!} b
(x ⊰ a) ++ b = x ⊰ (a ++ b)
-}
