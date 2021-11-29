module Data.Option where

import      Lvl
open import Data
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T : Type{ℓ}

data Option (T : Type{ℓ}) : Type{ℓ} where
  None : Option(T)
  Some : T → Option(T)
{-# BUILTIN MAYBE Option #-}

elim : ∀{A : Type{ℓ₁}}{B : Option(A) → Type{ℓ₂}} → B(None) → ((a : A) → B(Some a)) → ((o : Option(A)) → B(o))
elim b _  None     = b
elim b ab (Some a) = ab a
