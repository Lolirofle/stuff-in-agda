module Data.Option.Quantifiers where

import      Lvl
open import Data
open import Data.Option
import      Data.Option.Functions as Option
import      Functional
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

∀ₒₚₜ : Option(T) → (T → Type{ℓ}) → Type
∀ₒₚₜ = Functional.swap(Option.partialMap Unit)

∃ₒₚₜ : Option(T) → (T → Type{ℓ}) → Type
∃ₒₚₜ = Functional.swap(Option.partialMap Empty)
