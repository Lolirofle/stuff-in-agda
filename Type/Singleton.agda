import      Lvl
open import Type

module Type.Singleton {ℓ : Lvl.Level} {X : Type{ℓ}} where

open import Functional
open import Functional.Domains

-- A type with only a single object
Singleton : X → Type{ℓ}
Singleton(x) = Unapply(id) (x)
