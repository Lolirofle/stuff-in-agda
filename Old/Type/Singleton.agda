import      Lvl
open import Type

module Type.Singleton {ℓₗ ℓₒ : Lvl.Level} {X : Type{ℓₒ}} where

open import Functional
open import Functional.Domains

-- A type with only a single object
Singleton : X → Type{ℓₗ Lvl.⊔ ℓₒ}
Singleton(x) = Unmap{ℓₗ Lvl.⊔ ℓₒ}{ℓₒ}{ℓₒ} {X}{X} (id) (x)
