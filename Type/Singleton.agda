import      Lvl
open import Type
open import Structure.Setoid.WithLvl

module Type.Singleton {ℓ ℓₑ : Lvl.Level} {X : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(X) ⦄ where

open import Functional
open import Function.Domains
open import Logic.Predicate

-- A type with only a single object
Singleton : X → Type{ℓₑ Lvl.⊔ ℓ}
Singleton(x) = ∃(Fiber(id) (x))
