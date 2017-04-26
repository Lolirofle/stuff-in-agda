module FnSet where

import      Level as Lvl
open import Data
open import Functional
open import Relator.Equals(Lvl.𝟎)
open import Type

record FnSet(T : Type) : Type where
  field
    inclusion-fn : T → Bool

_∈_ : ∀{T} → T → FnSet(T) → Type
_∈_ a set = ((FnSet.inclusion-fn set a) ≡ 𝑇)


_∪_ : FnSet(T) → FnSet(T) → FnSet(T)
_∪_ A B =
  record{
    inclusion-fn = (elem ↦ FnSet.inclusion-fn(A)(elem) ∨ FnSet.inclusion-fn(B)(elem))
  }
