module BidirectionalFunction.Equiv where

open import BidirectionalFunction
import      Functional as Fn
import      Lvl
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T A B : Type{ℓ}

instance
  [↔]-reflexivity : Reflexivity{ℓ₂ = ℓ}(_↔_)
  [↔]-reflexivity = intro id

instance
  [↔]-symmetry : Symmetry{ℓ₂ = ℓ}(_↔_)
  [↔]-symmetry = intro(rev $ᵣ_)

instance
  [↔]-transitivity : Transitivity{ℓ₂ = ℓ}(_↔_)
  [↔]-transitivity = intro(Fn.swap(_∘_))

instance
  [↔]-equivalence : Equivalence{ℓ₂ = ℓ}(_↔_)
  [↔]-equivalence = intro

instance
  [↔]-equiv : Equiv(Type{ℓ})
  [↔]-equiv = intro(_↔_) ⦃ [↔]-equivalence ⦄
