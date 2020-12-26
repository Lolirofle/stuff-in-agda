module Structure.Operator.Ring.Rings where

import      Lvl
open import Structure.Operator.Ring
open import Structure.Setoid
open import Type
open import Type.Properties.Singleton

private variable ℓ ℓₑ : Lvl.Level
private variable T U : Type{ℓ}

postulate trivialRing : ∀{_+_ _⋅_ : U → U → U} → ⦃ equiv : Equiv{ℓₑ}(U) ⦄ ⦃ singleton : IsUnit(U) ⦄ → Ring(_+_)(_⋅_)
{-Ring.[+]-commutative-group  trivialRing = {!!}
Ring.[⋅]-binary-operator    trivialRing = {!!}
Ring.[⋅]-associativity      trivialRing = {!!}
Ring.[⋅][+]-distributivityₗ trivialRing = {!!}
Ring.[⋅][+]-distributivityᵣ trivialRing = {!!}
-}
