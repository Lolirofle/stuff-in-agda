module Data.Tuple.Equiv where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Structure.Function
open import Structure.Operator
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B : Type{ℓ}

record Extensionality ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄ ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄ (equiv : Equiv{ℓₑ}(A ⨯ B)) : Type{Lvl.of(A) Lvl.⊔ Lvl.of(B) Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓₑ} where
  constructor intro
  private instance _ = equiv
  field
     ⦃ [,]-function ⦄   : BinaryOperator(_,_)
     ⦃ left-function ⦄  : Function(Tuple.left)
     ⦃ right-function ⦄ : Function(Tuple.right)
