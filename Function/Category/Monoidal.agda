open import Functional
open import Structure.Operator
open import Structure.Setoid
open import Type

module Function.Category.Monoidal
  {ℓₒ ℓₑ}
  ⦃ equiv-func : ∀{A B : Type{ℓₒ}} → Equiv{ℓₑ}(A → B) ⦄
  ⦃ [∘]-func : ∀{A B C : Type{ℓₒ}} → BinaryOperator(_∘_ {X = A}{Y = B}{Z = C}) ⦄
  where

{-
open import Data
open import Function.Category
open import Function.Proofs
open import Logic.Propositional
import      Lvl
open import Structure.Categorical.Properties
open import Structure.Category
open import Structure.Category.Monoidal

private variable ℓ ℓₘ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B C : Type{ℓ}

functionMonoidalCategory : MonoidalCategory
-}
