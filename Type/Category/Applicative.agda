module Type.Category.Monad where

open import Functional
import      Lvl
import      Structure.Category.Monad.ExtensionSystem as Category
open import Structure.Operator
open import Structure.Setoid
open import Type
open import Type.Category

private variable ℓ ℓₒ ℓₘ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B C : Type{ℓ}

module _
  ⦃ equiv-func : ∀{A B : Type{ℓₒ}} → Equiv{ℓₑ}(A → B) ⦄
  ⦃ [∘]-func : ∀{A B C : Type{ℓₒ}} → BinaryOperator(_∘_ {X = A}{Y = B}{Z = C}) ⦄
  where

  Monad = Category.ExtensionSystem{C = Typeᶜᵃᵗ}
  module Monad {T} ⦃ monad : Monad(T) ⦄ where
    open Category.ExtensionSystem{C = Typeᶜᵃᵗ} (monad) public

    -- Do notation for monads.
    open import Syntax.Do
    instance
      doNotation : DoNotation(T)
      return ⦃ doNotation ⦄ = HaskellNames.return
      _>>=_  ⦃ doNotation ⦄ = swap(HaskellNames.bind)

  open Monad using () renaming (doNotation to Monad-doNotation) public
