module Function.Category.Proofs where

open import Data
open import Function
open import Function.Equiv
open import Function.Equiv.Proofs
import      Lvl
open import Structure.Categorical.Properties
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₘ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable A B C : Type{ℓ}

module _
  {equiv-type : ∀{T : Type{ℓₒ}} → Equiv{ℓₑ₁}(T)}
  {equiv-func : ∀{A B : Type{ℓₒ}} → Equiv{ℓₑ₂}(A → B)}
  ⦃ ext : ∀{A B : Type{ℓₒ}} → Extensionality{A = A}{B = B} equiv-type equiv-func ⦄
  where

  Empty-initialObject : Object.Initial{Obj = Type{ℓₒ}}(_→ᶠ_) ⦃ equiv-func ⦄ (Empty)
  Empty-initialObject = Empty-domain-unit ⦃ equiv-func ⦄ ⦃ equiv-type ⦄

module _ {equiv-func : ∀{A B : Type{ℓₒ}} → Equiv{ℓₑ₂}(A → B)} where
  Unit-terminalObject : Object.Terminal{Obj = Type{ℓₒ}}(_→ᶠ_) ⦃ equiv-func ⦄ (Unit)
  Unit-terminalObject = Unit-codomain-unit ⦃ equiv-func ⦄
