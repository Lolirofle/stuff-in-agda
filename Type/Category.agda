open import Functional
open import Structure.Operator
open import Structure.Setoid
open import Type

module Type.Category
  {ℓₒ ℓₑ}
  ⦃ equiv-func : ∀{A B : Type{ℓₒ}} → Equiv{ℓₑ}(A → B) ⦄
  ⦃ [∘]-func : ∀{A B C : Type{ℓₒ}} → BinaryOperator(_∘_ {X = A}{Y = B}{Z = C}) ⦄
  where

-- Re-exports Function.Category because the category of functions is sometimes also called the category of types.
open import Function.Category {ℓₒ}{ℓₑ} ⦃ equiv-func ⦄ ⦃ [∘]-func ⦄ public
  renaming (functionCategory to typeFnCategory ; Functionᶜᵃᵗ to Typeᶜᵃᵗ)
