module Type.Category.FakeExtensionalFunctionsCategory{ℓ} where

open import Function.Equals
open import Function.Equals.Proofs
open import Structure.Category
open import Type.Identity.Proofs

-- The type category is a category containing all types of a single universe level in the language.
-- The objects are all sets/types.
-- The morphisms are all functions where the domain/codomain-pair are from these objects.
-- Equality of morphisms are determined by the function equality which uses the identity type underneath.
-- This definition is closer to capturing the structure of the type category, but it will not be enough for a closed category (I think).
open import Type.Category{ℓ} ⦃ [⊜]-equiv ⦃ Id-equiv ⦄ ⦄ ⦃ [⊜][∘]-binaryOperator ⦃ _ ⦄ ⦃ _ ⦄ ⦃ function = Id-to-function ⦃ _ ⦄ ⦄ ⦄ public
  renaming (typeFnCategory to typeFakeExtensionalFnCategory ; Typeᶜᵃᵗ to FakeExtensionalTypeᶜᵃᵗ)
