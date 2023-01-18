module Type.Category.IntensionalFunctionsCategory{ℓ} where

open import Structure.Category
open import Type.Identity.Proofs

-- The type category is a category containing all types of a single universe level in the language.
-- The objects are all sets/types.
-- The morphisms are all functions where the domain/codomain-pair are from these objects.
-- Equality of morphisms are determined by the identity type (categories in intentional type theory).
open import Type.Category{ℓ} ⦃ Id-equiv ⦄ ⦃ Id-to-function₂ ⦃ Id-equiv ⦄ ⦄ public
  renaming (typeFnCategory to typeIntensionalFnCategory ; Typeᶜᵃᵗ to IntensionalTypeᶜᵃᵗ)
