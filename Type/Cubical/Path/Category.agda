{-# OPTIONS --cubical #-}

module Type.Cubical.Path.Category{ℓ} where

open import Type.Cubical.Path.Equality

-- The type category is a category containing all types of a single universe level in the language.
-- The objects are all sets/types.
-- The morphisms are all functions where the domain/codomain-pair are from these objects.
-- Equality of morphisms are determined by the path type (categories in extentional type theory).
open import Type.Category{ℓ} ⦃ Path-equiv ⦄ ⦃ Path-congruence₂ ⦄ public
  renaming (typeFnCategory to typeFnPathCategory ; Typeᶜᵃᵗ to ExtensionalTypeᶜᵃᵗ)
