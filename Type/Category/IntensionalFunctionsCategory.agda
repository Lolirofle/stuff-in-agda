module Type.Category.IntensionalFunctionsCategory{ℓ} where

open import Data
open import Functional
open import Logic.Propositional
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Category
open import Structure.Category.Properties
open import Structure.Operator
open import Type
open import Type.Properties.Singleton

-- The type category is a category containing all types of a single universe level in the language.
-- The objects are all sets/types.
-- The morphisms are all functions where the domain/codomain-pair are from these objects.
typeIntensionalFnCategory : Category{Obj = Type{ℓ}}(_→ᶠ_)
Category._∘_            typeIntensionalFnCategory = _∘_
Category.id             typeIntensionalFnCategory = id
BinaryOperator.congruence (Category.binaryOperator typeIntensionalFnCategory) [≡]-intro [≡]-intro = [≡]-intro
Category.associativity  typeIntensionalFnCategory = Morphism.intro [≡]-intro
Category.identity       typeIntensionalFnCategory = [∧]-intro (Morphism.intro [≡]-intro) (Morphism.intro [≡]-intro)

typeIntensionalFnCategoryObject : CategoryObject
typeIntensionalFnCategoryObject = intro typeIntensionalFnCategory

Unit-terminalObject : Object.Terminal{Obj = Type{ℓ}}(_→ᶠ_) (Unit)
IsUnit.unit       Unit-terminalObject = const <>
IsUnit.uniqueness Unit-terminalObject = [≡]-intro
