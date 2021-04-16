{-# OPTIONS --cubical #-}

module Type.Cubical.Path.Category{ℓ} where

open import Data.Tuple as Tuple using (_,_)
open import Data
open import Functional
open import Function.Axioms
open import Logic.Propositional
open import Structure.Category
open import Structure.Categorical.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Type
open import Type.Cubical.Path
open import Type.Cubical.Path.Equality
open import Type.Properties.Singleton

-- The type category is a category containing all types of a single universe level in the language.
-- The objects are all sets/types.
-- The morphisms are all functions where the domain/codomain-pair are from these objects.
typeFunctionPathCategory : Category{Obj = Type{ℓ}}(_→ᶠ_)
Category._∘_ typeFunctionPathCategory = _∘_
Category.id  typeFunctionPathCategory = id
Morphism.Associativity.proof (Category.associativity typeFunctionPathCategory)      = reflexivity(Path)
Morphism.Identityₗ.proof (Tuple.left (Category.identity typeFunctionPathCategory))  = reflexivity(Path)
Morphism.Identityᵣ.proof (Tuple.right (Category.identity typeFunctionPathCategory)) = reflexivity(Path)

typeFunctionPathCategoryObject : CategoryObject
typeFunctionPathCategoryObject = intro typeFunctionPathCategory

Empty-initialObject : Object.Initial{Obj = Type{ℓ}}(_→ᶠ_) (Empty)
IsUnit.unit       Empty-initialObject       = empty
IsUnit.uniqueness (Empty-initialObject {T}) = functionExtensionality(Empty)(T) \{}

Unit-terminalObject : Object.Terminal{Obj = Type{ℓ}}(_→ᶠ_) (Unit)
IsUnit.unit       Unit-terminalObject = const <>
IsUnit.uniqueness Unit-terminalObject = reflexivity(Path)
