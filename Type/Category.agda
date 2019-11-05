module Type.Category where

open import Data
open import Functional
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Operator.Properties
open import Type
open import Type.Unit

module _ {ℓ} where
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equivalence

  -- The set category is a category containing all sets/types of a single level in the language.
  -- The objects are all sets/types.
  -- The morphisms are all functions where the domain/codomain-pair are from these objects.
  typeIntensionalFnCategory : Category{Obj = Set(ℓ)}(_→ᶠ_)
  Category._∘_                     (typeIntensionalFnCategory) = _∘_
  Category.id                      (typeIntensionalFnCategory) = id
  Identityₗ.proof(Category.identityₗ(typeIntensionalFnCategory)) = [≡]-intro
  Identityᵣ.proof(Category.identityᵣ(typeIntensionalFnCategory)) = [≡]-intro
  Category.associativity           (typeIntensionalFnCategory) = [≡]-intro

module _ {ℓ} where
  open import Functional.Equals
  open import Functional.Equals.Proofs
  import      Relator.Equals as Eq
  open import Relator.Equals.Proofs.Equivalence

  -- The set category but the equality on the morphisms/functions is pointwise/extensional.
  typeExtensionalFnCategory : Category{Obj = Set(ℓ)}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄
  Category._∘_          (typeExtensionalFnCategory) = _∘_
  Category.id           (typeExtensionalFnCategory) = id
  Category.identityₗ     (typeExtensionalFnCategory) = [⊜]-identityₗ
  Category.identityᵣ     (typeExtensionalFnCategory) = [⊜]-identityᵣ
  Category.associativity(typeExtensionalFnCategory) {A}{B}{C}{D} {f}{g}{h} = [⊜]-associativity{ℓ}{ℓ}{ℓ}{ℓ} {A}{B}{C}{D} {f}{g}{h}

  -- Shorthand for the type of functors in the category of types.
  TypeFunctor = Endofunctor(typeExtensionalFnCategory)

  Empty-initialObject : Object.Initial{Obj = Set(ℓ)}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (Empty)
  IsUnit.unit Empty-initialObject = empty
  _⊜_.proof (IsUnit.uniqueness Empty-initialObject {f}) {}

  Unit-terminalObject : Object.Terminal{Obj = Set(ℓ)}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (Unit)
  IsUnit.unit Unit-terminalObject = const <>
  _⊜_.proof (IsUnit.uniqueness Unit-terminalObject {f}) {_} = Eq.[≡]-intro
