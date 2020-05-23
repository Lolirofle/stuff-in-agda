module Type.Category.ExtensionalFunctionsCategory{ℓ} where

open import Data
open import Functional
open import Function.Equals
open import Function.Equals.Proofs
open import Logic.Propositional
import      Relator.Equals as Eq
open import Relator.Equals.Proofs.Equiv
open import Structure.Category
open import Structure.Category.Properties
open import Type
open import Type.Unit

-- The set category but the equality on the morphisms/functions is pointwise/extensional.
typeExtensionalFnCategory : Category{Obj = Type{ℓ}}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄
Category._∘_ typeExtensionalFnCategory = _∘_
Category.id  typeExtensionalFnCategory = id
Category.binaryOperator typeExtensionalFnCategory = [⊜][∘]-binaryOperator
Morphism.Associativity.proof (Category.associativity typeExtensionalFnCategory) {x = _} {_} {_} {x = f} {g} {h} = [⊜]-associativity {x = f}{y = g}{z = h}
Category.identity typeExtensionalFnCategory = [∧]-intro (Morphism.intro (Dependent.intro Eq.[≡]-intro)) (Morphism.intro (Dependent.intro Eq.[≡]-intro))

typeExtensionalFnCategoryObject : CategoryObject
typeExtensionalFnCategoryObject = intro typeExtensionalFnCategory

Empty-initialObject : Object.Initial{Obj = Type{ℓ}}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (Empty)
IsUnit.unit Empty-initialObject = empty
_⊜_.proof (IsUnit.uniqueness Empty-initialObject {f}) {}

Unit-terminalObject : Object.Terminal{Obj = Type{ℓ}}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (Unit)
IsUnit.unit Unit-terminalObject = const <>
_⊜_.proof (IsUnit.uniqueness Unit-terminalObject {f}) {_} = Eq.[≡]-intro
