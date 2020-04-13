module Type.Category where

open import Data
open import Functional
open import Logic.Propositional
open import Sets.Setoid
open import Structure.Category
import      Structure.Category.Functor as Category
import      Structure.Category.Monad.ExtensionSystem as Category
open import Structure.Category.Properties
open import Structure.Operator.Properties
open import Structure.Operator
open import Type
open import Type.Unit

module _ {ℓ} where
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equivalence

  -- The set category is a category containing all sets/types of a single level in the language.
  -- The objects are all sets/types.
  -- The morphisms are all functions where the domain/codomain-pair are from these objects.
  typeIntensionalFnCategory : Category{Obj = Set(ℓ)}(_→ᶠ_)
  Category._∘_            typeIntensionalFnCategory = _∘_
  Category.id             typeIntensionalFnCategory = id
  BinaryOperator.congruence (Category.binaryOperator typeIntensionalFnCategory) [≡]-intro [≡]-intro = [≡]-intro
  Category.associativity  typeIntensionalFnCategory = Morphism.intro [≡]-intro
  Category.identity       typeIntensionalFnCategory = [∧]-intro (Morphism.intro [≡]-intro) (Morphism.intro [≡]-intro)

module _ {ℓ} where
  open import Function.Equals
  open import Function.Equals.Proofs
  import      Relator.Equals as Eq
  open import Relator.Equals.Proofs.Equivalence

  -- The set category but the equality on the morphisms/functions is pointwise/extensional.
  typeExtensionalFnCategory : Category{Obj = Set(ℓ)}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄
  Category._∘_ typeExtensionalFnCategory = _∘_
  Category.id  typeExtensionalFnCategory = id
  Category.binaryOperator typeExtensionalFnCategory = [⊜][∘]-binaryOperator
  Morphism.Associativity.proof (Category.associativity typeExtensionalFnCategory) {x = _} {_} {_} {x = f} {g} {h} = [⊜]-associativity {_}{_}{_}{_}{_}{_}{_}{_} {f}{g}{h}
  Category.identity typeExtensionalFnCategory = [∧]-intro (Morphism.intro (Dependent.intro Eq.[≡]-intro)) (Morphism.intro (Dependent.intro Eq.[≡]-intro))

  -- Shorthand for the category-related types in the category of types.
  Functor = Category.Endofunctor(typeExtensionalFnCategory)
  module Functor = Category.Endofunctor(typeExtensionalFnCategory)

  Monad = Category.ExtensionSystem{cat = typeExtensionalFnCategory}
  module Monad where
    open Category.ExtensionSystem{cat = typeExtensionalFnCategory} public
    open HaskellNames ⦃ … ⦄

    _>>=_ : ∀{T} → ⦃ _ : Monad(T) ⦄ → ∀{x y} → T(x) → (x → T(y)) → T(y)
    _>>=_ = swap bind

  Empty-initialObject : Object.Initial{Obj = Set(ℓ)}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (Empty)
  IsUnit.unit Empty-initialObject = empty
  _⊜_.proof (IsUnit.uniqueness Empty-initialObject {f}) {}

  Unit-terminalObject : Object.Terminal{Obj = Set(ℓ)}(_→ᶠ_) ⦃ [⊜]-equiv ⦃ [≡]-equiv ⦄ ⦄ (Unit)
  IsUnit.unit Unit-terminalObject = const <>
  _⊜_.proof (IsUnit.uniqueness Unit-terminalObject {f}) {_} = Eq.[≡]-intro
