module Structure.Setoid.Category where

open import Data
import      Data.Tuple as Tuple
open import Functional
open import Function.Equals
open import Function.Equals.Proofs
open import Function.Proofs
open import Logic.Predicate
import      Lvl
open import Structure.Category
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Type
open import Type.Properties.Singleton

private variable ℓ ℓₑ ℓₒ : Lvl.Level

-- TODO: Maybe move this?
FunctionObject : Setoid{ℓₑ}{ℓₒ} → Setoid{ℓₑ}{ℓₒ} → Type
FunctionObject ([∃]-intro A) ([∃]-intro B) = ∃{Obj = (A → B)} Function

instance
  FunctionObject-equiv : ∀{A B : Setoid{ℓₑ}{ℓₒ}} → Equiv(FunctionObject A B)
  Equiv._≡_ FunctionObject-equiv = (_⊜_) on₂ [∃]-witness
  Reflexivity.proof  (Equivalence.reflexivity  (Equiv.equivalence FunctionObject-equiv)) = reflexivity(_⊜_)
  Symmetry.proof     (Equivalence.symmetry     (Equiv.equivalence FunctionObject-equiv)) = symmetry(_⊜_)
  Transitivity.proof (Equivalence.transitivity (Equiv.equivalence FunctionObject-equiv)) = transitivity(_⊜_)

-- The setoid category contains setoids and functions respecting the congruence property in the setoid.
setoidCategory : Category{Obj = Setoid{ℓₑ}{ℓₒ}} FunctionObject
Category._∘_ setoidCategory ([∃]-intro f) ([∃]-intro g) = [∃]-intro (f ∘ g) ⦃ [∘]-function {f = f}{g = g} ⦄
Category.id setoidCategory = [∃]-intro id
BinaryOperator.congruence (Category.binaryOperator setoidCategory) f₁f₂ g₁g₂ = [⊜][∘]-binaryOperator-raw f₁f₂ g₁g₂
Morphism.Associativity.proof (Category.associativity setoidCategory) {x = _} {y = _} {z = _} {x = [∃]-intro f} {y = [∃]-intro g} {z = [∃]-intro h} = [∘]-associativity {f = f} {g = g} {h = h}
Morphism.Identityₗ.proof (Tuple.left  (Category.identity setoidCategory)) = [∘]-identityₗ
Morphism.Identityᵣ.proof (Tuple.right (Category.identity setoidCategory)) = [∘]-identityᵣ

setoidCategoryObject : ∀{ℓₑ}{ℓₒ} → CategoryObject
setoidCategoryObject{ℓₑ}{ℓₒ} = intro(setoidCategory{ℓₑ}{ℓₒ})

module _ where
  open import Data.Proofs
  open import Relator.Equals

  Empty-initialObject : Object.Initial(FunctionObject{ℓₑ}) ([∃]-intro Empty)
  IsUnit.unit Empty-initialObject = [∃]-intro empty
  _⊜_.proof (IsUnit.uniqueness Empty-initialObject) {}

  Unit-terminalObject : Object.Terminal(FunctionObject{ℓₑ}) ([∃]-intro Unit)
  IsUnit.unit Unit-terminalObject = [∃]-intro (const <>)
  _⊜_.proof (IsUnit.uniqueness Unit-terminalObject) = [≡]-intro
