module Structure.Setoid.Category where

open import Data
import      Data.Tuple as Tuple
open import Functional
open import Function.EqualsRaw
open import Function.Proofs
open import Functional.Setoid using () renaming (id to idₛₑₜ ; _∘_ to _∘ₛₑₜ_)
open import Logic.Predicate
import      Lvl
open import Structure.Category
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Structure.Setoid.Function
open import Syntax.Transitivity
open import Type.Properties.Singleton

private variable ℓ ℓₑ ℓₒ : Lvl.Level
private variable A B C : Setoid{ℓₑ}{ℓₒ}

-- The setoid category contains setoids and functions respecting the congruence property in the setoid.
setoidCategory : Category{Obj = Setoid{ℓₑ}{ℓₒ}} ExtensionalFunction
Category._∘_ setoidCategory = _∘ₛₑₜ_
Category.id setoidCategory = idₛₑₜ
BinaryOperator.congruence (Category.binaryOperator setoidCategory) f₁f₂ g₁g₂ = f₁f₂ 🝖 congruence₁(_) g₁g₂
Morphism.Associativity.proof (Category.associativity setoidCategory) {x = _} {y = _} {z = _} {x = [∃]-intro f} {y = [∃]-intro g} {z = [∃]-intro h} = reflexivity(_≡_)
Morphism.Identityₗ.proof (Tuple.left  (Category.identity setoidCategory)) = reflexivity(_≡_)
Morphism.Identityᵣ.proof (Tuple.right (Category.identity setoidCategory)) = reflexivity(_≡_)

setoidCategoryObject : ∀{ℓₑ}{ℓₒ} → CategoryObject
setoidCategoryObject{ℓₑ}{ℓₒ} = intro(setoidCategory{ℓₑ}{ℓₒ})

module _ where
  open import Data.Proofs
  open import Relator.Equals

  Empty-initialObject : Object.Initial(ExtensionalFunction{ℓₑ}) ([∃]-intro Empty)
  IsUnit.unit Empty-initialObject = [∃]-intro empty
  IsUnit.uniqueness Empty-initialObject {_}{}

  Unit-terminalObject : Object.Terminal(ExtensionalFunction{ℓₑ}) ([∃]-intro Unit)
  IsUnit.unit Unit-terminalObject = [∃]-intro (const <>)
  IsUnit.uniqueness Unit-terminalObject = [≡]-intro
