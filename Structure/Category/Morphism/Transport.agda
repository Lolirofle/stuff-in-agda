import      Lvl
open import Structure.Category
open import Structure.Setoid.WithLvl
open import Type

module Structure.Category.Morphism.Transport
  {ℓₒ ℓₘ ℓₑ : Lvl.Level}
  (cat : CategoryObject{ℓₒ}{ℓₘ}{ℓₑ})
  where

import      Functional.Dependent as Fn
import      Function.Equals
open        Function.Equals.Dependent
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Relator.Equals using ([≡]-intro) renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
import      Structure.Category.Morphism.IdTransport as IdTransport
import      Structure.Categorical.Names as Names
open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Relator.Properties

open CategoryObject(cat)
open Category(category)
open Category.ArrowNotation(category)
open Morphism.OperModule ⦃ morphism-equiv ⦄ (\{x} → _∘_ {x})
open Morphism.IdModule   ⦃ morphism-equiv ⦄ (\{x} → _∘_ {x})(id)

module _ {P : Object → Object} (p : ∀{x} → (x ⟶ P(x))) ⦃ isomorphism : ∀{x} → Isomorphism(p{x}) ⦄ where
  private variable a b c : Object

  transport : (a ≡ₑ b) → (P(a) ⟶ P(b))
  transport ab = p ∘ IdTransport.transport(cat) ab ∘ inv(p)
