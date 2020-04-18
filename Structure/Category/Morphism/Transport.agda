import      Lvl
open import Structure.Category
open import Structure.Setoid
open import Type

module Structure.Category.Morphism.Transport
  {ℓₒ ℓₘ : Lvl.Level}
  {Obj : Type{ℓₒ}}
  {Morphism : Obj → Obj → Type{ℓₘ}}
  ⦃ morphism-equiv : ∀{x y : Obj} → Equiv(Morphism x y) ⦄
  (cat : Category(Morphism) ⦃ morphism-equiv ⦄)
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
import      Structure.Category.Names as Names
open import Structure.Category.Properties
open import Structure.Function
open import Structure.Relator.Properties

open Names.ArrowNotation(Morphism)
open Category(cat)
open Morphism.OperModule ⦃ morphism-equiv ⦄ (\{x} → _∘_ {x})
open Morphism.IdModule   ⦃ morphism-equiv ⦄ (\{x} → _∘_ {x})(id)

module _ {P : Obj → Obj} (p : ∀{x} → (x ⟶ P(x))) ⦃ isomorphism : ∀{x} → Isomorphism(p{x}) ⦄ where
  private variable a b c : Obj

  transport : (a ≡ₑ b) → (P(a) ⟶ P(b))
  transport ab = p ∘ IdTransport.transport(cat) ab ∘ inv(p)
