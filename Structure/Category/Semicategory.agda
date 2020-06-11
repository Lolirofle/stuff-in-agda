module Structure.Category.Semicategory where

import      Lvl
open import Data
open import Functional using (const ; swap)
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Structure.Setoid.Uniqueness
open import Structure.Setoid
import      Structure.Category.Names as Names
open import Structure.Category.Properties
import      Structure.Operator.Names as Names
import      Structure.Operator.Properties as Properties
open import Structure.Operator
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Properties.Singleton

-- Obj is the collection of objects.
-- _⟶_ is the collection of morphisms.
module _ {ℓₒ ℓₘ : Lvl.Level} {Obj : Type{ℓₒ}} (Morphism : Obj → Obj → Type{ℓₘ}) where
  record Semicategory ⦃ morphism-equiv : ∀{x y} → Equiv(Morphism x y) ⦄ : Stmt{ℓₒ Lvl.⊔ ℓₘ} where
    open Names.ArrowNotation(Morphism)

    field
      _∘_ : Names.SwappedTransitivity(_⟶_)

    field
      ⦃ binaryOperator ⦄ : ∀{x y z} → BinaryOperator(_∘_ {x}{y}{z})
      ⦃ associativity ⦄ : Morphism.Associativity(\{x} → _∘_ {x})
