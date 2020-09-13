import      Lvl

module Structure.Semicategory {ℓₒ ℓₘ ℓₑ : Lvl.Level} where

open import Functional using (swap)
open import Logic
import      Structure.Categorical.Names as Names
open import Structure.Categorical.Properties
open import Structure.Operator
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Type

-- Obj is the collection of objects.
-- _⟶_ is the collection of morphisms.
module _
  {Obj : Type{ℓₒ}}
  (_⟶_ : Obj → Obj → Type{ℓₘ})
  ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(x ⟶ y) ⦄
  where

  -- A semicategory is a structure on a relation called a morphism.
  --
  -- It is similar to a category (a generalisation of it), but without the identity morphism/reflexivity.
  -- See `Structure.Category`.
  --
  -- It can also be seen as a generalized algebraic structure, or more specifically a generalization of semigroups (structure with an associative binary operator).
  -- The similarity between a semicategory and a category is like the similarity between a semigroup and a monoid.
  --
  -- An alternative interpretation of the definition:
  -- A type (Obj) and a binary relation (Morphism) on this type is a semicategory when:
  -- • The relator is transitive.
  -- • Chains of the transitivity proofs can be applied in any order and the resulting proof will be the same.
  record Semicategory : Stmt{ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
    field
      _∘_ : Names.SwappedTransitivity(_⟶_)

    field
      ⦃ binaryOperator ⦄ : ∀{x y z} → BinaryOperator(_∘_ {x}{y}{z})
      ⦃ associativity ⦄ : Morphism.Associativity(\{x} → _∘_ {x})

    -- This can be interpreted as proof of transitivity when `Morphism` is interpreted as a binary relation.
    morphism-transitivity : Transitivity(_⟶_)
    morphism-transitivity = intro(swap(_∘_))

    module ArrowNotation = Names.ArrowNotation(_⟶_)

record SemicategoryObject : Stmt{Lvl.𝐒(ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {Object}           : Type{ℓₒ}
    {Morphism}         : Object → Object → Type{ℓₘ}
    ⦃ morphism-equiv ⦄ : ∀{x y} → Equiv{ℓₑ}(Morphism x y)
    semicategory       : Semicategory(Morphism)

  open Semicategory(semicategory) public
  instance
    semicategory-instance = semicategory
