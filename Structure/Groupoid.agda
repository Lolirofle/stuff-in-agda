import      Lvl

module Structure.Groupoid {ℓₒ ℓₘ ℓₑ : Lvl.Level} where

open import Functional using (swap)
open import Logic
open import Logic.Predicate
open import Logic.Propositional
import      Structure.Categorical.Names as Names
open import Structure.Categorical.Properties
open import Structure.Category{ℓₒ}{ℓₘ}{ℓₑ}
open import Structure.Operator
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Setoid.WithLvl
open import Type

{- TODO: It would be nice if groupoids were defined using a category as a record field and if categories were defined using a semicategory as a record field (they are "substructures" of each other) so that no code-duplication is necessary, but the problem is how long the projections/copatterns become with this approach.
postulate A B C : Type{Lvl.𝟎}

record R : Type{Lvl.𝟎} where
  field
    a : A
    b : B

record R2 : Type{Lvl.𝟎} where
  field
    r : R
    c : C
  open R(r) public
  -- a = R.a r

-- This is not possible, but would be nice:
r2 : R2
R2.a r2 = ?
R2.b r2 = ?
R2.c r2 = ?

-- One must write this:
r2 : R2
R2.r(R.a r2) = ?
R2.r(R.b r2) = ?
R2.c r2 = ?

which means that the copatterns would be longer and longer for each nesting a record has.
If Agda had support for "copattern/projection synonyms" or if the example above worked, then 
-}

-- Obj is the collection of objects.
-- _⟶_ is the collection of morphisms.
module _
  {Obj : Type{ℓₒ}}
  (_⟶_ : Obj → Obj → Type{ℓₘ})
  ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(x ⟶ y) ⦄
  where

  -- A groupoid is a structure on a relation called a morphism.
  --
  -- It can be seen as a generalization of the structure in invertible functions between a collection of types/sets.
  -- More specifically, the algebraic properties of functions regarding composition and the identity function together with an function inverter.
  -- In this case, sets are objects and functions are morphisms.
  --
  -- It can also be seen as a generalized algebraic structure, or more specifically a generalization of groups.
  -- The type of a group's operator is usually restricted to a single type, but a groupoid allows it to vary (depending on the rules of morphism instead).
  -- (One can loosely call a groupoid to be a group without the "closed" property of algebraic structures).
  -- In this case, the binary operation is (_∘_) and the laws are the usual identity, associative and inverse laws.
  --
  -- An alternative interpretation of the definition:
  -- A type (Obj) and a binary relation (Morphism) on this type is a groupoid when:
  -- • The relator is transitive.
  -- • The relator is reflexive.
  -- • The relator is symmetric.
  -- • The reflexivity proof inside the transitivity proof does not result in a new proof.
  -- • Chains of the transitivity proofs can be applied in any order and the resulting proof will be the same.
  -- • Transitivity of a proof of a pair and its symmetry is the reflexivity proof.
  -- In other words, this is a specialized equivalence relation/setoid on `Obj`. If the morphism equivalence is trivial (always true) for a groupoid, then the groupoid describes the same structure as an equivalence relation does.
  -- See `Relator.Equals.Category` for an example of this kind of binary relation.
  --
  -- A groupoid is the common pattern seen in all the examples above.
  record Groupoid : Stmt{ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ} where
    field
      _∘_ : Names.SwappedTransitivity(_⟶_)
      id  : Names.Reflexivity(_⟶_)
      inv : Names.Symmetry(_⟶_)
    infixr 20 _∘_

    field
      ⦃ binaryOperator ⦄ : ∀{x y z} → BinaryOperator(_∘_ {x}{y}{z})
      ⦃ associativity ⦄ : Morphism.Associativity(\{x} → _∘_ {x})
      ⦃ identity ⦄ : Morphism.Identity(_∘_)(\{x} → id{x})
      ⦃ inverter ⦄ : Polymorphism.Inverter(_∘_)(\{x} → id{x})(inv)

    -- This can be interpreted as proof of symmetry when `Morphism` is interpreted as a binary relation.
    morphism-symmetry : Symmetry(_⟶_)
    morphism-symmetry = intro inv

    category : Category(_⟶_)
    Category._∘_            category = _∘_
    Category.id             category = id
    Category.binaryOperator category = binaryOperator
    Category.associativity  category = associativity
    Category.identity       category = identity

    open Category(category) hiding (_∘_ ; id ; binaryOperator ; associativity ; identity) public
    open Polymorphism.Inverter(_∘_)(\{x} → id{x})(inv)(inverter) renaming (left to inverterₗ ; right to inverterᵣ) public

    morphism-equivalence : Equivalence(_⟶_)
    Equivalence.reflexivity  morphism-equivalence = morphism-reflexivity
    Equivalence.symmetry     morphism-equivalence = morphism-symmetry
    Equivalence.transitivity morphism-equivalence = morphism-transitivity

    object-equiv : Equiv(Obj)
    object-equiv = intro(_⟶_) ⦃ morphism-equivalence ⦄

    morphism-setoid : Setoid
    morphism-setoid = [∃]-intro Obj ⦃ object-equiv ⦄

-- A category object can be used when one refers to a category as an object.
-- Examples of usage are in functors (morphism between categories) or in equivalences of categories.
record GroupoidObject : Stmt{Lvl.𝐒(ℓₒ Lvl.⊔ ℓₘ Lvl.⊔ ℓₑ)} where
  constructor intro
  field
    {Object}           : Type{ℓₒ}
    {Morphism}         : Object → Object → Type{ℓₘ}
    ⦃ morphism-equiv ⦄ : ∀{x y} → Equiv{ℓₑ}(Morphism x y)
    groupoid           : Groupoid(Morphism)

  open Groupoid(groupoid) public
  instance
    groupoid-instance = groupoid
