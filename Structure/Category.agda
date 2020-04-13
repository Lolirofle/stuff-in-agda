module Structure.Category where

import      Lvl
open import Data
open import Functional using (const ; swap)
open import Lang.Instance
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Sets.Setoid.Uniqueness
open import Sets.Setoid
import      Structure.Category.Names as Names
open import Structure.Category.Properties as Properties
import      Structure.Operator.Names as Names
import      Structure.Operator.Properties as Properties
open import Structure.Operator
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Unit

-- Obj is the collection of objects.
-- _⟶_ is the collection of morphisms.
module _ {ℓₒ ℓₘ : Lvl.Level} {Obj : Type{ℓₒ}} (Morphism : Obj → Obj → Type{ℓₘ}) where
  open Names.ArrowNotation(Morphism)

  -- A category is a general algebraic structure.
  --
  -- It can be seen as a generalization of monoids where the type is not restricted to a single one (algebraic structure without the "closed" property). It is instead replaced with the concept of a "morphism".
  -- In this case, the binary operation is (_∘_). It has an identity and is associative.
  --
  -- It can also be seen as an generalization of the structure in functions between a collection of sets.
  -- More specifically, the algebraic properties of functions regarding composition and the identity function.
  -- In this case, sets are objects and functions are morphisms.
  --
  -- An alternative interpretation of the definition:
  -- A type (Obj) and a binary relation (Morphism) on this type is a category when:
  -- • The relator is transitive.
  -- • The relator is reflexive.
  -- • The reflexivity proof inside the transitivity proof result in the same proof.
  -- • Chains of the transitivity proofs can be applied in any direction and the resulting proof will be the same.
  --
  -- A similiar interpretation to the above is that a category describes a graph and its paths.
  -- Vertices are objects and morphisms are paths between the vertices.
  --
  -- When the objects are algebraic structures, the morphisms is usually homomorphisms of the respective algebraic structure.
  -- In the case of categories being the objects in a category, functors are homomorphisms, and therefore also the morphisms.
  -- TODO: https://math.stackexchange.com/questions/405459/homomorphisms-vs-functors/405479#comment867772_405459 https://ncatlab.org/nlab/show/homomorphism)
  record Category ⦃ morphism-equiv : ∀{x y} → Equiv(x ⟶ y) ⦄ : Stmt{ℓₒ Lvl.⊔ ℓₘ} where
    field
      -- Existence of morphisms constructed by connecting two morphisms (The composition of two morphisms).
      -- Existence of a binary operator on morphisms connecting the ends of two morphisms.
      -- Also a proof of transitivity for the binary relator (_⟶_).
      -- Note that this is the operator like the operators in other algebraic structures with binary operators
      -- ∀{x y z : Obj} → (y ⟶ z) → (x ⟶ y) → (x ⟶ z)
      _∘_ : Names.SwappedTransitivity(_⟶_)

      -- Existence of a morphism connected to itself (The identity morphism).
      -- Also a proof of reflexivity for the binary relator (_⟶_).
      -- ∀{x : Obj} → (x ⟶ x)
      id  : Names.Reflexivity(_⟶_)
    infixr 20 _∘_

    field
      -- The binary operator respects the equivalence relation.
      ⦃ binaryOperator ⦄ : ∀{x y z} → BinaryOperator(_∘_ {x}{y}{z})

      -- The binary operator on mophisms is associative.
      -- The order of applying two transitivies on three proofs does not matter. It is the same proof.
      -- ∀{x y z w : Obj}{f : y ⟶ x}{g : z ⟶ y}{h : w ⟶ z} → ((f ∘ g) ∘ h ≡ f ∘ (g ∘ h))
      ⦃ associativity ⦄ : Morphism.Associativity(\{x} → _∘_ {x})

      -- The morphism `id` behaves like aa identity element with respect to the binary operator.
      -- Applying the proof of reflexivity on transitivity is an identity function for proofs.
      ⦃ identity ⦄ : Morphism.Identity(_∘_)(\{x} → id{x})

    instance
      identityₗ : Morphism.Identityₗ(_∘_)(\{x} → id{x})
      identityₗ = [∧]-elimₗ identity

    instance
      identityᵣ : Morphism.Identityᵣ(_∘_)(\{x} → id{x})
      identityᵣ = [∧]-elimᵣ identity

    -- As stated in `id`, it could be interpreted as proof of reflexivity when `Morphism` is interpreted as a binary relation.
    morphism-reflexivity : Reflexivity(_⟶_)
    morphism-reflexivity = intro id

    -- As stated in `_∘_`, it could be interpreted as proof of transitivity when `Morphism` is interpreted as a binary relation.
    morphism-transitivity : Transitivity(_⟶_)
    morphism-transitivity = intro(swap _∘_)

    module ArrowNotation = Names.ArrowNotation(Morphism)
