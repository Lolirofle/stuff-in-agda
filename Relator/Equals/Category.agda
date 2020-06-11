module Relator.Equals.Category where

import      Data.Tuple as Tuple
open import Functional
open import Logic.Predicate
import      Lvl
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Category.Functor
open import Structure.Category.NaturalTransformation
open import Structure.Category.Properties
open import Structure.Category
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Transitivity
open import Type.Category.IntensionalFunctionsCategory
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable f g : A → B
private variable P : T → Type{ℓ}
private variable x y z : T
private variable p : x ≡ y

-- The inhabitants of a type together with the equality relation using the identity type forms a category.
-- An object is an inhabitant of an arbitrary type, and a morphism is a proof of equality between two objects.
identityTypeCategory : Category{Obj = T} (_≡_)
Category._∘_ identityTypeCategory = swap(transitivity(_≡_))
Category.id  identityTypeCategory = reflexivity(_≡_)
Morphism.Associativity.proof (Category.associativity identityTypeCategory) {x = x} {.x} {.x} {x = [≡]-intro} {[≡]-intro} {[≡]-intro} = [≡]-intro
Morphism.Identityₗ.proof (Tuple.left  (Category.identity identityTypeCategory)) {f = [≡]-intro} = [≡]-intro
Morphism.Identityᵣ.proof (Tuple.right (Category.identity identityTypeCategory)) {f = [≡]-intro} = [≡]-intro

identityTypeCategoryObject : Type{ℓ} → CategoryObject
identityTypeCategoryObject(T) = intro {Object = T} identityTypeCategory

-- An isomorphism is a proof of symmetry for two inhabitants in the identity type category, and equality is always symmetric, so all morphisms are isomorphisms.
identityTypeIsomorphism : Morphism.Isomorphism{Obj = T}{Morphism = _≡_}(Category._∘_ (identityTypeCategory))(Category.id identityTypeCategory) p
∃.witness (identityTypeIsomorphism {p = p}) = symmetry(_≡_) p
Morphism.Inverseₗ.proof (Tuple.left  (∃.proof (identityTypeIsomorphism {p = [≡]-intro}))) = [≡]-intro
Morphism.Inverseᵣ.proof (Tuple.right (∃.proof (identityTypeIsomorphism {p = [≡]-intro}))) = [≡]-intro

-- Endofunctors are functions in the identity type category, and all functions are functions respecting equality (congruence).
functionEndofunctor : Endofunctor(identityTypeCategory) f
Functor.map (functionEndofunctor{f = f}) = congruence₁(f)
Functor.op-preserving functionEndofunctor {x} {.x} {.x} {[≡]-intro} {[≡]-intro} = [≡]-intro
Functor.id-preserving functionEndofunctor = [≡]-intro

-- A functor to the category of types is a predicate, and all of them are mapped by substitution.
predicateFunctor : Functor(identityTypeCategory)(typeIntensionalFnCategory) P
Functor.map (predicateFunctor{P = P}) = substitute₁(P)
Functor.op-preserving predicateFunctor {x} {.x} {.x} {[≡]-intro} {[≡]-intro} = [≡]-intro
Functor.id-preserving predicateFunctor = [≡]-intro

-- Natural transformations between functions are proofs of extensional function equalities.
extensionalFnNaturalTransformation : ∀{p} → NaturalTransformation([∃]-intro f ⦃ functionEndofunctor ⦄) ([∃]-intro g ⦃ functionEndofunctor ⦄) p
NaturalTransformation.natural (extensionalFnNaturalTransformation {f = f} {g} {H}) {x} {.x} {[≡]-intro} =
  congruence₁(f) [≡]-intro 🝖 H(x) 🝖-[ Morphism.Identityᵣ.proof (Tuple.right  (Category.identity identityTypeCategory)) ]
  H(x)                            🝖-[ Morphism.Identityₗ.proof (Tuple.left  (Category.identity identityTypeCategory)) ]-sym
  H(x) 🝖 congruence₁(g) [≡]-intro 🝖-end
