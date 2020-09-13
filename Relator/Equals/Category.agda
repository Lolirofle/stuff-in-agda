module Relator.Equals.Category where

import      Data.Tuple as Tuple
import      Functional as Fn
open import Logic.Predicate
import      Lvl
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Categorical.Properties
import      Structure.Category.Functor as Category
open import Structure.Category.NaturalTransformation
open import Structure.Category
open import Structure.Function
open import Structure.Groupoid
import      Structure.Groupoid.Functor as Groupoid
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Relator
open import Syntax.Transitivity
open import Type.Category.IntensionalFunctionsCategory
open import Type

private variable ℓ : Lvl.Level
private variable T A B Obj : Type{ℓ}
private variable f g : A → B
private variable P : T → Type{ℓ}
private variable x y z : T
private variable p : x ≡ y
private variable _⟶_ : Obj → Obj → Type{ℓ}

-- The inhabitants of a type together with the equality relation using the identity type forms a groupoid.
-- An object is an inhabitant of an arbitrary type, and a morphism is a proof of equality between two objects.
identityTypeGroupoid : Groupoid{Obj = T} (_≡_)
Groupoid._∘_ identityTypeGroupoid = Fn.swap(transitivity(_≡_))
Groupoid.id  identityTypeGroupoid = reflexivity(_≡_)
Groupoid.inv identityTypeGroupoid = symmetry(_≡_)
Morphism.Associativity.proof              (Groupoid.associativity identityTypeGroupoid) {x = _} {x = [≡]-intro} {y = [≡]-intro} {z = [≡]-intro} = [≡]-intro
Morphism.Identityₗ.proof     (Tuple.left  (Groupoid.identity      identityTypeGroupoid)) {f = [≡]-intro} = [≡]-intro
Morphism.Identityᵣ.proof     (Tuple.right (Groupoid.identity      identityTypeGroupoid)) {f = [≡]-intro} = [≡]-intro
Polymorphism.Inverterₗ.proof (Tuple.left  (Groupoid.inverter      identityTypeGroupoid)) {f = [≡]-intro} = [≡]-intro
Polymorphism.Inverterᵣ.proof (Tuple.right (Groupoid.inverter      identityTypeGroupoid)) {f = [≡]-intro} = [≡]-intro

identityTypeCategory : Category{Obj = T} (_≡_)
identityTypeCategory = Groupoid.category identityTypeGroupoid

-- TODO: Generalize and move this to Structure.Categorical.Proofs
inverse-of-identity : ∀{grp : Groupoid(_⟶_)}{x} → (Groupoid.inv grp (Groupoid.id grp {x}) ≡ Groupoid.id grp)
inverse-of-identity {grp = grp} =
  inv(id)      🝖[ _≡_ ]-[ Morphism.identityᵣ(_∘_)(id) ]-sym
  inv(id) ∘ id 🝖[ _≡_ ]-[ Morphism.inverseₗ(_∘_)(id)(id)(inv id) ]
  id           🝖[ _≡_ ]-end
  where open Structure.Groupoid.Groupoid(grp)

idTransportFunctor : ∀{grp : Groupoid(_⟶_)} → Groupoid.Functor(identityTypeGroupoid)(grp) Fn.id
Groupoid.Functor.map (idTransportFunctor{_⟶_ = _⟶_}{grp = grp}) = sub₂(_≡_)(_⟶_) where instance _ = Groupoid.morphism-reflexivity grp
Groupoid.Functor.op-preserving (idTransportFunctor{grp = grp}) {f = [≡]-intro} {g = [≡]-intro} = symmetry(_≡_) (Morphism.Identityₗ.proof (Tuple.left (Groupoid.identity grp)))
Groupoid.Functor.inv-preserving (idTransportFunctor{_⟶_ = _⟶_}{grp = grp}) {f = [≡]-intro} =
  sub₂(_≡_)(_⟶_) (symmetry(_≡_) (reflexivity(_≡_))) 🝖[ _≡_ ]-[]
  sub₂(_≡_)(_⟶_) (reflexivity(_≡_))                 🝖[ _≡_ ]-[]
  id                                                🝖[ _≡_ ]-[ inverse-of-identity{grp = grp} ]-sym
  inv(id)                                           🝖[ _≡_ ]-[]
  inv(sub₂(_≡_)(_⟶_) (reflexivity(_≡_)))            🝖-end
  where
    instance _ = Groupoid.morphism-reflexivity grp
    open Structure.Groupoid.Groupoid(grp)
Groupoid.Functor.id-preserving idTransportFunctor = [≡]-intro

-- Endofunctors are functions in the identity type category, and all functions are functions respecting equality (congruence).
functionFunctor : Groupoid.Functor(identityTypeGroupoid)(identityTypeGroupoid) f
Groupoid.Functor.map (functionFunctor {f = f}) = congruence₁(f)
Groupoid.Functor.op-preserving functionFunctor {f = [≡]-intro} {g = [≡]-intro} = [≡]-intro
Groupoid.Functor.inv-preserving functionFunctor {f = [≡]-intro} = [≡]-intro
Groupoid.Functor.id-preserving functionFunctor = [≡]-intro

-- A functor to the category of types is a predicate, and all of them are mapped by substitution.
predicateFunctor : Category.Functor(identityTypeCategory)(typeIntensionalFnCategory) P -- TODO: Is it possible to generalize so that the target (now `typeIntensionalFnCategory`) is more general? `idTransportFunctor` seems to be similar. Maybe on the on₂-category to the right?
Category.Functor.map (predicateFunctor{P = P}) = substitute₁(P)
Category.Functor.op-preserving predicateFunctor {x} {.x} {.x} {[≡]-intro} {[≡]-intro} = [≡]-intro
Category.Functor.id-preserving predicateFunctor = [≡]-intro

-- Natural transformations between functions are proofs of extensional function equalities.
extensionalFnNaturalTransformation : ∀{p} → NaturalTransformation([∃]-intro f ⦃ Groupoid.Functor.categoryFunctor functionFunctor ⦄) ([∃]-intro g ⦃ Groupoid.Functor.categoryFunctor functionFunctor ⦄) p
NaturalTransformation.natural (extensionalFnNaturalTransformation {f = f} {g} {H}) {x} {.x} {[≡]-intro} =
  congruence₁(f) [≡]-intro 🝖 H(x) 🝖-[ Morphism.Identityᵣ.proof (Tuple.right  (Category.identity identityTypeCategory)) ]
  H(x)                            🝖-[ Morphism.Identityₗ.proof (Tuple.left  (Category.identity identityTypeCategory)) ]-sym
  H(x) 🝖 congruence₁(g) [≡]-intro 🝖-end
