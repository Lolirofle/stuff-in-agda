module Relator.Equals.Category where

import      Data.Tuple as Tuple
open import Functional as Fn using (_$_)
open import Functional.Dependent using () renaming (_∘_ to _∘ᶠ_)
open import Logic.Predicate
import      Lvl
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Categorical.Properties
import      Structure.Category.Functor as Category
open import Structure.Category.Monad
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
open import Type.Identity
open import Type

private variable ℓ : Lvl.Level
private variable T A B Obj : Type{ℓ}
private variable f g : A → B
private variable P : T → Type{ℓ}
private variable x y z : T
private variable p : Id x y
private variable _⟶_ : Obj → Obj → Type{ℓ}

-- The inhabitants of a type together with the the inhabitants of the identity type forms a groupoid.
-- An object is an inhabitant of a certain type, and a morphism is a proof of identity between two objects.
identityTypeGroupoid : Groupoid{Obj = T} (Id)
Groupoid._∘_ identityTypeGroupoid = Fn.swap(transitivity(Id))
Groupoid.id  identityTypeGroupoid = reflexivity(Id)
Groupoid.inv identityTypeGroupoid = symmetry(Id)
Morphism.Associativity.proof              (Groupoid.associativity identityTypeGroupoid) {x = _} {x = intro} {y = intro} {z = intro} = intro
Morphism.Identityₗ.proof     (Tuple.left  (Groupoid.identity      identityTypeGroupoid)) {f = intro} = intro
Morphism.Identityᵣ.proof     (Tuple.right (Groupoid.identity      identityTypeGroupoid)) {f = intro} = intro
Polymorphism.Inverterₗ.proof (Tuple.left  (Groupoid.inverter      identityTypeGroupoid)) {f = intro} = intro
Polymorphism.Inverterᵣ.proof (Tuple.right (Groupoid.inverter      identityTypeGroupoid)) {f = intro} = intro

identityTypeCategory : Category{Obj = T} (Id)
identityTypeCategory = Groupoid.category identityTypeGroupoid

-- TODO: Generalize and move this to Structure.Categorical.Proofs
inverse-of-identity : ∀{grp : Groupoid(_⟶_)}{x} → (Groupoid.inv grp (Groupoid.id grp {x}) ≡ Groupoid.id grp)
inverse-of-identity {grp = grp} =
  inv(id)      🝖[ Id ]-[ Morphism.identityᵣ(_∘_)(id) ]-sym
  inv(id) ∘ id 🝖[ Id ]-[ Morphism.inverseₗ(_∘_)(id)(id)(inv id) ]
  id           🝖[ Id ]-end
  where open Structure.Groupoid.Groupoid(grp)

idTransportFunctor : ∀{grp : Groupoid(_⟶_)} → Groupoid.Functor(identityTypeGroupoid)(grp) Fn.id
Groupoid.Functor.map (idTransportFunctor{_⟶_ = _⟶_}{grp = grp}) = sub₂(Id)(_⟶_) where instance _ = Groupoid.morphism-reflexivity grp
Groupoid.Functor.op-preserving (idTransportFunctor{grp = grp}) {f = intro} {g = intro} = symmetry(Id) (Morphism.Identityₗ.proof (Tuple.left (Groupoid.identity grp)))
Groupoid.Functor.inv-preserving (idTransportFunctor{_⟶_ = _⟶_}{grp = grp}) {f = intro} =
  sub₂(Id)(_⟶_) (symmetry(Id) (reflexivity(Id))) 🝖[ Id ]-[]
  sub₂(Id)(_⟶_) (reflexivity(Id))                🝖[ Id ]-[]
  id                                             🝖[ Id ]-[ inverse-of-identity{grp = grp} ]-sym
  inv(id)                                        🝖[ Id ]-[]
  inv(sub₂(Id)(_⟶_) (reflexivity(Id)))           🝖-end
  where
    instance _ = Groupoid.morphism-reflexivity grp
    open Structure.Groupoid.Groupoid(grp)
Groupoid.Functor.id-preserving idTransportFunctor = intro

-- A functor in the identity type groupoid is a function and a proof of it being a function (compatibility with the identity relation, or in other words, respecting the congruence property).
-- Note: It does not neccessarily have to be an endofunctor because different objects (types) can be chosen for the respective groupoids.
functionFunctor : Groupoid.Functor(identityTypeGroupoid)(identityTypeGroupoid) f
Groupoid.Functor.map (functionFunctor {f = f}) = congruence₁(f)
Groupoid.Functor.op-preserving  functionFunctor {f = intro} {g = intro} = intro
Groupoid.Functor.inv-preserving functionFunctor {f = intro}             = intro
Groupoid.Functor.id-preserving  functionFunctor                         = intro

-- A functor to the category of types is a predicate and a proof of it being a relation (having the substitution property).
predicateFunctor : Category.Functor(identityTypeCategory)(typeIntensionalFnCategory) P -- TODO: Is it possible to generalize so that the target (now `typeIntensionalFnCategory`) is more general? `idTransportFunctor` seems to be similar. Maybe on the on₂-category to the right?
Category.Functor.map (predicateFunctor{P = P}) = substitute₁(P)
Category.Functor.op-preserving predicateFunctor {x} {.x} {.x} {intro} {intro} = intro
Category.Functor.id-preserving predicateFunctor = intro

-- A natural transformation in the identity type groupoid between two functions (functors of the identity type groupoid) is a proof of them being extensionally identical.
extensionalFnNaturalTransformation : (p : ∀(x) → (f(x) ≡ g(x))) → NaturalTransformation([∃]-intro f ⦃ Groupoid.Functor.categoryFunctor functionFunctor ⦄) ([∃]-intro g ⦃ Groupoid.Functor.categoryFunctor functionFunctor ⦄) p
NaturalTransformation.natural (extensionalFnNaturalTransformation {f = f} {g = g} p) {x} {.x} {intro} =
  congruence₁(f) intro 🝖 p(x) 🝖-[ Morphism.Identityᵣ.proof (Tuple.right (Category.identity identityTypeCategory)) ]
  p(x)                        🝖-[ Morphism.Identityₗ.proof (Tuple.left  (Category.identity identityTypeCategory)) ]-sym
  p(x) 🝖 congruence₁(g) intro 🝖-end

open import Function.Equals
open import Function.Proofs
open import Structure.Function.Domain
open import Structure.Function.Multi
open import Structure.Setoid using (Equiv)

-- A monad in the identity type groupoid is an identity function and a proof of it being that and it being idempotent.
-- The proof that it behaves the same extensionally as an identity function should also preserve congruence.
-- TODO: Instead of (∀{x} → (p(f(x))) ≡ congruence₁(f) (p(x))) , use something like ⦃ preserv : Preserving₁(p)(f)(congruence₁(f)) ⦄ , but it does not work at the moment. Maybe something is dependent here?
identityFunctionMonad : ∀{T : Type{ℓ}}{f : T → T} → (p : ∀(x) → (x ≡ f(x))) → (∀{x} → (p(f(x))) ≡ congruence₁(f) (p(x))) → Monad(f) ⦃ Groupoid.Functor.categoryFunctor functionFunctor ⦄
∃.witness (Monad.Η (identityFunctionMonad p _)) = p
NaturalTransformation.natural (∃.proof (Monad.Η (identityFunctionMonad {f = f} p _))) {x}{.x}{intro} =
  Fn.id intro 🝖 p(x)          🝖[ Id ]-[]
  intro 🝖 p(x)                🝖[ Id ]-[]
  p(x)                        🝖[ Id ]-[ Morphism.Identityₗ.proof (Tuple.left  (Category.identity identityTypeCategory)) ]-sym
  p(x) 🝖 intro                🝖[ Id ]-[]
  p(x) 🝖 congruence₁(f) intro 🝖-end
∃.witness (Monad.Μ (identityFunctionMonad {f = f} p _)) x = symmetry(Id) (congruence₁(f) (p(x)))
NaturalTransformation.natural (∃.proof (Monad.Μ (identityFunctionMonad {f = f} p _))) {x}{.x}{intro} =
  (congruence₁(f) Fn.∘ congruence₁(f)) intro 🝖 symmetry(Id) (congruence₁(f) (p(x)))  🝖[ Id ]-[]
  congruence₁(f) (congruence₁(f) intro) 🝖 symmetry(Id) (congruence₁(f) (p(x)))       🝖[ Id ]-[]
  congruence₁(f) intro 🝖 symmetry(Id) (congruence₁(f) (p(x)))                        🝖[ Id ]-[]
  intro 🝖 symmetry(Id) (congruence₁(f) (p(x)))                                       🝖[ Id ]-[]
  symmetry(Id) (congruence₁(f) (p(x)))                                               🝖[ Id ]-[ Morphism.Identityₗ.proof (Tuple.left  (Category.identity identityTypeCategory)) ]-sym
  symmetry(Id) (congruence₁(f) (p(x))) 🝖 intro                                       🝖[ Id ]-[]
  symmetry(Id) (congruence₁(f) (p(x))) 🝖 congruence₁(f) intro                        🝖-end
_⊜_.proof (Monad.μ-functor-[∘]-commutativity (identityFunctionMonad {f = f} p preserv)) {x} = congruence₂-₁(_🝖_)(symmetry(Id) (congruence₁(f) (p(x)))) $
  congruence₁(f) (symmetry(Id) (congruence₁(f) (p(x)))) 🝖[ Id ]-[ Groupoid.Functor.inv-preserving (functionFunctor{f = f}) {f = congruence₁(f) (p x)} ]
  symmetry(Id) (congruence₁(f) (congruence₁(f) (p(x)))) 🝖[ Id ]-[ congruence₁(symmetry(Id)) (congruence₁(congruence₁(f)) preserv) ]-sym
  symmetry(Id) (congruence₁(f) (p(f(x))))               🝖-end
_⊜_.proof (Monad.μ-functor-[∘]-identityₗ (identityFunctionMonad {f = f} p preserv)) {x} =
  congruence₁(f) (p(x)) 🝖 symmetry(Id) (congruence₁(f) (p(x))) 🝖[ Id ]-[ congruence₂(Groupoid._∘_ identityTypeGroupoid) (congruence₁(symmetry(Id)) preserv) preserv ]-sym
  p(f(x)) 🝖 symmetry(Id) (p(f(x)))                             🝖[ Id ]-[ Morphism.Inverseₗ.proof (Tuple.left(Groupoid.inverse identityTypeGroupoid {f = p(f x)})) ]
  intro{x = f(x)}                                              🝖-end
_⊜_.proof (Monad.μ-functor-[∘]-identityᵣ (identityFunctionMonad {f = f} p preserv)) {x} =
  p(f(x)) 🝖 symmetry(Id) (congruence₁(f) (p(x))) 🝖[ Id ]-[ congruence₂-₂(_🝖_)(p(f(x))) (congruence₁(symmetry(Id)) preserv) ]-sym
  p(f(x)) 🝖 symmetry(Id) (p(f(x)))               🝖[ Id ]-[ Morphism.Inverseₗ.proof (Tuple.left(Groupoid.inverse identityTypeGroupoid {f = p(f x)})) ]
  intro{x = f(x)}                                🝖-end
